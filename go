#!/bin/bash
# go - Ralph Wiggum agent loop for lean-zip
#
# "I'm in danger!" - runs autonomous Claude sessions in a loop with
# live monitoring, structured logging, and process tracking.
#
# Usage:
#   ./go [--help] [--force] [--single] [--sleep N] [--resume UUID] [--prompt TEXT] [--verbose]
#
# Flags:
#   --help, -h        Show this help
#   --force, -f       Skip quota check
#   --single          Run one session then exit (default: loop forever)
#   --sleep N         Sleep N seconds between sessions (default: 0)
#   --resume UUID     Resume an existing session
#   --prompt TEXT     Override default prompt (default: /start)
#   --verbose, -v     Verbose quota check output

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CLAUDE_AVAILABLE_MODEL="$HOME/.claude/skills/claude-usage/claude-available-model"
LOCKFILE="$SCRIPT_DIR/.go.lock"
LOGFILE="$SCRIPT_DIR/agent-loop.log"
JSONL_DIR="$HOME/.claude/projects/-Users-kim-projects-lean-lean-zip"

# --- Parse flags ---

FORCE=""
SINGLE=""
SLEEP_SECS=0
RESUME_UUID=""
PROMPT="/start"
VERBOSE=""

while [[ $# -gt 0 ]]; do
    case "$1" in
        --help|-h)    sed -n '2,/^[^#]/{ /^#/s/^# \{0,1\}//p; }' "$0"; exit 0 ;;
        --force|-f)   FORCE=1 ;;
        --single)     SINGLE=1 ;;
        --sleep)      SLEEP_SECS="$2"; shift ;;
        --resume)     RESUME_UUID="$2"; shift ;;
        --prompt)     PROMPT="$2"; shift ;;
        --verbose|-v) VERBOSE=1 ;;
        *) echo "Unknown flag: $1" >&2; exit 1 ;;
    esac
    shift
done

# --- Logging ---

log() {
    local msg="[$(date '+%Y-%m-%d %H:%M:%S')] $*"
    echo "$msg" >> "$LOGFILE"
}

# Print to terminal + log file
say() {
    local msg="[$(date '+%Y-%m-%d %H:%M:%S')] $*"
    echo "$msg"
    echo "$msg" >> "$LOGFILE"
}

# --- Lock file ---

if [ -f "$LOCKFILE" ]; then
    prev_pid=$(cat "$LOCKFILE")
    if kill -0 "$prev_pid" 2>/dev/null; then
        say "Previous run (PID $prev_pid) still active. Skipping."
        exit 0
    fi
    rm -f "$LOCKFILE"
fi

echo $$ > "$LOCKFILE"

# --- Cleanup / Ctrl-C handling ---

CURRENT_UUID=""
FILTER_PID=""
CLAUDE_PID=""

fmt_tokens() {
    local n=$1
    if (( n >= 1000000 )); then
        echo "$(( n / 1000000 )).$(( (n % 1000000) * 10 / 1000000 ))M"
    elif (( n >= 1000 )); then
        echo "$(( n / 1000 ))k"
    else
        echo "$n"
    fi
}

cleanup() {
    # Kill the streaming filter subshell (its EXIT trap kills tail + python3)
    if [[ -n "$FILTER_PID" ]]; then
        kill "$FILTER_PID" 2>/dev/null || true
        wait "$FILTER_PID" 2>/dev/null || true
    fi

    # Clean up state file
    [[ -n "$CURRENT_UUID" ]] && rm -f "/tmp/agent-${CURRENT_UUID}-state.json"

    # Remove lock
    rm -f "$LOCKFILE"

    # Print loop summary if we ran any sessions
    if (( SESSION_NUM > 0 )); then
        local loop_elapsed=$(( $(date +%s) - LOOP_START ))
        local tok_str=""
        if (( LOOP_TOTAL_IN > 0 || LOOP_TOTAL_OUT > 0 )); then
            local cost_dollars=$(( LOOP_COST_CENTS / 100 ))
            local cost_remainder=$(( LOOP_COST_CENTS % 100 ))
            tok_str=" tokens=$(fmt_tokens $LOOP_TOTAL_IN)/$(fmt_tokens $LOOP_TOTAL_OUT)~\$${cost_dollars}.$(printf '%02d' $cost_remainder)"
        fi
        echo ""
        say "Loop finished: ${SESSION_NUM} sessions over $(human_duration $loop_elapsed)$tok_str"
    fi

    # Print resume hint with original flags
    if [[ -n "$CURRENT_UUID" ]]; then
        local resume_cmd="./go --resume $CURRENT_UUID"
        [[ -n "$FORCE" ]] && resume_cmd="$resume_cmd --force"
        [[ -n "$SINGLE" ]] && resume_cmd="$resume_cmd --single"
        [[ "$PROMPT" != "/start" ]] && resume_cmd="$resume_cmd --prompt '$PROMPT'"
        (( SLEEP_SECS > 0 )) && resume_cmd="$resume_cmd --sleep $SLEEP_SECS"
        [[ -n "$VERBOSE" ]] && resume_cmd="$resume_cmd --verbose"
        echo "To resume: $resume_cmd"
    fi
}

trap cleanup EXIT

# --- Status line ---

# Format bytes as human-readable
human_size() {
    local bytes=$1
    if (( bytes >= 1048576 )); then
        echo "$(( bytes / 1048576 )).$(( (bytes % 1048576) * 10 / 1048576 ))MB"
    elif (( bytes >= 1024 )); then
        echo "$(( bytes / 1024 )).$(( (bytes % 1024) * 10 / 1024 ))KB"
    else
        echo "${bytes}B"
    fi
}

# Format seconds as human-readable duration
human_duration() {
    local secs=$1
    if (( secs >= 3600 )); then
        printf '%dh%02dm' $((secs/3600)) $((secs%3600/60))
    elif (( secs >= 60 )); then
        printf '%dm%02ds' $((secs/60)) $((secs%60))
    else
        printf '%ds' "$secs"
    fi
}

update_status() {
    local session_num=$1
    local pid=$2
    local uuid=$3
    local jsonl_path="$JSONL_DIR/$uuid.jsonl"
    local state_file="/tmp/agent-${uuid}-state.json"
    local now
    now=$(date +%s)

    # JSONL info
    local size_str="waiting"
    local age_str=""
    if [[ -f "$jsonl_path" ]]; then
        local size mod_time age
        size=$(stat -f%z "$jsonl_path" 2>/dev/null || echo 0)
        mod_time=$(stat -f%m "$jsonl_path" 2>/dev/null || echo "$now")
        age=$(( now - mod_time ))
        size_str=$(human_size "$size")
        age_str="+$(human_duration "$age")"
    fi

    # API connection status + thinking detection
    local api_status
    local tcp_count
    tcp_count=$(lsof -p "$pid" 2>/dev/null | grep -c 'TCP.*ESTABLISHED' || true)
    if (( tcp_count > 0 )); then
        if [[ -f "$jsonl_path" ]]; then
            local jsonl_age
            jsonl_age=$(( now - $(stat -f%m "$jsonl_path" 2>/dev/null || echo "$now") ))
            if (( jsonl_age > 10 )); then
                api_status="thinking $(human_duration $jsonl_age)"
            else
                api_status="api:live"
            fi
        else
            api_status="api:live"
        fi
    else
        api_status="api:idle"
    fi

    # Latest agent activity + token usage from streaming filter
    local last_text="" tokens_str=""
    if [[ -f "$state_file" ]]; then
        IFS=$'\t' read -r last_text tokens_str < <(python3 -c "
import json, sys
try:
    with open(sys.argv[1]) as f:
        d = json.load(f)
    text = d.get('text', '')
    ti = d.get('tokens_in', 0)
    to = d.get('tokens_out', 0)
    cr = d.get('cache_read', 0)
    cc = d.get('cache_create', 0)
    line = ''
    if text:
        line = text.strip().split('\n')[-1][:80]
    tok = ''
    total_in = ti + cr + cc
    if total_in or to:
        def fmt(n):
            if n >= 1000000: return f'{n/1000000:.1f}M'
            if n >= 1000: return f'{n/1000:.0f}k'
            return str(n)
        # Opus 4.6: \$5/M input, \$25/M output, \$0.50/M cache read, \$6.25/M cache create
        cost = ti * 5 / 1e6 + cc * 6.25 / 1e6 + cr * 0.50 / 1e6 + to * 25 / 1e6
        tok = f'{fmt(total_in)}/{fmt(to)}~\${cost:.2f}'
    print(line + '\t' + tok)
except:
    print('\t')
" "$state_file" 2>/dev/null) || true
    fi

    # Elapsed time for this session
    local elapsed=""
    if [[ -n "${SESSION_START:-}" ]]; then
        elapsed=" $(human_duration $(( now - SESSION_START )))"
    fi

    # Build status line
    local status
    status=$(printf '[%s] #%d PID:%d%s | %s%s | %s' \
        "$(date '+%H:%M:%S')" "$session_num" "$pid" "$elapsed" \
        "$size_str" "$age_str" "$api_status")
    if [[ -n "$tokens_str" ]]; then
        status="$status | tok:$tokens_str"
    fi

    if [[ -n "$last_text" ]]; then
        # Truncate to fit terminal width (leave room for status prefix)
        local prefix_len=${#status}
        local max_text=$(( ${COLUMNS:-120} - prefix_len - 6 ))
        if (( max_text > 10 )) && (( ${#last_text} > max_text )); then
            last_text="${last_text:0:$max_text}..."
        fi
        status="$status | $last_text"
    fi

    # Overwrite current line
    printf '\r\033[K%s' "$status"
}

# --- JSONL streaming filter ---

start_filter() {
    local uuid=$1
    local jsonl_path="$JSONL_DIR/$uuid.jsonl"
    local state_file="/tmp/agent-${uuid}-state.json"

    if [[ ! -f "$jsonl_path" ]]; then
        # Not ready yet — caller should retry later
        return 1
    fi

    # Run in a subshell so we can kill the entire process group (tail + python3).
    # Without this, killing python3 alone leaves tail -f orphaned since nobody
    # writes to the JSONL file to trigger SIGPIPE.
    (
        trap 'kill 0' EXIT
        tail -f "$jsonl_path" 2>/dev/null | python3 -c "
import json, sys

state_file = sys.argv[1]
last_text = ''
total_in = 0
total_out = 0
total_cache_read = 0
total_cache_create = 0

for line in sys.stdin:
    try:
        d = json.loads(line)
        ts = d.get('timestamp', '')
        typ = d.get('type', '')
        if typ == 'assistant':
            # Accumulate token usage
            usage = d.get('message', {}).get('usage', {})
            total_in += usage.get('input_tokens', 0)
            total_cache_create += usage.get('cache_creation_input_tokens', 0)
            total_cache_read += usage.get('cache_read_input_tokens', 0)
            total_out += usage.get('output_tokens', 0)
            for b in d.get('message', {}).get('content', []):
                if b.get('type') == 'text' and b.get('text', '').strip():
                    last_text = b['text'].strip()
                elif b.get('type') == 'tool_use':
                    name = b.get('name', '')
                    inp = b.get('input', {})
                    # Extract the interesting part of each tool
                    detail = ''
                    if name == 'Bash':
                        desc = inp.get('description', '')
                        cmd = inp.get('command', '')
                        if desc and cmd:
                            detail = desc + ': ' + cmd
                        else:
                            detail = desc or cmd
                    elif name == 'Edit':
                        p = inp.get('file_path', '')
                        detail = p.split('/')[-1] if p else ''
                    elif name in ('Read', 'Write'):
                        p = inp.get('file_path', '')
                        detail = p.split('/')[-1] if p else ''
                    elif name in ('Grep', 'Glob'):
                        detail = inp.get('pattern', '')
                    elif name == 'TodoWrite':
                        todos = inp.get('todos', [])
                        active = [t for t in todos if t.get('status') == 'in_progress']
                        detail = active[0].get('activeForm', '') if active else ''
                    elif name == 'Task':
                        detail = inp.get('description', '')
                    else:
                        detail = name
                    if detail:
                        last_text = '[' + name + '] ' + detail
                    else:
                        last_text = '[' + name + ']'
            with open(state_file, 'w') as f:
                json.dump({'ts': ts, 'text': last_text,
                           'tokens_in': total_in, 'tokens_out': total_out,
                           'cache_read': total_cache_read,
                           'cache_create': total_cache_create}, f)
    except:
        pass
" "$state_file"
    ) &
    FILTER_PID=$!
    return 0
}

# --- Quota check ---

check_quota() {
    if [[ -n "$FORCE" ]]; then
        return 0
    fi

    if [[ -n "$VERBOSE" ]]; then
        "$CLAUDE_AVAILABLE_MODEL" --verbose >&2 || true
    fi

    local model
    if ! model=$("$CLAUDE_AVAILABLE_MODEL" 2>/dev/null); then
        say "No Claude quota available. Try again later."
        return 1
    fi

    if [[ "$model" != "opus" ]]; then
        say "Only $model quota available. lean-zip work requires opus."
        return 1
    fi

    return 0
}

# --- Main loop ---

cd "$SCRIPT_DIR"
mkdir -p sessions

SESSION_NUM=0
PREV_STALE=0
LOOP_START=$(date +%s)
LOOP_TOTAL_IN=0
LOOP_TOTAL_OUT=0
LOOP_COST_CENTS=0

while true; do
    (( ++SESSION_NUM ))

    # Quota check
    if ! check_quota; then
        if [[ -n "$SINGLE" ]]; then
            exit 1
        fi
        say "Sleeping 60s before retry..."
        sleep 60
        continue
    fi

    # Generate or use resume UUID
    if [[ -n "$RESUME_UUID" ]]; then
        uuid="$RESUME_UUID"
        RESUME_UUID=""  # Only resume the first session
    else
        uuid=$(uuidgen | tr 'A-Z' 'a-z')
    fi
    CURRENT_UUID="$uuid"
    SESSION_START=$(date +%s)

    local_jsonl="$JSONL_DIR/$uuid.jsonl"

    # Determine if this is a resume
    claude_args=(--model opus)
    if [[ -f "$local_jsonl" ]]; then
        # Existing session — resume it
        claude_args+=(--resume "$uuid")
    else
        claude_args+=(--session-id "$uuid")
    fi
    claude_args+=(-p "$PROMPT")

    # Record git state at session start
    git_start=$(git rev-parse --short HEAD 2>/dev/null || echo "unknown")
    git_dirty=$(git status --porcelain 2>/dev/null | wc -l | tr -d ' ')

    say "Session #$SESSION_NUM starting: $uuid (git:$git_start dirty:$git_dirty)"
    log "Claude args: ${claude_args[*]}"

    # Launch claude in background
    ANTHROPIC_API_KEY= claude "${claude_args[@]}" \
        > "sessions/$uuid.stdout" 2>&1 &
    CLAUDE_PID=$!
    log "PID: $CLAUDE_PID"

    # Start the JSONL streaming filter (retried in monitor loop if JSONL not yet created)
    FILTER_PID=""
    start_filter "$uuid" || true

    # Monitor loop
    PREV_STALE=0
    JSONL_WARNED=""
    while kill -0 "$CLAUDE_PID" 2>/dev/null; do
        # Try to start filter if not yet running
        if [[ -z "$FILTER_PID" ]] || ! kill -0 "$FILTER_PID" 2>/dev/null; then
            FILTER_PID=""
            start_filter "$uuid" 2>/dev/null || true
        fi

        update_status "$SESSION_NUM" "$CLAUDE_PID" "$uuid"

        # Warn if JSONL never appeared
        if [[ ! -f "$local_jsonl" && -z "$JSONL_WARNED" ]]; then
            now_ts=$(date +%s)
            if (( now_ts - SESSION_START > 60 )); then
                log "WARNING: JSONL not created after 60s (session $uuid, PID $CLAUDE_PID)"
                JSONL_WARNED=1
            fi
        fi

        # Log state transitions: JSONL becoming stale
        # Only warn once the current session has actually written (mod_time > SESSION_START)
        if [[ -f "$local_jsonl" ]]; then
            now_ts=$(date +%s)
            mod_ts=$(stat -f%m "$local_jsonl" 2>/dev/null || echo "$now_ts")
            stale_secs=$(( now_ts - mod_ts ))

            if (( mod_ts > SESSION_START )); then
                if (( stale_secs > 300 && PREV_STALE <= 300 )); then
                    log "WARNING: JSONL stale for ${stale_secs}s (session $uuid, PID $CLAUDE_PID)"
                fi
            fi
            PREV_STALE=$stale_secs
        fi

        sleep 2
    done

    # Claude exited — wait may return 127 if already reaped, so don't let set -e kill us
    EXIT_CODE=0
    wait "$CLAUDE_PID" 2>/dev/null || EXIT_CODE=$?
    ELAPSED=$(( $(date +%s) - SESSION_START ))

    # Kill filter subshell (its EXIT trap kills tail + python3)
    if [[ -n "$FILTER_PID" ]]; then
        kill "$FILTER_PID" 2>/dev/null || true
        wait "$FILTER_PID" 2>/dev/null || true
    fi
    FILTER_PID=""

    # Final JSONL size
    final_size="0"
    if [[ -f "$local_jsonl" ]]; then
        final_size=$(stat -f%z "$local_jsonl" 2>/dev/null || echo 0)
    fi

    # Read final token counts before cleaning up state file
    final_tokens=""
    state_file="/tmp/agent-${uuid}-state.json"
    if [[ -f "$state_file" ]]; then
        IFS=$'\t' read -r final_tokens session_in session_out session_cost_cents < <(python3 -c "
import json, sys
try:
    with open(sys.argv[1]) as f:
        d = json.load(f)
    ti = d.get('tokens_in', 0)
    to = d.get('tokens_out', 0)
    cr = d.get('cache_read', 0)
    cc = d.get('cache_create', 0)
    total_in = ti + cr + cc
    def fmt(n):
        if n >= 1000000: return f'{n/1000000:.1f}M'
        if n >= 1000: return f'{n/1000:.0f}k'
        return str(n)
    cost = ti * 5 / 1e6 + cc * 6.25 / 1e6 + cr * 0.50 / 1e6 + to * 25 / 1e6
    cost_cents = int(cost * 100 + 0.5)
    tok = f'{fmt(total_in)}/{fmt(to)}~\${cost:.2f}' if (total_in or to) else ''
    print(f'{tok}\t{total_in}\t{to}\t{cost_cents}')
except:
    print('\t0\t0\t0')
" "$state_file" 2>/dev/null) || true
        LOOP_TOTAL_IN=$(( LOOP_TOTAL_IN + ${session_in:-0} ))
        LOOP_TOTAL_OUT=$(( LOOP_TOTAL_OUT + ${session_out:-0} ))
        LOOP_COST_CENTS=$(( LOOP_COST_CENTS + ${session_cost_cents:-0} ))
    fi

    # Record git state at session end
    git_end=$(git rev-parse --short HEAD 2>/dev/null || echo "unknown")
    git_commits=0
    if [[ "$git_start" != "unknown" && "$git_end" != "unknown" && "$git_start" != "$git_end" ]]; then
        git_commits=$(git rev-list --count "$git_start".."$git_end" 2>/dev/null || echo 0)
    fi

    # Clear status line and print summary
    printf '\r\033[K'
    token_summary=""
    if [[ -n "$final_tokens" ]]; then
        token_summary=" tokens=$final_tokens"
    fi
    git_summary=" git:$git_start..$git_end"
    if (( git_commits > 0 )); then
        git_summary="$git_summary(${git_commits} commits)"
    fi
    say "Session #$SESSION_NUM finished: exit=$EXIT_CODE duration=$(human_duration $ELAPSED) jsonl=$(human_size "$final_size")$token_summary$git_summary uuid=$uuid"

    # Clean up state file
    rm -f "$state_file"
    CURRENT_UUID=""

    if [[ -n "$SINGLE" ]]; then
        break
    fi

    if (( SLEEP_SECS > 0 )); then
        say "Sleeping ${SLEEP_SECS}s..."
        sleep "$SLEEP_SECS"
    fi
done
