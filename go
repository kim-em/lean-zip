#!/bin/bash
# go - Ralph Wiggum agent loop for lean-zip
#
# "I'm in danger!" - runs autonomous Claude sessions in a loop with
# live monitoring, structured logging, and process tracking.
#
# Sessions are auto-dispatched as planner or worker based on the issue
# queue depth (threshold: QUEUE_MIN=3). Planners create work items;
# workers execute them. Override with --prompt /plan or --prompt /work.
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
#   --prompt TEXT     Override default prompt (default: auto-dispatch)
#   --verbose, -v     Verbose quota check output

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CLAUDE_AVAILABLE_MODEL="$HOME/.claude/skills/claude-usage/claude-available-model"
LOGFILE="$SCRIPT_DIR/agent-loop.log"
WORKTREE_BASE="$SCRIPT_DIR/worktrees"
QUEUE_MIN=3   # Below this many unclaimed issues, sessions become planners

# --- Parse flags ---

FORCE=""
SINGLE=""
SLEEP_SECS=0
RESUME_UUID=""
PROMPT=""      # Empty = auto-dispatch based on queue depth
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

# --- Cleanup / Ctrl-C handling ---

CURRENT_UUID=""
FILTER_PID=""
CLAUDE_PID=""
CURRENT_WORKTREE=""
PLANNER_LOCK_HELD=""  # Set to 1 only when we successfully acquire the lock

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
    # Release planner lock only if we actually acquired it
    if [[ -n "$PLANNER_LOCK_HELD" ]]; then
        cd "$SCRIPT_DIR" && ./coordination unlock-planner 2>/dev/null || true
        PLANNER_LOCK_HELD=""
    fi

    # Kill Claude if still running (prevent orphan against removed worktree)
    if [[ -n "$CLAUDE_PID" ]] && kill -0 "$CLAUDE_PID" 2>/dev/null; then
        kill "$CLAUDE_PID" 2>/dev/null || true
        wait "$CLAUDE_PID" 2>/dev/null || true
    fi

    # Kill the filter python3 process (direct PID, no subshell indirection)
    if [[ -n "$FILTER_PID" ]]; then
        kill "$FILTER_PID" 2>/dev/null || true
        wait "$FILTER_PID" 2>/dev/null || true
    fi

    # Clean up state file
    [[ -n "$CURRENT_UUID" ]] && rm -f "/tmp/agent-${CURRENT_UUID}-state.json"

    # Remove worktree + branch if still present
    if [[ -n "$CURRENT_WORKTREE" && -d "$CURRENT_WORKTREE" ]]; then
        log "Cleaning up worktree: $CURRENT_WORKTREE"
        git -C "$SCRIPT_DIR" worktree remove --force "$CURRENT_WORKTREE" 2>/dev/null || true
    fi
    if [[ -n "${wt_branch:-}" ]]; then
        git branch -D "$wt_branch" 2>/dev/null || true
    fi

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
        [[ -n "$PROMPT" ]] && resume_cmd="$resume_cmd --prompt '$PROMPT'"
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
    local pid=$1
    local uuid=$2
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
    local last_text="" tokens_str="" claimed_issue="" pr_number=""
    if [[ -f "$state_file" ]]; then
        IFS=$'\t' read -r last_text tokens_str claimed_issue pr_number < <(python3 -c "
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
        line = text.strip().split('\n')[-1]
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
    ci = d.get('claimed_issue', 0)
    pr = d.get('pr_number', 0)
    # Replace tabs in line to avoid breaking TSV parsing
    line = line.replace('\t', ' ')
    print(f'{line}\t{tok}\t{ci}\t{pr}')
except:
    print('\t\t0\t0')
" "$state_file" 2>/dev/null) || true
    fi

    # Elapsed time for this session
    local elapsed=""
    if [[ -n "${SESSION_START:-}" ]]; then
        elapsed=" $(human_duration $(( now - SESSION_START )))"
    fi

    # Build mode label: planner, worker, worker #42, worker #42->PR
    local mode_label="${SESSION_MODE:-session}"
    if [[ "$SESSION_MODE" == "worker" && -n "$claimed_issue" && "$claimed_issue" != "0" ]]; then
        if [[ -n "$pr_number" && "$pr_number" != "0" ]]; then
            mode_label="worker #${claimed_issue}->PR"
        else
            mode_label="worker #${claimed_issue}"
        fi
    fi

    # Build status line
    local status
    status=$(printf '[%s] %s%s | %s%s | %s' \
        "$(date '+%H:%M:%S')" "$mode_label" "$elapsed" \
        "$size_str" "$age_str" "$api_status")
    if [[ -n "$tokens_str" ]]; then
        status="$status | tok:$tokens_str"
    fi

    if [[ -n "$last_text" ]]; then
        # Truncate to fit terminal width (leave room for status prefix)
        local prefix_len=${#status}
        local max_text=$(( ${COLUMNS:-200} - prefix_len - 6 ))
        if (( max_text > 10 )) && (( ${#last_text} > max_text )); then
            last_text="${last_text:0:$max_text}..."
        fi
        status="$status | $last_text"
    fi

    # Overwrite current line
    printf '\r\033[K%s' "$status"
}

# --- JSONL file watcher ---
# A standalone python3 process polls the JSONL file, extracts the latest
# assistant text/tool info and accumulates token usage. Reads from byte 0
# for accurate lifetime totals. Direct PID tracking (no subshell) means
# kill -0 reliably detects filter death.

start_filter() {
    local uuid=$1
    local jsonl_path="$JSONL_DIR/$uuid.jsonl"
    local state_file="/tmp/agent-${uuid}-state.json"

    # Single python3 process that watches the file directly. No tail -f pipe
    # means no SIGPIPE issues, no orphaned tail processes, and the PID we
    # track IS python3 itself (so kill -0 accurately detects filter death).
    # Reads from byte 0 for accurate lifetime totals. Handles file-not-yet-
    # existing by polling internally.
    python3 -c "
import json, sys, time, os, signal, re

state_file = sys.argv[1]
jsonl_path = sys.argv[2]

signal.signal(signal.SIGTERM, lambda s, f: sys.exit(0))

last_text = ''
total_in = 0
total_out = 0
total_cache_read = 0
total_cache_create = 0
claimed_issue = 0
pr_number = 0
pos = 0

def write_state(ts=''):
    with open(state_file, 'w') as f:
        json.dump({'ts': ts, 'text': last_text,
                   'tokens_in': total_in, 'tokens_out': total_out,
                   'cache_read': total_cache_read,
                   'cache_create': total_cache_create,
                   'claimed_issue': claimed_issue,
                   'pr_number': pr_number}, f)

while True:
    try:
        if not os.path.exists(jsonl_path):
            time.sleep(1)
            continue
        with open(jsonl_path, 'rb') as f:
            f.seek(pos)
            while True:
                line = f.readline()
                if not line:
                    break
                if not line.endswith(b'\n'):
                    break  # Partial line — retry next poll
                pos += len(line)
                try:
                    d = json.loads(line)
                    ts = d.get('timestamp', '')
                    if d.get('type') == 'assistant':
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
                                detail = ''
                                if name == 'Bash':
                                    desc = inp.get('description', '')
                                    cmd = inp.get('command', '')
                                    # Detect coordination claim/create-pr (anchored to avoid false positives)
                                    m = re.search(r'(?:^|&&\s*|;\s*)(?:\./)?coordination\s+claim\s+(\d+)', cmd)
                                    if m:
                                        claimed_issue = int(m.group(1))
                                    m = re.search(r'(?:^|&&\s*|;\s*)(?:\./)?coordination\s+create-pr\s+(\d+)', cmd)
                                    if m:
                                        pr_number = int(m.group(1))
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
                        write_state(ts)
                except:
                    pass
    except:
        pass
    time.sleep(1)
" "$state_file" "$jsonl_path" &
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
mkdir -p sessions "$WORKTREE_BASE"

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

    # Housekeeping: unblock issues whose dependencies have resolved
    cd "$SCRIPT_DIR" && ./coordination check-blocked 2>/dev/null || true

    # Auto-dispatch: determine session mode based on queue depth
    SESSION_MODE=""
    EFFECTIVE_PROMPT="$PROMPT"
    if [[ -z "$EFFECTIVE_PROMPT" ]]; then
        if ! queue_depth=$(cd "$SCRIPT_DIR" && ./coordination queue-depth 2>&1); then
            say "warning: coordination queue-depth failed: $queue_depth"
            say "Defaulting to planner mode"
            queue_depth=0
        fi
        if (( queue_depth < QUEUE_MIN )); then
            # Try to acquire planner lock (prevents concurrent planners)
            if cd "$SCRIPT_DIR" && ./coordination lock-planner 2>/dev/null; then
                SESSION_MODE="planner"
                PLANNER_LOCK_HELD=1
                EFFECTIVE_PROMPT="/plan"
                say "Queue depth: $queue_depth (< $QUEUE_MIN) → planner session (lock acquired)"
            elif (( queue_depth > 0 )); then
                SESSION_MODE="worker"
                EFFECTIVE_PROMPT="/work"
                say "Queue depth: $queue_depth (< $QUEUE_MIN) but planner lock held → worker session"
            else
                say "Queue depth: 0 and planner lock held. Waiting 60s..."
                sleep 60
                continue
            fi
        else
            SESSION_MODE="worker"
            EFFECTIVE_PROMPT="/work"
            say "Queue depth: $queue_depth (≥ $QUEUE_MIN) → worker session"
        fi
    elif [[ "$EFFECTIVE_PROMPT" == "/plan" ]]; then
        SESSION_MODE="planner"
    elif [[ "$EFFECTIVE_PROMPT" == "/work" ]]; then
        SESSION_MODE="worker"
    fi

    # Generate or use resume UUID
    if [[ -n "$RESUME_UUID" ]]; then
        uuid="$RESUME_UUID"
        RESUME_UUID=""  # Only resume the first session
    else
        uuid=$(uuidgen | tr 'A-Z' 'a-z')
    fi
    CURRENT_UUID="$uuid"
    export LEAN_ZIP_SESSION_ID="$uuid"
    SESSION_START=$(date +%s)

    # Create a fresh worktree for this session
    short_id="${uuid:0:8}"
    wt_branch="agent/$short_id"
    wt_dir="$WORKTREE_BASE/$short_id"
    CURRENT_WORKTREE="$wt_dir"

    if ! git -C "$SCRIPT_DIR" fetch origin master --quiet 2>/dev/null; then
        log "WARNING: git fetch failed, using potentially stale origin/master"
    fi
    # Remove any leftover worktree/branch from a crashed previous run
    if [[ -d "$wt_dir" ]]; then
        git -C "$SCRIPT_DIR" worktree remove --force "$wt_dir" 2>/dev/null || true
    fi
    git branch -D "$wt_branch" 2>/dev/null || true
    git -C "$SCRIPT_DIR" worktree add -b "$wt_branch" "$wt_dir" origin/master --quiet

    # Copy .lake/ build cache for fast iteration (skip for planner sessions)
    if [[ "$SESSION_MODE" != "planner" && -d "$SCRIPT_DIR/.lake" ]]; then
        rsync -a --quiet "$SCRIPT_DIR/.lake/" "$wt_dir/.lake/" 2>/dev/null || true
    fi

    # JSONL_DIR is based on the worktree path (Claude Code uses cwd to determine it)
    JSONL_DIR="$HOME/.claude/projects/$(echo "$wt_dir" | tr '/' '-')"
    local_jsonl="$JSONL_DIR/$uuid.jsonl"

    # For resume: the JSONL lives under the *original* project dir, not the
    # worktree's. Find it and copy it so claude can discover the session.
    if [[ ! -f "$local_jsonl" ]]; then
        orig_jsonl=$(find "$HOME/.claude/projects" -name "$uuid.jsonl" -print -quit 2>/dev/null)
        if [[ -n "$orig_jsonl" ]]; then
            mkdir -p "$JSONL_DIR"
            cp "$orig_jsonl" "$local_jsonl"
            log "Copied JSONL for resume: $orig_jsonl -> $local_jsonl"
        fi
    fi

    # Determine if this is a resume
    claude_args=(--model opus)
    if [[ -f "$local_jsonl" ]]; then
        # Existing session — resume it
        claude_args+=(--resume "$uuid")
    else
        claude_args+=(--session-id "$uuid")
    fi
    claude_args+=(-p "$EFFECTIVE_PROMPT")

    # Record git state at session start
    git_start=$(git -C "$wt_dir" rev-parse --short HEAD 2>/dev/null || echo "unknown")

    say "Session starting: ${SESSION_MODE:-unknown} $uuid worktree=$short_id (git:$git_start)"
    log "Claude args: ${claude_args[*]} cwd=$wt_dir"

    # Launch claude in the worktree directory (exec replaces subshell so $! is claude's PID)
    (cd "$wt_dir" && ANTHROPIC_API_KEY= exec claude "${claude_args[@]}") \
        > "$SCRIPT_DIR/sessions/$uuid.stdout" 2>&1 &
    CLAUDE_PID=$!
    log "PID: $CLAUDE_PID"

    # Start the JSONL file watcher (restarts automatically in monitor loop if it dies)
    FILTER_PID=""
    start_filter "$uuid"

    # Monitor loop
    PREV_STALE=0
    JSONL_WARNED=""
    while kill -0 "$CLAUDE_PID" 2>/dev/null; do
        # Restart filter if it died (direct PID check — no subshell indirection)
        if ! kill -0 "$FILTER_PID" 2>/dev/null; then
            log "Filter died (PID $FILTER_PID), restarting"
            FILTER_PID=""
            start_filter "$uuid"
        fi

        update_status "$CLAUDE_PID" "$uuid"

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

    # Kill filter python3 process
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

    # Record git state at session end (from the worktree)
    git_end=$(git -C "$wt_dir" rev-parse --short HEAD 2>/dev/null || echo "unknown")
    git_commits=0
    if [[ "$git_start" != "unknown" && "$git_end" != "unknown" && "$git_start" != "$git_end" ]]; then
        git_commits=$(git -C "$wt_dir" rev-list --count "$git_start".."$git_end" 2>/dev/null || echo 0)
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
    say "Session finished: ${SESSION_MODE:-unknown} exit=$EXIT_CODE duration=$(human_duration $ELAPSED) jsonl=$(human_size "$final_size")$token_summary$git_summary uuid=$uuid"

    # Release planner lock only if we acquired it
    if [[ -n "$PLANNER_LOCK_HELD" ]]; then
        cd "$SCRIPT_DIR" && ./coordination unlock-planner 2>/dev/null || true
        PLANNER_LOCK_HELD=""
    fi

    # Clean up worktree
    if [[ -d "$wt_dir" ]]; then
        git -C "$SCRIPT_DIR" worktree remove --force "$wt_dir" 2>/dev/null || true
        git branch -D "$wt_branch" 2>/dev/null || true
        log "Removed worktree: $wt_dir"
    fi
    CURRENT_WORKTREE=""

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
