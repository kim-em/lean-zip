#!/bin/bash
# go - Start an autonomous lean-zip session if Opus is available
#
# Usage: ./go [--verbose] [--force]
#
# Checks if Opus model has quota available, then starts a Claude session
# to continue work on lean-zip. Use --force to skip quota checks.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CLAUDE_AVAILABLE_MODEL="$HOME/.claude/skills/claude-usage/claude-available-model"
LOCKFILE="$SCRIPT_DIR/.go.lock"

# Check if a previous run is still active
if [ -f "$LOCKFILE" ]; then
    prev_pid=$(cat "$LOCKFILE")
    if kill -0 "$prev_pid" 2>/dev/null; then
        echo "[$(date '+%Y-%m-%d %H:%M:%S')] Previous run (PID $prev_pid) still active. Skipping."
        exit 0
    fi
    # Stale lock file - previous process exited without cleanup
    rm -f "$LOCKFILE"
fi

# Write lock file and ensure cleanup on exit
echo $$ > "$LOCKFILE"
trap 'rm -f "$LOCKFILE"' EXIT

# Log with timestamp
log() {
    echo "[$(date '+%Y-%m-%d %H:%M:%S')] $*"
}

VERBOSE=""
FORCE=""
for arg in "$@"; do
    case "$arg" in
        --verbose|-v) VERBOSE="--verbose" ;;
        --force|-f) FORCE=1 ;;
    esac
done

if [[ -n "$FORCE" ]]; then
    log "Force mode: skipping quota check."
else
    # Check model availability (verbose output goes to stderr, model name to stdout)
    if [[ -n "$VERBOSE" ]]; then
        "$CLAUDE_AVAILABLE_MODEL" --verbose >&2 || true
    fi

    if ! model=$("$CLAUDE_AVAILABLE_MODEL" 2>/dev/null); then
        log "No Claude quota available. Try again later."
        exit 1
    fi

    if [[ "$model" != "opus" ]]; then
        log "Only $model quota available. lean-zip work requires opus."
        exit 1
    fi
fi

log "Starting lean-zip session..."
cd "$SCRIPT_DIR"

# Generate timestamp for log file
TIMESTAMP=$(date -u +"%Y-%m-%d-%H%M%S")
mkdir -p sessions
STDOUT_LOG="sessions/${TIMESTAMP}.stdout"

# Use subscription auth (not API key) and run non-interactively
# Capture stdout to log file while also displaying it
ANTHROPIC_API_KEY= claude --model opus -p "/start" | tee "$STDOUT_LOG"
