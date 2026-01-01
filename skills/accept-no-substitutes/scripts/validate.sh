#!/usr/bin/env bash
# accept-no-substitutes validator - runs as PostToolUse hook
# Reads CLAUDE_TOOL_OUTPUT or stdin, exits non-zero on substitution detected

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SKILL_DIR="$(dirname "$SCRIPT_DIR")"

# Get input from hook env or stdin
if [[ -n "${CLAUDE_TOOL_OUTPUT:-}" ]]; then
    INPUT="$CLAUDE_TOOL_OUTPUT"
elif [[ -n "${1:-}" ]] && [[ -f "$1" ]]; then
    INPUT=$(cat "$1")
else
    INPUT=$(cat)
fi

# Phase 1: Regex scan (fast path)
CRITICAL_RE='(TODO|FIXME|TBD|placeholder|temporary|pseudo[-_]|xxx+|yyy+)'
WARNING_RE='(mock[-_]|fake[-_]|stub[-_]|dummy[-_]|skeleton|for now|later)'

critical_matches=$(echo "$INPUT" | grep -oiE "$CRITICAL_RE" 2>/dev/null | head -5 || true)
warning_matches=$(echo "$INPUT" | grep -oiE "$WARNING_RE" 2>/dev/null | head -3 || true)

# Phase 2: Compression test (detect boilerplate)
if command -v python3 &>/dev/null; then
    compress_ratio=$(python3 -c "
import sys, zlib
text = sys.stdin.read()
if len(text) > 100:
    ratio = len(zlib.compress(text.encode())) / len(text)
    print(f'{ratio:.3f}')
else:
    print('1.0')
" <<< "$INPUT" 2>/dev/null || echo "1.0")

    if (( $(echo "$compress_ratio < 0.25" | bc -l 2>/dev/null || echo 0) )); then
        echo "[BOILERPLATE] Suspiciously compressible (ratio=$compress_ratio)" >&2
        critical_matches="${critical_matches}
[boilerplate-detected]"
    fi
fi

# Phase 3: AST check if tree-sitter available and looks like code
if command -v tree-sitter &>/dev/null && echo "$INPUT" | grep -qE '(def |function |class |const |let |var )'; then
    # Write to temp, query for TODO comments
    tmp=$(mktemp)
    echo "$INPUT" > "$tmp"
    ast_todos=$(tree-sitter query '(comment) @c' "$tmp" 2>/dev/null | grep -iE 'TODO|FIXME' || true)
    rm -f "$tmp"

    if [[ -n "$ast_todos" ]]; then
        critical_matches="${critical_matches}
[ast-comment-todo]"
    fi
fi

# Emit result
if [[ -n "$critical_matches" ]]; then
    echo "[SUBSTITUTION DETECTED - CRITICAL]" >&2
    echo "$critical_matches" | head -5 >&2
    echo "" >&2
    echo "HALT: Output contains placeholder tokens." >&2
    echo "ABANDON: This content cannot be accepted." >&2
    echo "INTERVIEW: User input required." >&2

    # Emit GF(3) MINUS signal
    echo '{"trit": -1, "skill": "accept-no-substitutes", "action": "REJECT"}' > /tmp/gf3-signal.json 2>/dev/null || true

    exit 1
elif [[ -n "$warning_matches" ]]; then
    echo "[SUBSTITUTION WARNING]" >&2
    echo "$warning_matches" | head -3 >&2
    exit 0  # Warn but don't block
else
    exit 0
fi
