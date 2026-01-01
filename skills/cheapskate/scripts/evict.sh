#!/usr/bin/env bash
# cheapskate freeloader eviction - every token must pay rent
set -euo pipefail

INPUT="${1:-$(cat)}"

# Freeloader patterns - tokens that don't pay rent
PREAMBLE_RE="(I'll help|I'd be happy|Let me|I can help|I understand|Sure,|Of course,|Certainly)"
HEDGING_RE="(it seems|maybe|perhaps|might be|could be|I think|I believe|probably)"
RESTATING_RE="(You asked|You want|You mentioned|As you said|You're asking)"
FILLER_RE="(Let me think|Hmm|Well,|So,|Now,|Okay,|Alright)"
PERMISSION_RE="(Should I|Would you like|Do you want|Shall I|Can I)"
APOLOGY_RE="(Sorry|I apologize|My mistake|I'm sorry)"
SUMMARY_RE="(To summarize|In summary|To recap|In conclusion|Overall)"

evictions=0

check_pattern() {
    local name="$1"
    local pattern="$2"
    local matches
    matches=$(echo "$INPUT" | grep -oiE "$pattern" 2>/dev/null | head -3 || true)
    if [[ -n "$matches" ]]; then
        echo "[EVICT] $name: $matches" >&2
        ((evictions++)) || true
    fi
}

check_pattern "PREAMBLE" "$PREAMBLE_RE"
check_pattern "HEDGING" "$HEDGING_RE"
check_pattern "RESTATING" "$RESTATING_RE"
check_pattern "FILLER" "$FILLER_RE"
check_pattern "PERMISSION" "$PERMISSION_RE"
check_pattern "APOLOGY" "$APOLOGY_RE"
check_pattern "SUMMARY" "$SUMMARY_RE"

# Work ratio check
total_chars=${#INPUT}
if [[ $total_chars -gt 200 ]]; then
    # Count code blocks (paying rent)
    code_chars=$(echo "$INPUT" | grep -oE '```[^`]*```' 2>/dev/null | wc -c || echo 0)
    # Count tool references (paying rent)
    tool_chars=$(echo "$INPUT" | grep -oE '\[Tool:|<tool>|</tool>' 2>/dev/null | wc -c || echo 0)

    work_chars=$((code_chars + tool_chars))
    prose_chars=$((total_chars - work_chars))

    if [[ $total_chars -gt 0 ]]; then
        prose_ratio=$((prose_chars * 100 / total_chars))
        if [[ $prose_ratio -gt 80 ]]; then
            echo "[EVICT] PROSE_HEAVY: ${prose_ratio}% prose, not enough work" >&2
            ((evictions++)) || true
        fi
    fi
fi

# Compression check (repetitive = freeloading)
if command -v python3 &>/dev/null && [[ $total_chars -gt 100 ]]; then
    ratio=$(python3 -c "
import sys, zlib
t = sys.stdin.read()
r = len(zlib.compress(t.encode())) / len(t) if t else 1
print(f'{r:.2f}')
" <<< "$INPUT" 2>/dev/null || echo "1.0")

    if (( $(echo "$ratio < 0.25" | bc -l 2>/dev/null || echo 0) )); then
        echo "[EVICT] REPETITIVE: compression=$ratio (too compressible)" >&2
        ((evictions++)) || true
    fi
fi

# Verdict
if [[ $evictions -gt 2 ]]; then
    echo "" >&2
    echo "RENT UNPAID: $evictions freeloader patterns detected" >&2
    echo "Tokens must do work. Evicting." >&2
    echo '{"trit": -1, "skill": "cheapskate", "action": "EVICT", "count": '$evictions'}' > /tmp/gf3-signal.json 2>/dev/null || true
    exit 1
elif [[ $evictions -gt 0 ]]; then
    echo "[WARN] $evictions minor freeloaders detected" >&2
    exit 0
else
    exit 0
fi
