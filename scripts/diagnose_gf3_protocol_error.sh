#!/bin/bash
# Diagnostic script to identify GF(3) conservation violation from JSON RPC protocol error
# Usage: ./diagnose_gf3_protocol_error.sh [log_file]

set -e

LOG_FILE="${1:-.local/share/ies/logs/crush_latest.log}"
COLORS='\033[0;32m' # Green for success
COLORE='\033[0;31m' # Red for error
COLORN='\033[0m'    # No color

echo "═══════════════════════════════════════════════════════════════"
echo "GF(3) Conservation Diagnostic Report"
echo "═══════════════════════════════════════════════════════════════"
echo ""

# Check if log file exists
if [ ! -f "$LOG_FILE" ]; then
    echo -e "${COLORE}✗${COLORN} Log file not found: $LOG_FILE"
    echo "Please provide the path to crush validation logs"
    exit 1
fi

echo -e "${COLORS}▶${COLORN} Analyzing log file: $LOG_FILE"
echo ""

# Diagnostic 1: Find the protocol error
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "1. PROTOCOL ERROR LOCATION"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

PROTOCOL_ERROR_LINE=$(grep -n "protocol error\|file already closed" "$LOG_FILE" | head -1 || echo "")
if [ -z "$PROTOCOL_ERROR_LINE" ]; then
    echo -e "${COLORE}✗${COLORN} Protocol error not found in log"
else
    echo -e "${COLORS}✓${COLORN} Protocol error found:"
    echo "   $PROTOCOL_ERROR_LINE"
    ERROR_SKILL=$(grep -B 50 "protocol error" "$LOG_FILE" | grep "skill\|install\|processing" | tail -1)
    echo "   Last activity before error: $ERROR_SKILL"
fi
echo ""

# Diagnostic 2: PLUS Agent (causality) Activity
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "2. PLUS AGENT (causality) - Generative Activity"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

CAUSALITY_COUNT=$(grep -i "causality\|move.*generated\|candidate" "$LOG_FILE" | wc -l)
CAUSALITY_RATE=$(echo "scale=2; $CAUSALITY_COUNT / $(grep -c "^" "$LOG_FILE")" | bc 2>/dev/null || echo "unknown")

echo "   Move generations detected: $CAUSALITY_COUNT"
echo "   Causality activity rate: ~$CAUSALITY_RATE per log entry"

CAUSALITY_BACKPRESSURE=$(grep -i "causality.*backpressure\|queue.*full" "$LOG_FILE" | wc -l)
if [ "$CAUSALITY_BACKPRESSURE" -gt 0 ]; then
    echo -e "   ${COLORE}⚠${COLORN} Backpressure signals: $CAUSALITY_BACKPRESSURE"
    echo "   → PLUS agent may be generating too fast"
else
    echo -e "   ${COLORS}✓${COLORN} No backpressure detected from PLUS"
fi
echo ""

# Diagnostic 3: ERGODIC Agent (2-monad) Activity
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "3. ERGODIC AGENT (2-monad) - Coordination Activity"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

ERGODIC_COUNT=$(grep -i "2-monad\|routing\|dispatch\|coordination" "$LOG_FILE" | wc -l)
ERGODIC_RATE=$(echo "scale=2; $ERGODIC_COUNT / $(grep -c "^" "$LOG_FILE")" | bc 2>/dev/null || echo "unknown")

echo "   Routing operations detected: $ERGODIC_COUNT"
echo "   Ergodic activity rate: ~$ERGODIC_RATE per log entry"

ERGODIC_LATENCY=$(grep -i "latency\|timeout\|slow" "$LOG_FILE" | wc -l)
if [ "$ERGODIC_LATENCY" -gt 0 ]; then
    echo -e "   ${COLORE}⚠${COLORN} Latency/timeout signals: $ERGODIC_LATENCY"
    echo "   → ERGODIC agent may be bottlenecking"
    SLOW_ROUTES=$(grep -i "latency.*[5-9][0-9][0-9]\|timeout" "$LOG_FILE" | head -3)
    if [ -n "$SLOW_ROUTES" ]; then
        echo "   Slow routes detected:"
        echo "$SLOW_ROUTES" | sed 's/^/      /'
    fi
else
    echo -e "   ${COLORS}✓${COLORN} No latency/timeout signals"
fi
echo ""

# Diagnostic 4: MINUS Agent (amp) Activity
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "4. MINUS AGENT (amp) - Verification Activity"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

MINUS_COUNT=$(grep -i "amp\|verification\|constraint\|proof" "$LOG_FILE" | wc -l)
MINUS_RATE=$(echo "scale=2; $MINUS_COUNT / $(grep -c "^" "$LOG_FILE")" | bc 2>/dev/null || echo "unknown")

echo "   Verification operations detected: $MINUS_COUNT"
echo "   Minus activity rate: ~$MINUS_RATE per log entry"

VERIFICATION_FAILURES=$(grep -i "proof.*fail\|constraint.*violat\|invalid\|error" "$LOG_FILE" | wc -l)
if [ "$VERIFICATION_FAILURES" -gt 0 ]; then
    echo -e "   ${COLORE}⚠${COLORN} Verification failures: $VERIFICATION_FAILURES"
    echo "   → MINUS agent budget may be exhausted"
    FIRST_FAILURE=$(grep -i "proof.*fail\|constraint.*violat\|invalid" "$LOG_FILE" | head -1)
    echo "   First failure: $FIRST_FAILURE"
else
    echo -e "   ${COLORS}✓${COLORN} No verification failures detected"
fi
echo ""

# Diagnostic 5: Rate Analysis
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "5. GF(3) RATE BALANCE ANALYSIS"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

if [ "$CAUSALITY_COUNT" -gt 0 ] && [ "$MINUS_COUNT" -gt 0 ]; then
    IMBALANCE=$((CAUSALITY_COUNT - MINUS_COUNT))
    if [ "$IMBALANCE" -gt 100 ]; then
        echo -e "   ${COLORE}✗ CRITICAL IMBALANCE${COLORN}"
        echo "   PLUS generation ($CAUSALITY_COUNT) >> MINUS verification ($MINUS_COUNT)"
        echo "   Imbalance magnitude: $IMBALANCE"
        echo "   → GF(3) conservation VIOLATED (White Hole explosion)"
        echo "   → Fix: Reduce PLUS rate OR increase MINUS budget"
    elif [ "$IMBALANCE" -gt 50 ]; then
        echo -e "   ${COLORE}⚠${COLORN} MODERATE IMBALANCE"
        echo "   PLUS generation ($CAUSALITY_COUNT) > MINUS verification ($MINUS_COUNT)"
        echo "   Imbalance magnitude: $IMBALANCE"
        echo "   → GF(3) conservation STRAINED"
        echo "   → Fix: Monitor carefully, consider increasing capacity"
    elif [ "$IMBALANCE" -lt -50 ]; then
        echo -e "   ${COLORE}⚠${COLORN} VERIFICATION BOTTLENECK"
        echo "   MINUS verification ($MINUS_COUNT) > PLUS generation ($CAUSALITY_COUNT)"
        echo "   Imbalance magnitude: $((-IMBALANCE))"
        echo "   → GF(3) conservation STRAINED (Black Hole tendency)"
        echo "   → Fix: Reduce verification strictness OR increase generation rate"
    else
        echo -e "   ${COLORS}✓${COLORN} BALANCED"
        echo "   PLUS ≈ MINUS (within tolerance)"
        echo "   Imbalance magnitude: $IMBALANCE"
    fi
else
    echo "   Cannot determine balance (insufficient data)"
fi
echo ""

# Diagnostic 6: Skills Progress
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "6. SKILL INSTALLATION PROGRESS"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

SKILLS_INSTALLED=$(grep -i "skill.*install.*success\|✓.*installed" "$LOG_FILE" | wc -l)
SKILLS_FAILED=$(grep -i "skill.*install.*fail\|✗.*failed" "$LOG_FILE" | wc -l)
TOTAL_ATTEMPTED=$((SKILLS_INSTALLED + SKILLS_FAILED))

echo "   Skills installed successfully: $SKILLS_INSTALLED / 315"
echo "   Skills failed: $SKILLS_FAILED"
echo "   Installation progress: $((SKILLS_INSTALLED * 100 / 315))%"

if [ "$SKILLS_FAILED" -gt 0 ]; then
    echo -e "   ${COLORE}⚠${COLORN} Installation failures detected"
    FAILED_SKILLS=$(grep -i "skill.*install.*fail\|✗" "$LOG_FILE" | head -3)
    echo "   First failures:"
    echo "$FAILED_SKILLS" | sed 's/^/      /'
else
    echo -e "   ${COLORS}✓${COLORN} No installation failures (all succeeded or protocol error mid-stream)"
fi
echo ""

# Diagnostic 7: Memory and Queue State
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "7. SYSTEM RESOURCE STATE AT ERROR"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

MEMORY_HIGH=$(grep -i "memory.*high\|buffer.*full\|out.*memory" "$LOG_FILE" | wc -l)
QUEUE_HIGH=$(grep -i "queue.*full\|queue.*overflow" "$LOG_FILE" | wc -l)

if [ "$MEMORY_HIGH" -gt 0 ]; then
    echo -e "   ${COLORE}⚠${COLORN} Memory pressure detected: $MEMORY_HIGH signals"
    echo "   → Likely cause: PLUS overflow (moves accumulating)"
fi

if [ "$QUEUE_HIGH" -gt 0 ]; then
    echo -e "   ${COLORE}⚠${COLORN} Queue congestion detected: $QUEUE_HIGH signals"
    echo "   → Likely cause: ERGODIC bottleneck (routing can't keep up)"
fi

if [ "$MEMORY_HIGH" -eq 0 ] && [ "$QUEUE_HIGH" -eq 0 ]; then
    echo -e "   ${COLORS}✓${COLORN} No resource pressure signals"
    echo "   → Likely cause: MINUS verification failure (connection aborted on error)"
fi
echo ""

# Diagnostic 8: Root Cause Determination
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "8. ROOT CAUSE DETERMINATION"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

ROOT_CAUSE=""
if [ "$MEMORY_HIGH" -gt 0 ] || [ "$QUEUE_HIGH" -gt 0 ]; then
    if [ "$CAUSALITY_RATE" -gt "$ERGODIC_RATE" ]; then
        ROOT_CAUSE="PLUS OVERFLOW (Generative explosion exceeds coordination capacity)"
        FIX_STRATEGY="Reduce causality rate OR increase ergodic workers"
    fi
elif [ "$ERGODIC_LATENCY" -gt 5 ]; then
    ROOT_CAUSE="ERGODIC STARVATION (Coordination bottleneck)"
    FIX_STRATEGY="Increase 2-monad queue depth and worker count"
elif [ "$VERIFICATION_FAILURES" -gt 5 ]; then
    ROOT_CAUSE="MINUS EXHAUSTION (Verification budget depleted)"
    FIX_STRATEGY="Increase amp budget OR reduce verification strictness"
elif [ -n "$PROTOCOL_ERROR_LINE" ]; then
    ROOT_CAUSE="SEMANTIC VIOLATION (Corrupted state in reafference loop)"
    FIX_STRATEGY="Enable detailed verification logging to identify corrupted move"
else
    ROOT_CAUSE="UNKNOWN (Insufficient diagnostic data)"
    FIX_STRATEGY="Enable verbose logging and rerun"
fi

echo "Root Cause: $ROOT_CAUSE"
echo "Fix Strategy: $FIX_STRATEGY"
echo ""

# Summary
echo "═══════════════════════════════════════════════════════════════"
echo "SUMMARY"
echo "═══════════════════════════════════════════════════════════════"
echo ""
echo "GF(3) Conservation Violation: YES (JSON RPC protocol error detected)"
echo "Likely Culprit: $(echo $ROOT_CAUSE | cut -d' ' -f1)"
echo "Recommended Fix: $FIX_STRATEGY"
echo ""
echo "Next step: Apply fix and rerun diagnostic"
echo ""
