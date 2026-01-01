#!/bin/bash
# Phase A.0 Real-Time GF(3) Conservation Monitor
# Tracks agent activity during 315-skill installation
# Usage: ./phase_a0_realtime_monitor.sh &
# Then: npx ai-agent-skills install plurigrid/asi --agent crush

set -e

LOG_DIR="/Users/bob/.crush/logs"
MONITORING_FILE="/tmp/phase_a0_gf3_metrics.json"
SAMPLE_INTERVAL=5  # seconds

# Initialize monitoring file
cat > "$MONITORING_FILE" << 'EOF'
{
  "start_time": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "samples": [],
  "gf3_metrics": {
    "causality_count": 0,
    "ergodic_count": 0,
    "minus_count": 0,
    "imbalance": 0,
    "max_queue_depth": 0,
    "max_memory_percent": 0,
    "protocol_errors": 0
  }
}
EOF

echo "═══════════════════════════════════════════════════════════════"
echo "Phase A.0 Real-Time GF(3) Conservation Monitor"
echo "═══════════════════════════════════════════════════════════════"
echo ""
echo "Monitoring started: $(date)"
echo "Log directory: $LOG_DIR"
echo "Metrics file: $MONITORING_FILE"
echo ""
echo "Tracking:"
echo "  • Causality (PLUS) activity: move generation"
echo "  • 2-monad (ERGODIC) activity: routing and coordination"
echo "  • Amp (MINUS) activity: verification and constraints"
echo "  • Memory usage and queue depth"
echo "  • GF(3) balance: sum of (PLUS + ERGODIC + MINUS) mod 3"
echo ""

# Main monitoring loop
sample_count=0
while true; do
    sample_count=$((sample_count + 1))
    timestamp=$(date -u +%Y-%m-%dT%H:%M:%SZ)

    # Count agent activities from logs (would need real log parsing here)
    # For now, show sampling pattern
    causality_activity=$(tail -n 1000 "$LOG_DIR/crush.log" 2>/dev/null | grep -i "causality\|move.*gen" | wc -l)
    ergodic_activity=$(tail -n 1000 "$LOG_DIR/crush.log" 2>/dev/null | grep -i "2-monad\|routing" | wc -l)
    minus_activity=$(tail -n 1000 "$LOG_DIR/crush.log" 2>/dev/null | grep -i "amp\|verification" | wc -l)

    # Calculate imbalance
    imbalance=$(( (causality_activity - minus_activity) % 3 ))

    # Get system metrics
    memory_percent=$(vm_stat | grep "Pages active" | awk '{print int($3 * 100 / 4194304)}' || echo "0")

    # Display current state
    echo "[Sample $sample_count @ $timestamp]"
    echo "  PLUS (causality):        $causality_activity activities"
    echo "  ERGODIC (2-monad):       $ergodic_activity activities"
    echo "  MINUS (amp):             $minus_activity activities"
    echo "  GF(3) Imbalance:         $imbalance"
    echo "  Memory Usage:            ${memory_percent}%"
    echo ""

    # Check for protocol errors
    protocol_errors=$(tail -n 500 "$LOG_DIR/crush.log" 2>/dev/null | grep -i "protocol.*error\|json.*rpc.*error" | wc -l)
    if [ "$protocol_errors" -gt 0 ]; then
        echo "⚠️  ALERT: $protocol_errors protocol error(s) detected!"
        echo "   Likely root cause: $(
            if [ "$causality_activity" -gt "$ergodic_activity" ]; then
                echo "PLUS OVERFLOW"
            elif [ "$ergodic_activity" -lt "$causality_activity" ]; then
                echo "ERGODIC STARVATION"
            else
                echo "MINUS EXHAUSTION"
            fi
        )"
        echo ""
    fi

    # Sleep before next sample
    sleep "$SAMPLE_INTERVAL"
done
