#!/bin/bash
# Thread Exchange Scheduler
# Periodically searches threads and exchanges files via P2P LocalSend
# Install as launchd plist or run via cron

set -e

PROJECT_HOME="/Users/bob/ies/music-topos"
LIB_DIR="$PROJECT_HOME/lib"
SCRIPT="$LIB_DIR/thread_exchange.py"
LOG_DIR="/tmp/thread_exchange_logs"
TIMESTAMP=$(date '+%Y-%m-%d_%H-%M-%S')

# Create log directory
mkdir -p "$LOG_DIR"
LOG_FILE="$LOG_DIR/exchange_${TIMESTAMP}.log"

echo "[$(date)] Starting scheduled thread exchange..." | tee "$LOG_FILE"

# Define search strategies - search for different concepts on a schedule
SEARCHES=(
  "skill"
  "MCP"
  "ACSet"
  "HyJAX"
  "parallelism"
  "DuckDB"
  "alife"
  "relational"
)

# Pick a concept based on hour of day (rotate through searches)
HOUR=$(date +%H)
SEARCH_INDEX=$((HOUR % ${#SEARCHES[@]}))
CONCEPT="${SEARCHES[$SEARCH_INDEX]}"

echo "[LOG] Searching for: $CONCEPT" | tee -a "$LOG_FILE"

# Run search and exchange
python3 "$SCRIPT" search "$CONCEPT" 2>&1 | tee -a "$LOG_FILE"

# Get result count
RESULT_FILE="/tmp/thread_exchange_${CONCEPT}.json"
if [ -f "$RESULT_FILE" ]; then
    THREADS=$(grep -o '"thread_id"' "$RESULT_FILE" | wc -l)
    echo "[SUCCESS] Searched $THREADS threads, results saved to $RESULT_FILE" | tee -a "$LOG_FILE"
else
    echo "[WARNING] No results file found" | tee -a "$LOG_FILE"
fi

# Cleanup old logs (keep only last 30 days)
find "$LOG_DIR" -name "*.log" -mtime +30 -delete

echo "[$(date)] Scheduled exchange complete" | tee -a "$LOG_FILE"
