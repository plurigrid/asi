#!/usr/bin/env bash
# Find the highest rank in a goals org file and return next rank.
# Usage: next-rank.sh [goals-file]
# Default: looks for goals-*.org in current dir or ~/worlds/

GOALS_FILE="${1:-}"
if [ -z "$GOALS_FILE" ]; then
    # Auto-discover: newest goals-*.org
    for d in . ~/worlds ~/v; do
        found=$(ls -t "$d"/goals-*.org 2>/dev/null | head -1)
        if [ -n "$found" ]; then GOALS_FILE="$found"; break; fi
    done
fi

if [ ! -f "$GOALS_FILE" ]; then
    echo "1"
    exit 0
fi

# Extract highest rank from :RANK: properties
max=$(grep -oP ":RANK:\s+\K\d+" "$GOALS_FILE" 2>/dev/null | sort -n | tail -1)
if [ -z "$max" ]; then
    echo "1"
else
    echo $((max + 1))
fi
