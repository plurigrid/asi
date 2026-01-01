#!/usr/bin/env bash
# delta-derive.sh - Fast delta extraction via ACSets morphism
set -euo pipefail

RECENT="$1"
PREVIOUS="$2"
OUTPUT="${3:-/tmp/delta_analysis.json}"

# Fast extract
unzip -qo "$RECENT" conversations.json -d /tmp/recent_export 2>/dev/null
unzip -qo "$PREVIOUS" conversations.json -d /tmp/previous_export 2>/dev/null

# Single jq pass for full analysis
jq -s '
  (.[0] | map({key: .conversation_id, value: .}) | from_entries) as $r |
  (.[1] | map({key: .conversation_id, value: .}) | from_entries) as $p |
  {
    recent: (.[0] | length),
    previous: (.[1] | length),
    new: [.[0][] | select(.conversation_id | in($p) | not) | {
      id: .conversation_id, title: .title, nodes: (.mapping|length)
    }],
    mutated: [.[0][] | select(.conversation_id | in($p)) |
      select(.current_node != $p[.conversation_id].current_node) |
      {id: .conversation_id, title: .title, delta: ((.mapping|length) - ($p[.conversation_id].mapping|length))}
    ]
  }
' /tmp/recent_export/conversations.json /tmp/previous_export/conversations.json > "$OUTPUT"

jq -r '"Δ \(.recent - .previous) new | \(.mutated|length) mutated"' "$OUTPUT"
