#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF' >&2
Usage:
  scripts/beeper_send_file.sh <chat_id> <file_path> [text]

Sends a single attachment (plus optional text) via Beeper Desktop API.

Auth:
  - If BEEPER_ACCESS_TOKEN is set, uses it.
  - Else reads it from fnox:
      fnox get BEEPER_ACCESS_TOKEN --age-key-file ~/.age/key.txt

Config:
  - BEEPER_DESKTOP_API_BASE (default: http://localhost:23373)
EOF
}

if [[ $# -lt 2 ]]; then
  usage
  exit 2
fi

CHAT_ID="$1"
FILE_PATH="$2"
TEXT="${3-}"

if [[ ! -f "$FILE_PATH" ]]; then
  echo "File not found: $FILE_PATH" >&2
  exit 1
fi

API_BASE="${BEEPER_DESKTOP_API_BASE:-http://localhost:23373}"

if [[ -n "${BEEPER_ACCESS_TOKEN-}" ]]; then
  TOKEN="$BEEPER_ACCESS_TOKEN"
else
  if ! command -v fnox >/dev/null 2>&1; then
    echo "Missing fnox and BEEPER_ACCESS_TOKEN is not set." >&2
    exit 1
  fi
  AGE_KEY_FILE="${AGE_KEY_FILE:-$HOME/.age/key.txt}"
  if [[ ! -f "$AGE_KEY_FILE" ]]; then
    echo "Missing age key file: $AGE_KEY_FILE" >&2
    exit 1
  fi
  TOKEN="$(fnox get BEEPER_ACCESS_TOKEN --age-key-file "$AGE_KEY_FILE")"
fi

if ! command -v jq >/dev/null 2>&1; then
  echo "Missing jq" >&2
  exit 1
fi

ENC_CHAT_ID="$(jq -nr --arg v "$CHAT_ID" '$v|@uri')"

# 1) Upload
upload_resp="$(
  curl -sS -X POST "$API_BASE/v1/assets/upload" \
    -H "Authorization: Bearer $TOKEN" \
    -F "file=@${FILE_PATH}"
)"

upload_id="$(printf '%s' "$upload_resp" | jq -r '.uploadID // .uploadId // .id // empty')"
if [[ -z "$upload_id" ]]; then
  echo "Failed to upload asset (no uploadID in response)." >&2
  printf '%s\n' "$upload_resp" >&2
  exit 1
fi

# 2) Send message with attachment
filename="$(basename "$FILE_PATH")"

if [[ -n "$TEXT" ]]; then
  body="$(jq -nc --arg text "$TEXT" --arg uploadID "$upload_id" --arg fileName "$filename" '{text:$text, attachment:{uploadID:$uploadID, fileName:$fileName}}')"
else
  body="$(jq -nc --arg uploadID "$upload_id" --arg fileName "$filename" '{attachment:{uploadID:$uploadID, fileName:$fileName}}')"
fi

send_resp="$(
  curl -sS -X POST "$API_BASE/v1/chats/$ENC_CHAT_ID/messages" \
    -H "Authorization: Bearer $TOKEN" \
    -H "Content-Type: application/json" \
    -d "$body"
)"

pending_id="$(printf '%s' "$send_resp" | jq -r '.pendingMessageID // empty')"
if [[ -z "$pending_id" ]]; then
  echo "Sent request, but did not get pendingMessageID (raw response below)." >&2
  printf '%s\n' "$send_resp" >&2
  exit 1
fi

echo "Sent attachment to $CHAT_ID (pendingMessageID=$pending_id)"

