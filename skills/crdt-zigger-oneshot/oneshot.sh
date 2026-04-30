#!/usr/bin/env bash
set -uo pipefail
EC=/nix/store/477v13kr244fc37pi6fk3syxwqa5yslk-emacs-nox-30.2/bin/emacsclient
TOKEN=$(/Users/alice/.cargo/bin/fnox get BEEPER_ACCESS_TOKEN -c /Users/alice/worlds/f/fnox.toml --age-key-file /Users/alice/.age/key.txt 2>/dev/null)
ROOM='!NhltGRLZWLUeHEBiFT:beeper.com'
ENC=$(python3 -c "import urllib.parse; print(urllib.parse.quote('${ROOM}', safe=''))")
HOST=100.87.209.11
PORT=6530
NONCE="${1:-0x$(date +%s | xxd -p | head -c 16)$(printf '%08x' $RANDOM$RANDOM)}"
TS_NOW=$(date -u +%Y-%m-%dT%H:%M:%SZ)

# --- Path A: Matrix DM (independent, idempotent via 5-min same-nonce check)
RECENT=$(curl -s -m 8 -6 -H "authorization: Bearer $TOKEN" "http://[::1]:23373/v1/chats/${ENC}/messages?limit=5&direction=before" 2>/dev/null)
SKIP_A=$(echo "$RECENT" | python3 -c "
import json,sys,datetime as dt,os
nonce=os.environ.get('NONCE','')
try:
    d=json.load(sys.stdin)
    cutoff=dt.datetime.utcnow()-dt.timedelta(minutes=5)
    for i in d.get('items',[]):
        if i.get('senderID')!='@greenteatree01:beeper.com': continue
        ts=i.get('timestamp','')
        if not ts: continue
        t=dt.datetime.fromisoformat(ts.replace('Z',''))
        if t>cutoff and nonce in (i.get('text') or ''):
            print('skip')
            break
except: pass
" NONCE="$NONCE" 2>/dev/null)

if [ "$SKIP_A" = "skip" ]; then
  PATH_A_STATUS='{"sent":false,"reason":"already_sent_within_5min","verified_in_room":true}'
else
  BODY=$(python3 -c "import json,os; print(json.dumps({'text': f'oneshot handshake {os.environ[\"NONCE\"]} ts={os.environ[\"TS_NOW\"]} — alice/bob-mod confirms reachability via this dm + crdt-connect to 100.87.209.11:6530. echo nonce to verify path-invariance.'}))" 2>/dev/null)
  SEND_OUT=$(NONCE="$NONCE" TS_NOW="$TS_NOW" curl -s -m 12 -6 -X POST -H "authorization: Bearer $TOKEN" -H 'content-type: application/json' --data "$BODY" "http://[::1]:23373/v1/chats/${ENC}/messages")
  PEND=$(echo "$SEND_OUT" | python3 -c "import json,sys
try: print(json.load(sys.stdin).get('pendingMessageID',''))
except: pass" 2>/dev/null)
  sleep 5
  VERIFY=$(curl -s -m 8 -6 -H "authorization: Bearer $TOKEN" "http://[::1]:23373/v1/chats/${ENC}/messages?limit=3&direction=before" 2>/dev/null | python3 -c "
import json,sys,os
nonce=os.environ.get('NONCE','')
try:
    d=json.load(sys.stdin)
    for i in d.get('items',[]):
        if nonce in (i.get('text') or '') and i.get('senderID')=='@greenteatree01:beeper.com':
            print('true'); break
    else: print('false')
except: print('false')
" NONCE="$NONCE")
  PATH_A_STATUS=$(printf '{"sent":true,"pendingMessageID":"%s","verified_in_room":%s}' "$PEND" "$VERIFY")
fi

# --- Path B: crdt-connect from a live alice daemon
PORT_OPEN="false"
nc -z -w 3 -G 3 "$HOST" "$PORT" 2>/dev/null && PORT_OPEN="true"

PATH_B_STATUS='{"connected":false,"reason":"port_closed"}'
if [ "$PORT_OPEN" = "true" ]; then
  SOCKS=$(for PID in $(ps -axo pid,comm | grep -E 'emacs(-nox)?$' | awk '{print $1}'); do
    lsof -U -p "$PID" 2>/dev/null | awk '/emacs501/ {gsub(".*emacs501/","",$NF); print $NF}'
  done | sort -u)
  PICK=""
  for S in $SOCKS; do
    R=$(perl -e 'alarm 14; exec @ARGV' "$EC" -s "$S" -e '(progn (ignore-errors (require (quote crdt))) (featurep (quote crdt)))' 2>/dev/null | tr -d '\n')
    if [ "$R" = "t" ]; then PICK="$S"; break; fi
  done
  if [ -n "$PICK" ]; then
    perl -e 'alarm 14; exec @ARGV' "$EC" -s "$PICK" -e '(unless (and (boundp (quote crdt--session-list)) (cl-some (lambda (s) (let ((p (crdt--session-network-process s))) (and (eq (process-status p) (quote open)) (equal (nth 0 (process-contact p)) "100.87.209.11")))) crdt--session-list)) (ignore-errors (crdt-connect "100.87.209.11" 6530)))' >/dev/null 2>&1
    sleep 3
    SUMMARY=$(perl -e 'alarm 14; exec @ARGV' "$EC" -s "$PICK" -e '(let ((sessions crdt--session-list) (shared (cl-remove-if-not (lambda (b) (with-current-buffer b (bound-and-true-p crdt-mode))) (buffer-list)))) (json-encode (list :session_count (length sessions) :buffers (mapcar #'\''buffer-name shared) :first_site_id (when shared (with-current-buffer (car shared) (bound-and-true-p crdt--site-id))))))' 2>/dev/null)
    PATH_B_STATUS=$(printf '{"connected":true,"daemon_socket":"%s",%s' "$PICK" "${SUMMARY#\"\{}")
    PATH_B_STATUS="${PATH_B_STATUS%\"}"
  else
    PATH_B_STATUS='{"connected":false,"reason":"no_crdt_capable_daemon"}'
  fi
fi

ZIGGER_LAST=$(curl -s -m 8 -6 -H "authorization: Bearer $TOKEN" "http://[::1]:23373/v1/chats/${ENC}/messages?limit=30&direction=before" 2>/dev/null | python3 -c "
import json,sys
try:
    d=json.load(sys.stdin)
    for i in d.get('items',[]):
        if i.get('senderID')=='@zigger:beeper.com':
            print(i.get('timestamp','')); break
except: pass" 2>/dev/null)

cat <<JSON
{"ts":"$TS_NOW","nonce":"$NONCE","path_a_matrix":$PATH_A_STATUS,"path_b_crdt":$PATH_B_STATUS,"zigger_last_turn":"$ZIGGER_LAST","port_open":$PORT_OPEN}
JSON
