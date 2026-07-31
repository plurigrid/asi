#!/usr/bin/env bash
# Spawn barton-zigger triad on the most-recent live emacs daemon.
# Verified 2026-04-29. Idempotent. Single Monitor call from cold context.
set -u
EC=/Users/alice/.local/bin/emacsclient
[ -x "$EC" ] || EC=$(ls /nix/store/*emacs-nox-*/bin/emacsclient 2>/dev/null | head -1)
SOCKDIR="$TMPDIR/emacs501"
CAND=""; PID=""
for s in "$SOCKDIR/server" $(ls -t "$SOCKDIR"/fresh-* 2>/dev/null); do
  [ -S "$s" ] || continue
  name=$(basename "$s")
  pong=$(perl -e 'alarm 14; exec @ARGV' "$EC" -s "$name" -e '(emacs-pid)' 2>&1)
  case "$pong" in [0-9]*) CAND="$name"; PID="$pong"; break ;; esac
done
[ -z "$CAND" ] && { echo "no-live-daemon"; exit 1; }
echo "daemon=$CAND pid=$PID"
read -r -d '' SPAWN <<'ELISP'
(progn
  (require 'crdt)
  (let ((trits '((minus . 6540) (ergodic . 6541) (plus . 6542))) (out '()))
    (dolist (p trits)
      (let* ((tag (car p)) (port (cdr p))
             (bufname (format "*barton-zigger-crdt-%s*" tag))
             (netname (format "barton-zigger-crdt-%s.org" tag))
             (already (cl-some (lambda (s)
                                 (let ((np (crdt--session-network-process s)))
                                   (and np (eq (process-status np) 'listen)
                                        (= port (cadr (process-contact np))))))
                               crdt--session-list))
             (buf (get-buffer-create bufname)))
        (with-current-buffer buf
          (unless (eq major-mode 'org-mode) (org-mode))
          (when (= (buffer-size) 0)
            (insert (format "#+TITLE: barton-zigger-crdt %s (port %d)\n* trit\n%s\n" tag port tag))))
        (if already
            (push (list :tag tag :port port :status 'already) out)
          (condition-case err
              (let ((s (crdt-new-session port nil "" "alice" crdt-default-session-permissions)))
                (crdt--share-buffer buf s netname)
                (push (list :tag tag :port port :status 'spawned :site-id (crdt--session-local-id s)) out))
            (error (push (list :tag tag :port port :status 'error :err (error-message-string err)) out))))))
    (nreverse out)))
ELISP
perl -e 'alarm 45; exec @ARGV' "$EC" -s "$CAND" -e "$SPAWN"
echo
for p in 6540 6541 6542; do
  st=$(lsof -nP -iTCP:$p -sTCP:LISTEN 2>/dev/null | tail -n +2 | awk '{print $1, $2}')
  echo "port=$p ${st:-NONE}"
done
