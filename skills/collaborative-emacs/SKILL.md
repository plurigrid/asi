---
name: collaborative-emacs
description: Claude Code runs an Emacs daemon, starts a CRDT server, shares buffers.
---
# Collaborative Emacs — Claude Code + CRDT Live Editing

**Trit**: 0 (ERGODIC - bidirectional coordination)
**Status**: Working
**Date**: 2026-02-10
**Prerequisite**: crdt.el (elpa), emacsclient

## What This Does

Claude Code runs an Emacs daemon, starts a CRDT server, shares buffers.
User's Emacs auto-connects and sees live edits. No interactive prompts.

## Quick Start (Human Side)

1. **Install crdt.el**
   ```elisp
   ;; Via GNU ELPA
   (use-package crdt)
   ```

2. **Host a session** (on your machine)
   ```
   M-x crdt-share-buffer    ;; share current buffer
   ;; or
   M-x crdt-new-session     ;; start a session, then share buffers into it
   ```
   Prompts for port (default 6530). Binds `0.0.0.0` so Tailscale peers can connect.

3. **Connect from another machine**
   ```
   M-x crdt-connect
   ;; URL: ein://your-machine.tail1234.ts.net:6530
   ;; or:  ein://100.x.y.z:6530
   ```

## Architecture (Preferred)

```
┌──────────────┐    emacsclient -s     ┌──────────────────┐
│  Claude Code │ ──────────────────▶   │  Emacs daemon    │
│  (this CLI)  │                       │  "claude-crdt"   │
└──────────────┘                       │  CRDT SERVER     │
                                       │  port 6531       │
                                       └────────┬─────────┘
                                                │
                                         auto-connect
                                         (crdt-autoconnect.el)
                                                │
                                                ▼
                                       ┌──────────────────┐
                                       │  User's Emacs    │
                                       │  (CRDT client)   │
                                       └──────────────────┘
```

## Setup

### Auto-connect file (already installed)

`~/.emacs.d/crdt-autoconnect.el`:
```elisp
(require 'crdt)
(require 'url-parse)
(run-at-time 3 nil
  (lambda ()
    (condition-case err
        (let ((url (url-generic-parse-url "ein://localhost:6531")))
          (crdt-connect url "alice")
          (message "Connected to Claude CRDT on port 6531"))
      (error (message "CRDT connect failed: %S" err)))))
```

## Usage

### Step 1: Claude starts daemon with CRDT server

```bash
emacs -nw --daemon=claude-crdt

emacsclient -s claude-crdt -e '
(progn
  (require (quote crdt))
  (let ((buf (get-buffer-create "*claude-workspace*")))
    (with-current-buffer buf (org-mode) (insert "#+TITLE: Workspace\n"))
    (crdt-new-session 6531 nil "" "claude"
      (quote (crdt-default-session-permissions)))
    (crdt--share-buffer buf (car crdt--session-list) "workspace.org")))'
```

### Step 2: Claude shares files

```bash
emacsclient -s claude-crdt -e '
(let* ((s (car crdt--session-list))
       (buf (find-file-noselect "/path/to/file.org")))
  (crdt--share-buffer buf s "file.org"))'
```

### Step 3: User launches Emacs and auto-connects

Local:
```bash
emacs -nw -l ~/.emacs.d/crdt-autoconnect.el
```

Over Tailscale (from any node on the tailnet):
```bash
CRDT_HOST=2-monad CRDT_PORT=6531 emacs -nw -l ~/.emacs.d/crdt-autoconnect.el
```

Or by Tailscale IP:
```bash
CRDT_HOST=100.87.209.11 emacs -nw -l ~/.emacs.d/crdt-autoconnect.el
```

3 seconds after startup, connects automatically.
No minibuffer prompts. Then: `M-x crdt-switch-to-buffer`

### Tailscale Notes

The daemon's `crdt-new-session` binds to `0.0.0.0` — accessible
on all interfaces including Tailscale. No extra config needed.

#### crdt.el URL Format (confirmed from upstream docs)

| Protocol | URL | Use |
|----------|-----|-----|
| Unencrypted | `ein://host:port` | Default |
| TLS (stunnel) | `eins://host:port` | Encrypted |

Full Tailscale URLs for `M-x crdt-connect`:
```
ein://2-monad.pirate-dragon.ts.net:6531   # FQDN
ein://2-monad:6531                        # MagicDNS short
ein://100.87.209.11:6531                  # by IP
```

Programmatic connection (no prompts):
```elisp
(crdt-connect (url-generic-parse-url "ein://2-monad.pirate-dragon.ts.net:6531") "alice")
```

`crdt-copy-url` on the server side also generates these `ein://` URLs.

Online tailnet nodes:
- `2-monad` (100.87.209.11) — this machine
- `causality` (100.69.33.107)
- `hatchery` (100.72.249.116)

### Step 4: Claude reads shared buffers

```bash
emacsclient -s claude-crdt -e '
(let* ((s (car crdt--session-list))
       (buf (gethash "BUFFER-NAME" (crdt--session-buffer-table s))))
  (with-current-buffer buf
    (buffer-substring-no-properties (point-min) (point-max))))'
```

### Step 5: Claude writes to shared buffers

```bash
emacsclient -s claude-crdt -e '
(let* ((s (car crdt--session-list))
       (buf (gethash "BUFFER-NAME" (crdt--session-buffer-table s))))
  (with-current-buffer buf
    (goto-char (point-max))
    (insert "\n* New heading from Claude\n")))'
```

## Key Patterns

### Read buffer content
```elisp
(let* ((s (car crdt--session-list))
       (buf (gethash "BUFFER" (crdt--session-buffer-table s))))
  (with-current-buffer buf
    (buffer-substring-no-properties (point-min) (point-max))))
```

### Insert at point-max
```elisp
(with-current-buffer buf
  (goto-char (point-max))
  (insert "text"))
```

### Insert at specific position
```elisp
(with-current-buffer buf
  (goto-char (point-min))
  (search-forward "* Target Heading")
  (end-of-line)
  (insert "\nNew content under heading"))
```

### Run org commands on shared buffer
```elisp
(with-current-buffer buf
  (org-sort-entries nil ?a))  ; sort alphabetically
```

### Check who's connected
```bash
emacsclient -s claude-crdt -e '
(let ((s (car crdt--session-list)))
  (hash-table-keys (crdt--session-user-table s)))'
```

## Critical Lessons

- `crdt-share-buffer` and `crdt-connect` use interactive settings
  buffers — NEVER call them from emacsclient, they block forever
- Use `crdt-new-session` (programmatic) to create server sessions
- Use `crdt--share-buffer` (internal) to add buffers without prompts
- Use `crdt-autoconnect.el` with `url-generic-parse-url` for the
  user's side — fully non-interactive, delayed 3s after init
- Claude daemon hosts the server (port 6531), user is the client
- `emacs --batch` can't maintain CRDT connections (exits immediately)
- Always use `--daemon=claude-crdt` for persistent connection

## Cleanup

```bash
# Kill the daemon when done
emacsclient -s claude-crdt -e '(kill-emacs)'
```

## Related Skills

- `crdt-vterm` — terminal sharing via CRDT + vterm
- `emacs` — base Emacs ecosystem skill
- `elisp` — Emacs Lisp reference
- `emacs-info` — Info navigation
