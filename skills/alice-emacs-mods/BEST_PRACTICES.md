# Best Practices — `.sh → .bb` Migration for Emacs Daemon Control

Distilled from the 2026-04-21 `takeover.sh → takeover.bb` rewrite. These are
load-bearing lessons; every one of them cost a wedged daemon or a silent
hang to learn.

## 1. Never call modal Emacs functions from `emacsclient -e`

Daemons have no frame to surface a minibuffer prompt on. Any code path
that can prompt — `find-file` (local variables / recover / symlinks /
large file), `save-buffer` (overwrite), `load-file` (eval-depth) — will
wedge the daemon silently. The client times out, subsequent probes hang.

**Do:** stub the prompt functions before the risky call.

```elisp
(cl-letf (((symbol-function 'y-or-n-p)    (lambda (&rest _) nil))
          ((symbol-function 'yes-or-no-p) (lambda (&rest _) nil)))
  ...)
```

**And** set every known prompt-inducing variable to a permissive value:

```elisp
(let ((inhibit-message t)
      (enable-local-variables :safe)
      (large-file-warning-threshold nil)
      (find-file-suppress-same-file-warnings t)
      (vc-follow-symlinks t)
      (confirm-nonexistent-file-or-buffer nil))
  ...)
```

**And** prefer `find-file-noselect` + `set-window-buffer` over `find-file`
when you only need the buffer, not the interactive visit semantics.

## 2. Always wrap `emacsclient -e` in perl-alarm

`emacsclient` has no `-t`-style timeout. A wedged daemon keeps the socket
open; the client blocks forever. Wrap every call:

```bash
perl -e 'alarm shift; exec @ARGV' 5 emacsclient -s NAME -e FORM
```

In babashka:

```clojure
(p/sh "perl" "-e" "alarm shift; exec @ARGV" (str timeout) "emacsclient" ...)
```

5s is a good default for probes, 20s for heavier ops like window splits.
If the alarm fires, decide: unstick or abort, not retry.

## 3. Gentle unstick, never SIGKILL

User's no-harm-daemon policy: don't `kill -9` on a wedged daemon unless
explicitly authorized per-incident. Instead:

```bash
emacsclient -s NAME -n -e '(ignore-errors (top-level))'
```

`-n` (no-wait) returns immediately; `(top-level)` breaks out of any
recursive edit including minibuffer prompts. Works on the same daemon
that was refusing synchronous calls a moment ago.

## 4. Probe before acting

```bash
emacsclient -s NAME -e '(+ 1 1)'    # expects "2"
```

If this doesn't return "2" in ≤3s, the daemon is either dead or wedged —
different remedies. Dead = restart; wedged = gentle unstick (§3).

## 5. Instrument, don't guess

Silent hangs are the default failure mode with emacsclient chains.
Default to stderr progress logging in any bb script that calls
emacsclient multiple times:

```clojure
(defn log [& xs] (binding [*out* *err*] (apply println "[bb]" xs) (flush)))
```

Call it before each emacsclient invocation. When observing via Monitor,
merge stderr: `cmd 2>&1 | sed -u 's/^/BB: /'`.

## 6. Target the right daemon

`ps -ef | grep '[e]macs.*daemon'` first. Multiple daemons coexist
(factory, server, claude-crdt, horsin-around). Only `server` has a
visible frame the user actually attached to; placing files on a
headless daemon is a no-op from the user's perspective.

**Default to `server`** unless you have a reason to pick another.
See SKILL.md § "Daemon roles" for the matrix.

## 7. The user's visible TUI may not be the daemon you're probing

A standalone `emacs -nw` in a terminal is NOT a daemon — it has no
socket. Verify with `ps` and `lsof -a -U`:

```bash
lsof -a -U -p $(pgrep -f emacs-nox | head -1)
```

If it shows no `/var/folders/.../T/emacs501/*` socket, it's standalone.
Editing via emacsclient against a different daemon will place content
where the user can't see it.

## 8. `p/sh` over `p/process` + `deref`

`babashka.process/sh` waits synchronously with a clear exit code and
stdout string. `p/process` + `deref` with timeout has inconsistent
cancel semantics across bb versions and can leak zombies. If you need
a timeout, use perl-alarm (§2) and `p/sh`, not `deref` with timeout.

## 9. `stat -f '%m %N'` on macOS, `stat -c '%Y %n'` on Linux

The takeover's "find N most recent .org files" step used macOS-specific
`stat -f`. Port check: `stat --version 2>&1 | head -1` tells you which
flavor. If both matter, use `find -printf` on Linux and `stat -f` on
Darwin, switched by `(System/getProperty "os.name")`.

## 10. Behavior-invariant rewrites need a side-by-side test

Before deleting the `.sh`, run both against the same daemon with the
same arguments and compare **observable state**: window count, frame
list, loaded files, color-chain seed. Don't trust "it didn't error" —
trust "the daemon state matches."

For this migration:
- bb: "placed 6 files across 1 frame(s) 6 windows"
- sh: same contract per SKILL.md § "Takeover recipe"
- Seed 0x42D applied in both; `horsin/seed` readable after load.

## 11. Delete only after the user's directive AND after test

User said: "rewrite and replace .sh into .bb invariantly and then get
rid of .sh after teasting". Deletion was gated on BOTH conditions.
Don't short-circuit: the test validates invariance; the directive
authorizes destruction. Either alone is insufficient.

## 12. Update references atomically with the delete

When removing a file, the same commit/operation should update every
doc that names it (SKILL.md, inline comments, upstream README). A
`grep -rn 'takeover\.sh'` pass before commit catches stragglers.
A backup of any edited doc goes in the same dir with a `.bak.<ts>`
suffix — reversible without git.

## 13. The bb self-comment should note the replacement

`takeover.bb` opens with:

```
;; Canonical takeover (replaced takeover.sh 2026-04-21), plus prompt
;; suppression and perl-alarm timeouts.
```

Future readers (including future-you) need to know this replaced
something and when; otherwise the prompt-suppression block looks
paranoid. The 'why' is: it prevents the daemon wedge we actually hit.

---

## Triad closure

Per CLAUDE.md GF(3), this migration engaged:

- **MINUS (-1)**: `spi-parallel-verify` — observable-state diff between sh and bb
- **ERGODIC (0)**: `collaborative-emacs` — daemon as shared substrate
- **PLUS (+1)**: `babashka-clj` — the bb rewrite itself

Σ = 0 ✓

The best-practices above are the frozen trace of that triad's execution.
