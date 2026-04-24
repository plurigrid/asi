---
name: bob-emacs-mods
description: Complement to alice-emacs-mods. Covers what alice does not — ghostel mastery, multi-daemon orchestration, cross-session coordination, debug/recovery harness, REPL-as-dynamical-citizen, QRTP distribution, strobe internals, and the hard-won lessons from spawning and debugging live REPLs under the server daemon. Read alongside alice-emacs-mods; together they tile the total Emacs-mod space on this machine.
---

# Bob's Emacs Mods — the other half

Read `alice-emacs-mods` first. That skill covers the *host-level* defaults: build (emacs-nox 30.2 from Nix), daemons (factory/server/claude-crdt/horsin-around), causal transients, org worlding, Gnus, keyboard, clipetty, takeover.bb. Bob covers everything else: the operational layer where live REPLs, cross-session coordination, and debug/recovery actually happen.

## Ghostel mastery (the real one, not the comint imposter)

### The imposter problem
`(make-comint "ghostel: <name>" prog)` yields a buffer named `*ghostel: <name>*` in `comint-mode`. This is **not** a ghostel buffer. It has no VT parsing, no OSC-133, no bridge, no TRAMP, no prompt-awareness. Many skills and my own earlier spawns emit comint imposters. Audit: `(cl-remove-if-not (lambda (b) (and (string-match-p "ghostel" (buffer-name b)) (eq (with-current-buffer b major-mode) 'comint-mode))) (buffer-list))`.

### The correct spawn
```elisp
(require 'ghostel)
(let ((ghostel-shell "/Users/alice/.juliaup/bin/julia")
      (ghostel-buffer-name "*ghostel: julia-real*"))
  (ghostel))
```
Buffer comes up in `ghostel-mode`, parses VT through `ghostel-module.dylib` (Zig, libghostty-vt). Everything downstream — strobe, prompt nav, bridge, OSC-52, TRAMP — starts working.

### Parallel-spawn hazard
Spawning ≥2 ghostel buffers that each launch a heavy REPL (julia, stack ghci) in the same redisplay frame **hangs the daemon**. The Zig module's VT parser is not reentrant against concurrent PTY floods. Julia's startup banner alone is ~100 KB of escape sequences per pane. Three parallel spawns = instant hang (observed twice in the session).

### Safe multi-spawn recipe
1. **Wrap shells with quiet flags** via a trivial script. `~/bin/julia-quiet`:
   ```sh
   #!/bin/sh
   exec /Users/alice/.juliaup/bin/julia --color=no --banner=no "$@"
   ```
2. **Serialize** spawns + poll for prompt between each:
   ```elisp
   (defun bob/ghostel-spawn-wait (name shell &optional timeout)
     (let ((ghostel-shell shell)
           (ghostel-buffer-name (format "*ghostel: %s*" name))
           (deadline (+ (float-time) (or timeout 15))))
       (unless (get-buffer ghostel-buffer-name) (ghostel))
       (while (and (< (float-time) deadline)
                   (not (with-current-buffer ghostel-buffer-name
                          (save-excursion
                            (goto-char (point-max))
                            (forward-line -1)
                            (looking-at ".*\\(julia\\|> \\|λ>\\) *$")))))
         (sit-for 0.2))
       ghostel-buffer-name))
   ```
3. **Throttle during the multi-spawn window**:
   ```elisp
   (let ((ghostel-timer-delay 0.1)
         (ghostel-immediate-redraw-threshold 4096)
         (ghostel-input-coalesce-delay 0.05))
     (bob/ghostel-spawn-wait "sd-minus"   "/Users/alice/bin/julia-quiet")
     (sit-for 2)
     (bob/ghostel-spawn-wait "sd-ergodic" "/Users/alice/bin/julia-quiet")
     (sit-for 2)
     (bob/ghostel-spawn-wait "sd-plus"    "/Users/alice/bin/julia-quiet"))
   ```

### Nuclear fallback — one daemon per tree
When the single-daemon pattern can't be made safe, fork per trit:
```sh
emacs --daemon=sd-minus   -l ~/.claude/skills/emacs-strobe-walk/color-walk-gay.el
emacs --daemon=sd-ergodic -l ~/.claude/skills/emacs-strobe-walk/color-walk-gay.el
emacs --daemon=sd-plus    -l ~/.claude/skills/emacs-strobe-walk/color-walk-gay.el
```
No shared VT parser. Cost: three frames. Win: true triadic parallelism, one GF(3) component per daemon. `emacsclient -s sd-minus -t` to attach.

## Ghostel feature table (what alice doesn't cover)

| Feature | Knob | Value / notes |
|---|---|---|
| VT render rate | `ghostel-timer-delay` | 0.033 → 30 fps (lower for multi-spawn) |
| Adaptive FPS | `ghostel-adaptive-fps` | t (idle buffers idle the timer) |
| Big-chunk bypass | `ghostel-immediate-redraw-threshold` | 256 chars default; raise to 4 KB during spawn |
| Input batching | `ghostel-input-coalesce-delay` | 3 ms default |
| Scrollback cap | `ghostel-max-scrollback` | 5 MB; raise to 64 MB for long-lived REPLs |
| Shell → Emacs bridge | `ghostel-eval-cmds` | defaults: find-file, find-file-other-window, dired, dired-other-window, message |
| Prompt nav hooks | `ghostel-command-{start,finish}-functions` | empty until shell sources `etc/ghostel.{zsh,bash,fish}` |
| SSH terminfo | `ghostel-ssh-install-terminfo` | `'auto` |
| TRAMP shells | `ghostel-tramp-shells` | per-host shell mapping |
| Compile mode | `M-x ghostel-compile` | replacement for `M-x compile`, full VT |
| Eshell bridge | load `ghostel-eshell` | eshell inside a ghostel buffer |

### Extend the bridge for this session
```elisp
(dolist (pair '(("gay-reseed"     horsin/reseed)
                ("gay-strobe-on"  horsin/enable)
                ("gay-strobe-off" horsin/disable)
                ("delta-append"   (lambda (text) (append-to-file text nil "~/worlds/e/2026-04-21-delta.org")))))
  (add-to-list 'ghostel-eval-cmds pair))
```
From any shell inside a ghostel buffer: `printf '\e]51;e;gay-reseed;305419896\a'` reseeds the strobe. No socket, no RPC, the VT stream *is* the control channel.

## Known Emacs-daemon cracks (observed this session)

### Crack 1: `proof-easy-config: PG already in use or name/symbol mismatch`
After `(require 'proof-general)`, narya.el's own `(proof-ready-for-assistant 'narya)` fails the macro's name-check and `define-derived-mode narya-mode` never lands. Workaround: set `narya-toolbar-entries` to nil *before* loading (handles one error) and either load narya *before* any other PG assistant OR do `(unload-feature 'proof-general t)` first. Escape valve: use `coq-mode` + a `.v` file — PG bindings work fine there.

### Crack 2: `wrong-type-argument integerp (HI . LO)` in horsin/tick
The strobe chain uses `logand (+ seed golden) mask` where seed can be a bignum. On Emacs 30.2 + aarch64, some path returns a `(hi . lo)` *cons pair* instead of a bignum integer, which `logand` can't handle. Observed every time `horsin/seed` exceeds fixnum range and the tick advances. Workaround: `(setq horsin/seed (logand (or (and (consp horsin/seed) (logior (ash (car horsin/seed) 64) (cdr horsin/seed))) horsin/seed) #xFFFFFFFFFFFFFFFF))` as a coerce-on-read.

### Crack 3: sequential narrow-terminal window splits silently drop panes
`(dotimes (_ 4) (split-window-right))` on a 120-col terminal silently fails after ~3 splits — Emacs reports "Window too small for splitting" only when the fifth split is attempted directly, not inside `dotimes`. Always check `(length (window-list))` after a split burst and fall back to vertical layout if short.

### Crack 4: daemon hang on multi-ghostel spawn
Symptom: `emacsclient -s server -e '(+ 1 2)'` → SIGALRM after 3-5 s. Cause: see "Parallel-spawn hazard" above. Recovery: `C-g` in the user's live Emacs frame. No emacsclient-side recovery exists (all `-e` calls queue behind the hung VT parser).

## Cross-session coordination (the L6 layer alice doesn't discuss)

The user routinely runs 4+ Claude Code sessions in parallel Ghostty tabs (⌘1–⌘4). These sessions share only:
- `/worlds/*` filesystem
- `~/.claude/skills/` (shared skill library)
- `~/.claude/projects/-Users-alice-worlds-*/memory/` (per-project memory dirs)
- the single Emacs daemon (PID 1831, `server` socket)

They do **not** share:
- conversation transcript (each session has its own `/tmp/claude-501/<uuid>/`)
- Monitor task outputs (same; each session's `tasks/*.output` is isolated)
- a messaging inbox

### Shared-state rendezvous patterns that work
- **Memory entries** under `~/.claude/projects/-Users-alice-worlds-e/memory/MEMORY.md` — indexed, one-line hooks. Multiple sessions can read + append (last-writer-wins, but entries are append-only by convention).
- **DuckDB on disk** — `/worlds/e/broadcast_e.duckdb` and `/worlds/i/ies_beeper.duckdb` are written by one session, queried by another. Tables like `barton_ies_messages` are durable rendezvous points.
- **Org buffers shared via the Emacs daemon** — all sessions driving `server` see the same `*ghostel: …*` buffers. Two sessions editing the same buffer is safe as long as only one writes to a given region (CRDT is optional; last-writer-wins OK for ephemeral).

### Anti-patterns observed
- Trying to SIGINT another session's Claude Code process → no cross-session permission.
- Polling `/tmp/claude-501/*/tasks/*.output` for another session's progress → works but slow; use a DuckDB table instead.

## REPL as dynamical citizen

Long-lived REPLs in ghostel buffers are not tools — they're citizens with state. Observed in this session:
- `*ghostel: nanoclj-zig*` retained seed-split hex history across multiple parallel agents.
- `*ghostel: julia-gay*` retained `gay_seed!(0xd8dbb2df5c81869c)` from one agent's earlier run.
- `*ghostel: duckdb*` on `broadcast_e.duckdb` holds the result cache across queries.

Implication: **source-verify before every REPL call** (established in prior memory) AND **state-verify** — read the prompt history's tail, don't assume a fresh REPL. Pattern:
```elisp
(defun bob/repl-tail (buf &optional n)
  (with-current-buffer buf
    (buffer-substring-no-properties
      (max (point-min) (- (point-max) (or n 800)))
      (point-max))))
```

## Team-red canonical parameters (this session's gauge)

- minus seed: `0x144d8132a6e983f5`  (validator / `-.tree`)
- ergodic seed: `0xa4dd4adf1c71e889` (coordinator / `0.tree`)
- plus seed: `0x4fd68f19a3c21491`  (generator / `+.tree`)
- pleasant-red locus: `LCH(55.5, 139.9, 12.4)` ≈ `#f34240`
- 3-MATCH triad: ghci (−1) ⊗ nanoclj-zig (0) ⊗ julia-gay (+1) = 0 ✓

Reseed the strobe:
```elisp
(horsin/reseed #x144d8132a6e983f5)
```
(note crack 2 — coerce the seed first if it's a bignum cons).

## The numeric horizons of the three REPL languages

| REPL | Native int | Max exact | Above that |
|---|---|---|---|
| GHCi | Word64 | 2^63−1 | bignum `Integer` |
| Julia | Int64 / UInt64 | 2^63−1 / 2^64−1 | `BigInt` on demand |
| nanoclj-zig | double (Int53) | 2^53−1 ≈ 9e15 | **literal rejected**: "invalid number" |

Implication for cross-REPL seeds: if the seed exceeds 2^53−1, **split into 32-bit hi/lo halves** and run paired SplitMix32. Reference code: `/worlds/e/sm32-split.cljc`. See memory `repl_numeric_horizons_2026_04_22.md`.

## Canonical Gay.jl path

Four directories claim the name "Gay.jl" with TWO distinct UUIDs:
- `/worlds/g/Gay.jl` — **CANONICAL** — UUID `f3dee6b2-1ce2-4cc9-bfb1-25e98f6f315b`, v0.3.0 (newest, richest src tree)
- `/worlds/g/Gay.jl_1` — sibling copy, same HEAD
- `/worlds/g/Gay.jl_2` — older snapshot (v0.2.1)
- `/worlds/e/exo__home1/exo/Gay.jl` — **DIFFERENT PACKAGE** (UUID `a8c5b8e4…`, v0.1.0) — do not load by accident

Global autoload already installed at `~/.julia/config/startup.jl`; takes effect for every future Julia REPL via `atreplinit`. See memory `canonical_gay_jl.md`.

## Layout patterns & their tradeoffs

| Grid | Use when | Gotchas |
|---|---|---|
| 1×3 horizontal | 3 REPLs, wide terminal | `split-window-right` ×2; narrow cols on small screens |
| 1×4 / 1×5 horizontal | 4–5 panes, wide | `Window too small for splitting` on < 160 col |
| 2×3 grid | 6 panes, balanced | need ≥ 120 col × 30 rows |
| 4×2 grid (tall) | 8 panes, narrow terminal | vertical-dominant; fall back if 2×4 horizontal fails |
| 3×1 vertical | 3 panes, narrow | each pane very short (7-8 rows) |

Always check `(length (window-list))` after splits; fall back on failure.

## QRTP distribution of a session

Full bundle template at `/worlds/e/ghostty-emacs-combo/`. Pack: `scripts/pack.bb` → `frames/*.png`. Play: `scripts/play.sh` at 8 fps. Receiver: `scripts/unpack.sh` via `zbarcam`. See README.org in that dir. ~228 KB bundle ≈ 395 frames ≈ 50 s / loop.

## bb-native MCP server template

When a skill wants an MCP server without Node/TypeScript, use `/worlds/e/bb-mcp.bb` (95 lines, pure babashka). Replaces a 40-file TypeScript babashka-mcp-server. Register in `~/.mcp.json` with stdio transport.

## Debug harness

Proposed but not yet scaffolded (TODO):
- `debug/scan-sessions.sh` — inventory all `/tmp/claude-501/*/tasks/` + last 5 outputs
- `debug/emacs-health.el` — `M-x bob/health` prints daemon-PID, seed, tick, layout, messages-tail
- `debug/shared-inbox/` — `fswatch`-triggered cross-session messaging
- `debug/pg-snapshot.el` — dump PG locked/processing offsets per `.v` buffer

## Things NOT to do (session-observed)

1. Don't `(julia-snail)` on a fresh project without killing PG state first — `proof-easy-config` collides with narya.el's init (see Crack 1).
2. Don't spawn ≥2 ghostel buffers in the same redisplay frame unless banner-silenced AND throttled.
3. Don't call `vterm-send-string` — we're in comint/ghostel land. Use `process-send-string (get-buffer-process BUF) STR`.
4. Don't assume a ghostel-prefixed buffer is in ghostel-mode. Grep `major-mode` first.
5. Don't use fish-shell `for` loops in Monitor scripts — they don't word-split `$VAR`. Use `bash -c '…'` explicitly OR inline values.
6. Don't `Pkg.add` in a ghostel pane *before* the prompt is visible — the resolver progress flood blocks the VT parser.
7. Don't assume the Emacs "daemon" is a daemon — on this machine it's `emacs -nw` (PID 1831) running interactively in a TTY that happens to host the `server` socket. `C-g` at the user's frame is the canonical recovery.

## Quick triage

| Symptom | Probe | Fix |
|---|---|---|
| `emacsclient -s server -e '(+ 1 2)'` → SIGALRM | daemon hung | user C-g |
| `*ghostel:…*` in comint-mode | comint imposter | kill + respawn with `(ghostel)` |
| horsin tick error `(HI . LO)` | seed overflow to cons | coerce with mask |
| narya-mode doesn't activate | PG macro collision | setq `narya-toolbar-entries`, then `unload-feature 'proof-general` |
| REPL pane tripled | narrow-terminal split collapse | fall back to vertical layout |
| shell commands in ghostel don't trigger OSC-133 | shell rc hasn't sourced `etc/ghostel.zsh` | source it |

## Session-specific memory hooks

- `memory/delta_2026_04_21.md` — team-red ladder + 3-MATCH triad + source-verify discipline + open-games verdict
- `memory/repl_numeric_horizons_2026_04_22.md` — three REPLs, three ints, canonical
- `memory/canonical_gay_jl.md` — Gay.jl path disambiguation (f3dee6b2 = canonical)
- `memory/team_red_locus.md` — LCH(55, 138, 12) locus, #f34240
- canonical Beeper archive: `/Users/alice/Library/Application Support/BeeperTexts/account.db` (352 MB) + `/worlds/i/ies_beeper.duckdb` (478 MB, pre-processed IES slice)

## GF(3) triadic composition

```
alice-emacs-mods (-1)   ⊗  bob-emacs-mods (0)  ⊗  plurigrid-asi-ghostel (+1)  = 0  ✓
```
Alice anchors the host (validator of the install). Bob coordinates the live operation (ergodic). Plurigrid-asi-ghostel generates the substrate for new REPL/agent channels. The three together tile the Emacs-mod space.

## See also (bidirectional)

- [[alice-emacs-mods]] — host-level defaults; read first
- [[plurigrid-asi-ghostel]] — ghostel substrate for agent channels
- [[ghostel]] — the underlying terminal
- [[emacs-strobe-walk]] — horsin/color-walk; target of the bignum coerce workaround
- [[proofgeneral-narya]] — Narya PG integration; source of Crack 1
- [[three-match]] — the 3-MATCH triadic framework we instantiate on REPLs
- [[emacs-color-chain]] — sibling strobe skill
- [[julia-gay]] / [[clojure]] — language content layers
- [[bumpus-narratives]] / [[open-games]] — proof-target formalizations with open cracks


## Session cross-refs (2026-04-23, e-session)

This skill participates in the 32-skill working set assembled in /Users/alice/worlds/e session 2026-04-23 (15 new skills also created).

**Outgoing references** (this skill `src` → other skill `dest`):
- `bob-emacs-mods` → `plurigrid-asi-ghostel` — VT substrate (named ghostel-vt in ghostel-rooms)
- `bob-emacs-mods` → `three-match` — 3-MATCH framework bob's session instantiates
- `bob-emacs-mods` → `bumpus-narratives` — proof-target sheaf substrate
- `bob-emacs-mods` → `open-games` — proof-target formalization with open cracks
- `bob-emacs-mods` → `emacs-strobe-walk` — target of bignum-safe patch
- `bob-emacs-mods` → `proofgeneral-narya` — Crack #1 source skill
- `bob-emacs-mods` → `ies-triadic` — 3-MATCH triad instantiated in ghci/nanoclj/julia-gay
- `bob-emacs-mods` → `horsin-bignum-safe` — implements the Crack #2 workaround bob documents
- `bob-emacs-mods` → `ghostel-imposter-audit` — implements the imposter audit bob requests
- `bob-emacs-mods` → `ghostel-multi-spawn-safe` — implements bob's safe-multi-spawn recipe
- `bob-emacs-mods` → `three-repl-triad` — codifies bob's canonical team-red triad seeds

**Incoming references** (other skill `src` → this skill `dest`):
- `alice-emacs-mods` → `bob-emacs-mods` — operational complement to alice host-level
- `plurigrid-asi-ghostel` → `bob-emacs-mods` — ghostel mastery and multi-daemon orchestration

**Verified GF(3) triads containing this skill:**
- alice-emacs-mods (-1) ⊗ bob-emacs-mods (0) ⊗ plurigrid-asi-ghostel (+1) = 0 ✓


## REPL atlas

Part of: `repl-commons`. Family canonical: `emacs`.
