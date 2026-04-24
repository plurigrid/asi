---
name: alice-emacs-mods
description: Tour of Alice's heavily-customized terminal Emacs — Causal transients, Worlding org, proof tooling, MLX chat, voice, and clipboard.
metadata:
  trit: 0
---

# Alice's Emacs Mods

Read this BEFORE editing `~/.emacs.d/init.el`, suggesting packages, or
explaining why some keybinding does something unexpected. Most surprises
here are intentional and load-bearing.

## Shape of the install

- **Build**: `emacs-nox 30.2` from Nix store (`/nix/store/...emacs-nox-30.2`)
- **Frontend**: terminal only — no GUI Emacs. Always assume `(display-graphic-p) = nil`
- **Daemons**: typically 2–4 running at once (`factory`, `server`, `claude-crdt`, `horsin-around`, …)
  - `factory` = full init.el (the "real" one)
  - `claude-crdt` / `horsin-around` = `-Q` daemons, started for specific purposes
  - sockets: `/var/folders/.../T/emacs501/<name>`
- **Init**: `~/.emacs.d/init.el` (~700 lines), `~/.emacs.d/early-init.el`
- **Custom code**: `~/.emacs.d/lisp/` (e.g. `org-worlding.el`), `~/.emacs.d/site-lisp/` (whisper.el, chatgpt-shell, shell-maker)
- **Packages**: `package.el` + `use-package` (`use-package-always-ensure t`), MELPA + GNU + nonGNU. `~/.emacs.d/elpa/` ≈ 70 packages
- **No** straight, **no** elpaca, **no** doom, **no** spacemacs

## The dominant pattern: Causal transients on `C-o`

`causal` is a plurigrid fork of `casual-suite` — Transient-based menus
covering most built-in modes plus several additions. The convention:

- `C-o` opens the mode's transient menu in dired, isearch, ibuffer, info,
  calc, bookmarks, agenda, calendar, compile/grep, re-builder, eshell,
  help, man, csv, image, ediff, eww, make, ghostty, gnus (group/summary/
  article/message), portal, proof.
- `M-m` opens transients for elisp-mode, html-mode, css-mode.
- Globally, `C-o` is `causal-editkit-main-tmenu` (the umbrella menu).

Plurigrid additions beyond casual-suite:

| Binding | Menu | What it's for |
|---------|------|---------------|
| `C-c C` | `causal-catcolab-tmenu` | Capture proof → olog export to CatColab |
| `C-c p` | `causal-portal-tmenu` | Post-web proof-theoretic navigation (Narya) |
| `C-c t z` | `causal-timezone-tmenu` | Multi-zone planning |

Other causal modules loaded if present (`require ... nil t`):
`causal-self-walker`, `causal-self-walker-paperproof`, `causal-proof`,
`causal-proofreader`, `causal-ucm`, `causal-xypic`, `causal-notebooklm`,
`sophia-mnemosyne`, `causal-portal`, `causal-gnus`.

If a `C-o` binding doesn't seem to work, the mode probably isn't loaded
yet — Causal uses `with-eval-after-load` everywhere.

## Org subsystem — "worlding," not GTD

- **Each org file declares its own `#+TODO:` states.** There is no global
  GTD configuration. Don't impose one.
- `org-worlding` (custom, in `~/.emacs.d/lisp/org-worlding.el`) supplies
  faces, agenda files, capture templates, keybindings.
- Heading colors are **uniformly** `#7AA2F7` (light blue) across all 8 levels —
  this is intentional via `set-face-attribute` after `org-faces` loads.
- `org-bullets` for pretty bullets, `org-roam` at `~/org-roam/`,
  `org-download` for screenshots/yank to `~/org-images/`.
- `C-c a` agenda, `C-c c` capture, `C-c n …` for org-roam.
- `org-mcp` — exposes org over MCP.

## Email = Gnus over Gmail/Workspace

Configured for `barton@plurigrid.com` via IMAP `imap.gmail.com:993` SSL +
SMTP `smtp.gmail.com:587` STARTTLS. Auth in `~/.authinfo`. Start with
`C-c g`. Gnus dirs all under `~/.emacs.d/gnus/`. Causal-gnus binds `C-o`
in every Gnus mode.

## Lisps / proof tooling

- `paredit`, `rainbow-delimiters`, `magit`, `avy`
- `cider`, `clojure-mode`, `parseclj`, `parseedn`, `sesman` — Clojure
- `hy-mode` — Hy
- `proof-general` + `narya` — Narya is the active proof assistant
- `causal-proof` binds `C-o` in `proof-mode-map`; `causal-portal` binds
  `C-o` in `narya-mode-map` so Narya hops live inside the Portal menu.

## LLMs in the buffer

- `chatgpt-shell` (xenodium) loaded from `~/.emacs.d/site-lisp/chatgpt-shell`
  with `shell-maker` next to it. Uses **local MLX server at
  `http://127.0.0.1:8009`** running `mlx-community/Olmo-3-1125-32B-4bit`
  ("Olmo-3-32B"). Anthropic key from `ANTHROPIC_API_KEY` env. OpenAI
  key falls back to literal `"local"`.
- `agent-shell` + `acp` — Agent Client Protocol.
- `mcp-server-lib`, `org-mcp` — MCP from inside Emacs.

## Voice → text on F9

`whisper.el` (in `~/.emacs.d/site-lisp/`) bound to `F9`:
- `whisper-cli` from flox (NOT auto-installed by whisper.el; `whisper-install-whispercpp = nil`)
- Model: `~/v/ggml-base.en.bin` (base.en)
- macOS mic: `avfoundation :1` (MacBook Pro Mic)
- Inserts at point, no timestamps. Custom `whisper-command` overrides
  the default to point at the flox binary + local model.

## Keyboard

- **Caps Lock → F19 → Meta** (and F7 fallback for terminals that map
  F19→F7). Done via `key-translation-map` + `input-decode-map` so it
  works in both GUI and terminal frames. The user is on a Kinesis
  Advantage 360 + Dvorak.
- Don't suggest remapping Caps Lock — already done.

## Terminal-specific UI

- `xterm-mouse-mode` on (terminal-only block).
- `mouse-1` set point, mouse-4/5 scroll, drag copies region.
- `tab-line-mode` global, terminal styling: black bg / white fg, current
  tab inverted. `C-c <left>`/`C-c <right>` switch tabs.
- Tabs grouped by major-mode (`tab-line-tabs-mode-buffers`).

## Tree-sitter (Emacs 30 builtin)

`treesit-language-source-alist` populated for ~16 languages
(bash, c, cpp, css, go, html, java, js, json, markdown, python, rust, toml,
tsx, typescript, yaml). `M-x install-tree-sitter-grammars` installs all.
`major-mode-remap-alist` sends `*-mode → *-ts-mode`.

## Other notable mods

- **AUCTeX** with `latexmk -pdf` as `TeX-command-default`, RefTeX on,
  `cdlatex` for both LaTeX and Org math. `C-o` in bibtex-mode.
- **ledger-mode** wired to `hledger` (not ledger). Custom reports for
  income statement / balance sheet / cash flow / monthly expenses.
  Files: `*.journal`, `*.ledger`, `*.hledger`. `ob-ledger` for org-babel.
- **undo-tree** with persistent history at `~/.emacs.d/undo-tree-hist/`.
  Auto-save every 100 keys / 30s idle.
- **crdt** loaded — see `collaborative-emacs` skill for the
  Claude-Code ↔ Emacs CRDT setup using socket `claude-crdt` on port 6531.
- **bbdb** (contacts), **bongo** (music), **org-drill** (spaced repetition).
- **clipetty** — system clipboard via OSC 52 from TTY frames. Replaces
  the broken `menu-bar-enable-clipboard` button (which sets `gui-*`
  functions that no-op without a window-system frame). Enabled
  globally via `(after-init . global-clipetty-mode)`.

## Disabled but still present

- **Emacspeak**: commented out due to SwiftMac OGG decode having no
  cache → CPU spin. The `binaural` sound theme is built (see
  `emacspeak-binaural` skill) but the `(load-file ...)` line is
  commented. Re-enable at your own risk.

## Things NOT to do

1. Don't suggest `pbcopy`/`pbpaste` shellouts for clipboard — clipetty
   already handles this via OSC 52, faster + works over SSH.
2. Don't add a global `#+TODO:` config — each org file owns its states.
3. Don't `M-x package-install` an alternative to causal-suite — the
   plurigrid `causal` fork supersedes it and adds modes you'd lose.
4. Don't override `interprogram-cut-function` directly; let
   `global-clipetty-mode` advise it per-frame.
5. Don't try to re-enable Emacspeak without first solving the SwiftMac
   OGG cache issue (it WILL spin a core).
6. Don't assume GUI Emacs — there is none.
7. Don't remove "selected packages" from the customize block at the
   bottom of init.el — they're how `package-autoremove` is governed.

## Quick triage

- Something doesn't bind on `C-o`? Check whether the mode hook fired
  (`with-eval-after-load`) and whether `causal-<mode>` was required.
- "menu-bar-enable-clipboard" button doesn't paste? clipetty must be
  loaded; check `(featurep 'clipetty)` and `global-clipetty-mode`.
- Whisper produces nothing? Check that `whisper-cli` is on PATH (flox
  env active), that `~/v/ggml-base.en.bin` exists, and that
  `avfoundation :1` is the right mic index.
- Caps Lock not Meta? Verify the terminal sends the F19 escape — some
  terminals translate it to F7 instead, both are mapped.
- Org-roam DB out of sync? `M-x org-roam-db-sync`.

## Related skills

- `emacs` — base ecosystem
- `elisp` — language reference
- `emacs-color-chain` — SplitMix64 → faces
- `emacspeak-binaural` — disabled audio theme
- `collaborative-emacs` — CRDT setup using `claude-crdt` daemon
- `xenodium-elisp` — chatgpt-shell / agent-shell
- `proofgeneral-narya` — proof assistant

## Cmd+C → Emacs kill (Ghostty binding)

The user's hard requirement is **Cmd+C in terminal Emacs → macOS pasteboard, Cmd+V anywhere**. The full chain that delivers this:

```
Cmd+C in Ghostty
  → Ghostty keybind sends literal M-w (ESC w) to Emacs
  → Emacs runs kill-ring-save on the marked region
  → clipetty advice fires, emits OSC 52 to terminal
  → Ghostty receives OSC 52 and writes selection to macOS pasteboard
  → Cmd+V anywhere on the Mac pastes the killed text
```

**The Ghostty side** lives in `~/.config/ghostty/config`:

```
keybind = cmd+c=text:\x1bw
```

This OVERRIDES Ghostty's default `Cmd+C = copy_to_clipboard`. Trade-off: you
lose "copy Ghostty's mouse selection on Cmd+C". Workarounds for terminal-text
capture: right-click → Copy, or mouse-drag with `copy-on-select = true`.

**The Emacs side**: clipetty must be loaded and `global-clipetty-mode` on.
Already in init.el; verify with `(featurep 'clipetty)` and `global-clipetty-mode`.

**Workflow**: `C-Space` to set mark → move cursor → **Cmd+C** → text on macOS pasteboard.

### Things that look like clipboard but aren't

- `menu-bar-enable-clipboard` — the "turn on copy paste" menu button. Sets
  `interprogram-cut-function` to `gui-select-text` which is a no-op in TTY
  frames. clipetty bypasses this entirely. Don't trust the button.
- Pressing Cmd+C with no Emacs region marked — sends M-w which kill-ring-saves
  an empty region (warning: "The mark is not active now"). Pasteboard unchanged.
  This isn't a bug; mark a region first.
- Ghostty selection + Cmd+C — no longer copies the terminal selection because
  the keybind override redirects Cmd+C to Emacs. Use right-click menu.

### Reloading Ghostty config

`Cmd+Shift+,` reloads Ghostty config in place. If keybinds don't take effect,
fully quit and relaunch Ghostty.

### Backups

Backup of original Ghostty config saved at `~/.config/ghostty/config.bak.<ts>`
before the Cmd+C override was added (2026-04-19).

## Color strobe (`emacs-strobe-walk` skill)

A separate sibling skill at `~/.claude/skills/emacs-strobe-walk/` that drives
**every face in the frame** from a SplitMix64 chain advanced once per
interaction. Background, foreground, cursor, region, hl-line, mode-line
(active + inactive), fringe, all `font-lock-*` faces, and `org-level-1..8`
get retinted on each tick. Strobing, deterministic, reseedable, throttled
(default 40 ms minimum gap).

**This is what the `horsin-around` daemon already runs** — it was launched
with `-Q -l ~/horsin-around/color-walk.el` (and the canonical copy is in the
skill dir). Default seed is `#x42D` (1069). Commands: `M-x horsin/enable`,
`horsin/disable`, `horsin/reseed`. Variables: `horsin/seed`, `horsin/throttle`.

**Drop into any new daemon:**

```bash
emacs --daemon=NAME -l ~/.claude/skills/emacs-strobe-walk/color-walk.el
# or, into a live one:
emacsclient -s NAME -e '(load-file "~/.claude/skills/emacs-strobe-walk/color-walk.el")'
```

**Hooks installed**: `post-command-hook`, `server-visit-hook`,
`server-after-make-frame-hook`, plus `:after` advice on
`server-eval-and-print` so even `emacsclient -e` ticks the chain.

**Footgun (in the skill, repeating it here): never advise `server-process-filter`** —
it fires on every network byte and deadlocks the daemon. Recovery is `kill -9`.
Also don't call `redraw-display` in the tick; `force-mode-line-update t` is
enough and won't block on a tty frame.

**Composes cleanly with** `emacs-color-chain` (the other SplitMix64 skill —
that one is on-demand single-apply via `C-c g a`; strobe-walk is continuous
auto-tick). Don't enable both at once on the same faces.

### Gay-backed strobe (merged mode)

As of 2026-04-19 there is a bridge file
`~/.claude/skills/emacs-strobe-walk/color-walk-gay.el` that loads both
skills and rewires the strobe's two helpers (`horsin/-sm`, `horsin/-hsl`)
to delegate to `gay--splitmix64` / `gay--hsl-to-hex`. Single source of
truth for the math; strobe provides hooks + face spec, gay provides the
color chain.

**To launch a daemon with merged mode:**

```bash
emacs --daemon=NAME -l ~/.claude/skills/emacs-strobe-walk/color-walk-gay.el
# or hot-load into a running daemon:
emacsclient -s NAME -e '(load-file "~/.claude/skills/emacs-strobe-walk/color-walk-gay.el")'
```

`horsin/seed` and `gay-seed` are mirrored at load time; `horsin/reseed`
is advised to also update `gay-seed`. Reseeding either now retargets
both the strobe trajectory and any on-demand `gay-apply-chain` calls.

**Behavioral identity:** same SplitMix64 constants, same face spec, same
output — this is deduplication, not a visual change.

## Takeover recipe (one-shot)

`takeover.bb` in this skill dir does the whole "I'm sitting down at a
daemon, give me my workspace" routine in a single call. Loading *this*
skill is enough — no need to also load `emacs-strobe-walk` /
`emacs-color-chain` / `tmux` / `org`; the script pulls what it needs.

```bash
~/.claude/skills/alice-emacs-mods/takeover.bb           # server + 6 orgs + 0x42D
~/.claude/skills/alice-emacs-mods/takeover.bb factory   # same for factory daemon
~/.claude/skills/alice-emacs-mods/takeover.bb server 4 0xCAFE
```

What it does, in order:

1. Finds `emacsclient` via `/nix/store/*emacs-nox-*/bin/emacsclient` (with
   PATH / homebrew fallbacks).
2. Probes the daemon using `perl -e 'alarm 3; exec @ARGV'` — never hangs
   on a stale socket (the `factory` socket has bitten us; `claude-crdt`
   and `server` are usually live).
3. Finds N most-recent `.org` files across `~/worlds ~/org ~/org-roam
   ~/.emacs.d` using `stat -f '%m %N'` + `sort -rn` (macOS stat syntax).
4. Splits every frame of the daemon into a **2×3 grid** via
   `split-window … 'below` + `'right`, then `balance-windows`, and
   visits one file per pane in reading order:

   ```
   w1 w4
   w2 w5
   w3 w6
   ```
5. Hot-loads `~/.claude/skills/emacs-strobe-walk/color-walk-gay.el` and
   calls `(horsin/reseed SEED)` **with an explicit seed**. *Gotcha:* after
   the bridge loads, `horsin/reseed` is advised with arity 1 — calling it
   no-arg raises `Wrong number of arguments`. The script catches that
   and falls back to the no-arg form for the plain `color-walk.el` case.

### Daemon roles (matters — don't pick the wrong one)

| Daemon         | What it is                                                        | Good for takeover? |
|----------------|-------------------------------------------------------------------|--------------------|
| `server`       | The real frame the user attaches to with `emacsclient -t -s server` | **yes** (default)  |
| `factory`      | Full `init.el` daemon; may be stale (hung probe)                  | sometimes          |
| `claude-crdt`  | `-Q` headless for CRDT sharing — **no visible frame by default**  | no (placement is invisible) |
| `horsin-around`| `-Q` strobe-only daemon                                           | no                 |

Lesson 2026-04-20: targeting `claude-crdt` placed 6 files on an invisible
frame while the user watched an unrelated `emacs -nw` splash. Always target
`server` unless you have a reason not to.

### Attach

```bash
emacsclient -s server -t      # TTY frame in current terminal
emacsclient -s server -c      # new graphical frame (GUI build only — N/A here)
```


## See also (added by plurigrid-asi-ghostel)
- [[plurigrid-asi-ghostel]] — ghostel (libghostty-vt) substrate for plurigrid/asi agent channels. Replaces make-comint; adds OSC-133 prompt nav, OSC-51;e shell→Emacs bridge, TRAMP-aware remote VT, ghostel-compile.


## See also (added by bob-emacs-mods)
- [[bob-emacs-mods]] — operational complement of alice: ghostel mastery, multi-daemon orchestration, cross-session coordination, REPL-as-citizen, debug/recovery, session-specific team-red params.


## Session cross-refs (2026-04-23, e-session)

This skill participates in the 32-skill working set assembled in /Users/alice/worlds/e session 2026-04-23 (15 new skills also created).

**Outgoing references** (this skill `src` → other skill `dest`):
- `alice-emacs-mods` → `ghostel-imposter-audit` — detects comint imposters in daemon buffer-list
- `alice-emacs-mods` → `horsin-bignum-safe` — fixes Crack #2 bignum seed overflow in horsin/tick
- `alice-emacs-mods` → `ghostel-multi-spawn-safe` — serialized spawn recipe avoids Crack #4 daemon hang
- `alice-emacs-mods` → `narya-pg-clean-reload` — workaround for Crack #1 PG macro collision
- `alice-emacs-mods` → `emacs-session-seed-bridge` — ties $CLAUDE_SESSION_ID into horsin/seed
- `alice-emacs-mods` → `causal-asi-hydra` — wires asi-agenda onto C-c a A alongside Causal C-o

**Incoming references** (other skill `src` → this skill `dest`):
- `plurigrid-asi-ghostel` → `alice-emacs-mods` — host daemon conventions
- `bob-emacs-mods` → `alice-emacs-mods` — host-level defaults; operational layer lives in bob

**Verified GF(3) triads containing this skill:**
- alice-emacs-mods (-1) ⊗ bob-emacs-mods (0) ⊗ plurigrid-asi-ghostel (+1) = 0 ✓
