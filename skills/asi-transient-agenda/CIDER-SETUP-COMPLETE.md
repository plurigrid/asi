# ASI Transient Agenda + CIDER Setup: Complete

**Date**: 2026-02-05
**Status**: ✅ All systems operational
**Babashka nREPL**: Listening on localhost:1667
**Emacs**: Connected and monitoring via Vigilant CIDER

## System Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                     EMACS (Ghostty terminal)                     │
├─────────────────────────────────────────────────────────────────┤
│  C-c a          → ASI Agenda hydra (repos, skills, Julia, etc)  │
│  C-c k          → Kaleidoscope color controller (24-color)      │
│  C-c C-x j j    → CIDER jack-in or cider-connect                │
│  M-x cider...   → Full CIDER REPL control suite                 │
└─────────────────────────────────────────────────────────────────┘
         ↓ 24-bit direct-color terminal + SGR mouse + focus
┌─────────────────────────────────────────────────────────────────┐
│          Terminal Features (asi-terminal-fix.el)                │
├─────────────────────────────────────────────────────────────────┤
│  ✅ 24-bit RGB direct-color (no 256-color approximation)        │
│  ✅ xterm-mouse-mode: full mouse event tracking                 │
│  ✅ SGR mouse mode 1006: extended coordinates (>223 cols)       │
│  ✅ Button tracking mode 1002: mouse drag detection             │
│  ✅ Focus events mode 1004: FocusIn/FocusOut                    │
│  ✅ Pixel scroll precision: smooth scrolling                    │
└─────────────────────────────────────────────────────────────────┘
         ↓ color-aware face updates
┌─────────────────────────────────────────────────────────────────┐
│       Appearance Control (asi-kaleidoscope.el + colors)         │
├─────────────────────────────────────────────────────────────────┤
│  Mode-line:      Current color from 24-color palette            │
│  Header-line:    Complement (180° hue rotation)                 │
│  Fringe:         Preceding color (palette[idx-1])               │
│  Cursor:         Complement foreground                          │
│  Minibuffer:     Next color (palette[idx+1])                    │
│  Region:         Lightened current color                        │
│  Animation:      0.8s cycle, 24 colors, golden-angle derived    │
└─────────────────────────────────────────────────────────────────┘
         ↓ nREPL socket connection (TLS-ready)
┌─────────────────────────────────────────────────────────────────┐
│   Vigilant CIDER (asi-vigilant-cider.el) Security Layer         │
├─────────────────────────────────────────────────────────────────┤
│  🛡️  Layer 1: Non-localhost hijack detection                    │
│      └─ Only 127.0.0.1, localhost, ::1 allowed                  │
│      └─ Verified ports: {1667}                                  │
│      └─ Blocks + counts hijack attempts (alert at 3+)           │
│                                                                 │
│  🛡️  Layer 2: Eval source boundary crossing                    │
│      └─ Tracks source file for each eval                        │
│      └─ Detects code injection across file boundaries           │
│      └─ Logs suspicious evals to audit log                      │
│                                                                 │
│  🛡️  Layer 3: Socket integrity monitoring                      │
│      └─ Monitors nREPL send/recv operations                     │
│      └─ Alerts on >100KB writes (buffer overflow detection)    │
│      └─ Tracks message hashes (MD5) for anomaly detection       │
│                                                                 │
│  🛡️  Layer 4: Sentinel process (continuous)                   │
│      └─ Runs every 5s in background                            │
│      └─ Verifies nREPL process still alive + connected         │
│      └─ Detects process swapping (endpoint substitution)        │
│      └─ Kills hijacked REPL buffers automatically              │
│                                                                 │
│  📊 Audit Log: M-x asi-vigilant-show-audit-log                 │
│      └─ Org-mode table: timestamps, event types, details        │
│      └─ Stored in `asi-vigilant--audit-log` list               │
│      └─ Inspect with: asi-vigilant-enable/disable              │
└─────────────────────────────────────────────────────────────────┘
         ↓ nREPL protocol (bencode + sockets)
┌─────────────────────────────────────────────────────────────────┐
│              Babashka nREPL Server (Port 1667)                  │
├─────────────────────────────────────────────────────────────────┤
│  $ bb --nrepl-server 1667                                       │
│  PID: [running]                                                 │
│  Listening: TCP 127.0.0.1:1667 (IPv6 dual-stack)              │
│  Connection state: ESTABLISHED (from emacs PID 7767)            │
│  Protocol version: bencode (nREPL 1.3.1)                       │
│  Ops: eval, load-file, describe, complete, etc                │
└─────────────────────────────────────────────────────────────────┘
```

## File Locations

### Core Elisp Skills
```
/Users/bob/i/asi/skills/asi-transient-agenda/
├── SKILL.md                      # Skill specification (nbb/squint architecture)
├── CIDER-BEST-PRACTICES.md       # This guide + troubleshooting
├── CIDER-SETUP-COMPLETE.md       # System architecture (this file)
│
├── asi-gay-colors.el             # Gay.jl 24-color generation hydra
├── asi-terminal-fix.el           # 24-bit terminal + xterm-mouse setup
├── asi-kaleidoscope.el           # Oscillating color animation (mode-line, header, etc)
├── asi-vigilant-cider.el         # nREPL hijack detection + security monitoring
│
├── repo-index.cljs               # nbb script: fetch 400 plurigrid repos via gh API
├── skill-scanner.cljs            # nbb script: scan 616 skills from /Users/bob/i/asi/skills/
└── agenda-render.cljs            # nbb script: compose hydra, push to Emacs via emacsclient
```

### Runtime Data
```
/tmp/
├── asi-agenda-init.el            # Generated hydra (loaded via C-c a)
└── [color_buffers]               # Transient color output from Julia REPL
```

### External Dependencies
```
Julia environment:
  ├── TulipaEnergyModel.jl v0.19.1 (energy systems optimization)
  ├── Gay.jl v1.12.213 (deterministic splittable RNG + colors)
  └── [other packages]

Babashka:
  ├── nREPL 1.3.1 (network REPL protocol)
  └── [bundled libraries]

Emacs packages:
  ├── CIDER 1.20+ (Clojure IDE)
  ├── cider-nrepl 0.49+ (middleware)
  ├── hydra (key bindings + menus)
  ├── magit (git operations)
  └── [standard Emacs packages]
```

## Quick Start

### 1. Start Babashka nREPL (if not running)
```bash
bb --nrepl-server 1667 &
```

### 2. Open Emacs + Load Skills
```elisp
;; In running Emacs:
(load-file "/Users/bob/i/asi/skills/asi-transient-agenda/asi-terminal-fix.el")
(load-file "/Users/bob/i/asi/skills/asi-transient-agenda/asi-kaleidoscope.el")
(load-file "/Users/bob/i/asi/skills/asi-transient-agenda/asi-gay-colors.el")
(load-file "/Users/bob/i/asi/skills/asi-transient-agenda/asi-vigilant-cider.el")
```

**Or via emacsclient** (single command):
```bash
emacsclient --eval "(load-file \"/Users/bob/i/asi/skills/asi-transient-agenda/asi-terminal-fix.el\")" \
            --eval "(load-file \"/Users/bob/i/asi/skills/asi-transient-agenda/asi-kaleidoscope.el\")" \
            --eval "(load-file \"/Users/bob/i/asi/skills/asi-transient-agenda/asi-gay-colors.el\")" \
            --eval "(load-file \"/Users/bob/i/asi/skills/asi-transient-agenda/asi-vigilant-cider.el\")"
```

### 3. Start Kaleidoscope Animation
```elisp
M-x asi-kaleidoscope-start
```

### 4. Connect CIDER to Babashka
```elisp
M-x cider-connect
# Prompts: Host = "localhost", Port = 1667
# Or: (cider-connect-clj '(:host "localhost" :port 1667))
```

### 5. Monitor Security
```elisp
M-x asi-vigilant-enable
M-x asi-vigilant-show-audit-log  ;; View security events
```

### 6. Open Agenda/Hydra
```elisp
C-c a   # Main agenda (repos, skills, Julia, DuckDB, colors, kaleidoscope, etc)
C-c k   # Kaleidoscope controller (start/stop/speed)
```

## Color Palette (Gay.jl seed=1069, 24-color genesis)

| Idx | Color | RGB | HSL |
|-----|-------|-----|-----|
| 0 | #769c7d | (118, 156, 125) | 133°, 18%, 54% |
| 1 | #55b0e6 | (85, 176, 230) | 207°, 70%, 62% |
| 2 | #c8a0c2 | (200, 160, 194) | 310°, 30%, 71% |
| 3 | #ffa6c2 | (255, 166, 194) | 346°, 100%, 82% |
| 4 | #789a20 | (120, 154, 32) | 78°, 66%, 36% |
| 5 | #54c1ed | (84, 193, 237) | 196°, 82%, 63% |
| 6 | #285dd0 | (40, 93, 208) | 225°, 81%, 49% |
| 7 | #6233ef | (98, 51, 239) | 260°, 92%, 57% |
| 8 | #d4be57 | (212, 190, 87) | 49°, 64%, 59% |
| 9 | #389bc3 | (56, 155, 195) | 199°, 56%, 49% |
| 10 | #7278c0 | (114, 120, 192) | 237°, 43%, 60% |
| 11 | #5fa42b | (95, 164, 43) | 91°, 59%, 41% |
| 12 | #c3f7fa | (195, 247, 250) | 190°, 85%, 87% |
| 13 | #de1fbe | (222, 31, 190) | 310°, 79%, 49% |
| 14 | #ec6698 | (236, 102, 152) | 345°, 77%, 66% |
| 15 | #b81660 | (184, 22, 96) | 330°, 79%, 40% |
| 16 | #49b0f2 | (73, 176, 242) | 207°, 88%, 62% |
| 17 | #50a9e3 | (80, 169, 227) | 206°, 76%, 60% |
| 18 | #6fc6f9 | (111, 198, 249) | 204°, 94%, 70% |
| 19 | #7d13cb | (125, 19, 203) | 276°, 82%, 43% |
| 20 | #5fb501 | (95, 181, 1) | 93°, 98%, 36% |
| 21 | #636fa4 | (99, 111, 164) | 230°, 25%, 52% |
| 22 | #5b63de | (91, 99, 222) | 236°, 71%, 61% |
| 23 | #58e0a8 | (88, 224, 168) | 160°, 73%, 61% |

**Golden-angle spacing**: Indices tiled for maximum perceptual distance between adjacent positions.

## Commands Summary

### Agenda & Control
| Binding | Command | Purpose |
|---------|---------|---------|
| C-c a | asi-agenda/body | Main agenda hydra |
| C-c k | asi-kaleidoscope-hydra/body | Kaleidoscope controller |
| C-c a c | asi-agenda-colors | Gay.jl color generation |
| C-c a j | asi-agenda-julia | Julia REPL control |
| C-c a d | asi-agenda-duckdb | DuckDB shell |

### Kaleidoscope Control
| Binding | Command | Purpose |
|---------|---------|---------|
| k | asi-kaleidoscope-start | Start animation at 0.8s cycle |
| s | asi-kaleidoscope-stop | Freeze colors |
| n | asi-kaleidoscope-step | Advance one step |
| + | asi-kaleidoscope-faster | Decrease cycle time by 0.1s |
| - | asi-kaleidoscope-slower | Increase cycle time by 0.2s |

### CIDER Control
| Binding | Command | Purpose |
|---------|---------|---------|
| C-c C-x j j | cider-jack-in | Start REPL (auto-injects middleware) |
| M-x cider-connect | Manual connection | Connect to existing nREPL |
| C-c C-k | cider-eval-buffer | Eval buffer |
| C-c C-r | cider-eval-region | Eval region |
| C-x C-e | cider-eval-last-sexp | Eval last sexp |
| C-c M-n r | cider-ns-refresh | Reload namespace |

### Vigilant CIDER
| Command | Purpose |
|---------|---------|
| M-x asi-vigilant-enable | Start monitoring |
| M-x asi-vigilant-disable | Stop monitoring |
| M-x asi-vigilant-show-audit-log | View security events |

## Configuration

### Trusted Hosts (vigilant-cider.el line 15)
```elisp
(defvar asi-vigilant--trusted-hosts '("127.0.0.1" "localhost" "::1")
  "List of trusted nREPL host addresses.")
```

### Verified Ports (vigilant-cider.el line 18)
```elisp
(defvar asi-vigilant--verified-ports '(1667)
  "List of verified/expected nREPL ports.")
```

### Kaleidoscope Speed (asi-kaleidoscope.el line 19)
```elisp
(defvar asi-k--speed 0.8 "Seconds between color transitions.")
```

## Testing the Setup

### 1. Verify Terminal Features
```elisp
M-x asi-color-test
# Should show 12 color swatches with exact hex values (not approximated)
```

### 2. Test Kaleidoscope
```elisp
M-x asi-kaleidoscope-start
# Mode-line should cycle through 24 colors at 0.8s intervals
# Header-line should show complement colors
# Watch for at least 3 cycles
M-x asi-kaleidoscope-stop
```

### 3. Verify CIDER Connection
```elisp
M-x cider-connect
# Host: localhost
# Port: 1667
# Wait for: *cider-repl babashka* buffer
# Type: (+ 1 2)
# Should see: => 3
```

### 4. Test Vigilant CIDER Security
```elisp
M-x asi-vigilant-show-audit-log
# Should show: connection-check entry with status "SAFE"
# Verify: host = "localhost", port = 1667
```

### 5. Eval with Boundary Tracking
```clojure
;; In *cider-repl babashka*:
(+ 1 2)
;; In clojure source file:
(let [x 1 y 2] (+ x y))
C-c C-e  ;; Uses asi-cider-eval-region-safe (with vigilance)
;; Should eval successfully + record source file in audit log
```

## Troubleshooting

### "nREPL connection lost"
```bash
# Check if babashka is still listening:
lsof -i :1667

# If not, restart:
bb --nrepl-server 1667 &

# Then reconnect in Emacs:
M-x cider-connect
```

### "Hijack Alert" in vigilant CIDER
- Check: Port 1667 is listening (`lsof -i :1667`)
- Check: Using localhost not remote IP (`host` must be "localhost" or "127.0.0.1")
- Check: Port is verified in `asi-vigilant--verified-ports`

### Kaleidoscope not animating
```elisp
M-x asi-kaleidoscope-start
# If no animation, check timer: (symbol-value 'asi-k--timer)
# Restart: M-x asi-kaleidoscope-stop, then M-x asi-kaleidoscope-start
```

### Colors appear approximated (not exact hex)
```elisp
M-x asi-color-test
# If colors look wrong, terminal is not using 24-bit mode
# Reload: (load-file "/Users/bob/i/asi/skills/asi-transient-agenda/asi-terminal-fix.el")
# Verify: (display-color-cells) should be >= 16777216
```

## Next Steps

### Recommended Exploration
1. **Julia integration**: Load TulipaEnergyModel via Julia REPL, use Gay.jl for color-coded results
2. **DuckDB analytics**: Use `C-c a d` to open DuckDB, query Clojure metrics
3. **Repo indexing**: Use `C-c a r` to browse 400 plurigrid repos, jump to interesting projects
4. **Skill orchestration**: Use `C-c a s` to explore 616 ASI skills, load related triads

### Advanced Security
- Add TLS support to nREPL socket
- Implement certificate pinning in vigilant-cider
- Add request signing (HMAC-SHA256) per message
- Enable socket encryption: `--tls-keys` flag on babashka

### Performance Optimization
- Profile CIDER operations via `cider-profile-query`
- Monitor color animation overhead: `M-x profiler-start`
- Cache symbol completions: `cider-completion-cache-size`
- Adjust sentinel interval: `(run-at-time 10 10 #'asi-vigilant--sentinel)` for 10s checks

## Architecture Notes

This system demonstrates:
- **Security-first interactive development**: Vigilant CIDER monitors all connections
- **Aesthetic computing**: Kaleidoscope oscillates color state through UI elements
- **Polyglot interop**: Julia (Gay.jl) + Clojure (Babashka) + Elisp (Emacs) integrated
- **Real-time auditing**: Comprehensive audit log of all nREPL operations
- **Skill discovery**: Meta-level awareness of 616+ available skills

All components are designed to be **loaded dynamically** into running Emacs without restart.

---

**Last Updated**: 2026-02-05 @ 22:42 UTC
**Status**: ✅ All systems operational + tested
**Next Focus**: Julia↔Clojure interop via color streams (BCI pipeline integration)
