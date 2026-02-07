# CIDER Best Practices 2026 + Vigilant Security

## Overview
CIDER is a powerful Clojure IDE for Emacs providing interactive development, code evaluation, debugging, and profiling. This guide combines official CIDER best practices with vigilant security monitoring (nREPL hijack detection, eval boundary crossing, socket integrity).

## 1. Connection Management

### Two Connection Modes
**cider-jack-in** (Recommended for new projects)
- Automatically injects CIDER nREPL middleware
- Manages dependencies and classpath
- Command: `C-c C-x (C-)j (C-)j`
- Works with: Leiningen 2.9.0+, tools.deps, Gradle

**cider-connect** (Existing nREPL server)
- Connect to a manually-started or remote nREPL
- Requires CIDER nREPL middleware installed separately
- Command: `M-x cider-connect`
- Supported versions:
  - CIDER 1.20+ (latest)
  - CIDER nREPL 0.49+ (latest)

### Port Management
- Default nREPL ports: 1667 (babashka), 7888 (Clojure), 3333 (Node)
- Verify listening: `lsof -i :PORT` or `netstat -tuln | grep PORT`
- Multiple projects: Each gets dedicated REPL buffer + connection

### Vigilant Connection Security
```elisp
(asi-vigilant-enable)  ;; Start monitoring
M-x asi-vigilant-show-audit-log  ;; View security events
```

**Monitored Threats**:
1. Non-localhost connections (only 127.0.0.1, localhost, ::1 allowed)
2. Unexpected port changes (only verified ports, default 1667)
3. Process swapping (nREPL endpoint substitution detection)
4. Eval source boundary crossing (detecting code injection)
5. Anomalous socket writes (>100KB threshold alert)

## 2. Code Evaluation

### Evaluation Terminology
- **defun**: Top-level expression (function/macro definition)
- **sexp**: S-expression, arbitrary form
- **last-sexp**: Form immediately before cursor position
- **sexp-at-point**: Form containing or immediately before cursor

### Core Evaluation Commands
| Command | Binding | Purpose |
|---------|---------|---------|
| `cider-eval-last-sexp` | `C-x C-e` | Eval form before cursor, result in minibuffer |
| `cider-eval-region` | `C-c C-r` | Eval selected region |
| `cider-eval-defun` | `C-M-x` | Eval top-level form (defn/def/deftest) |
| `cider-eval-buffer` | `C-c C-k` | Eval entire buffer |
| `cider-eval-ns-form` | `C-c C-c` | Eval form at cursor + all dependencies |
| `asi-cider-eval-region-safe` | `C-c C-e` | Eval region with vigilance guards (boundary tracking) |

### Result Display
- Inline results: `#'var` for vars, function metadata, lazy seqs
- Pretty-printing: CIDER automatically formats output
- Images: Inline display of base64 PNG/JPG
- Long results: Truncated with history via `C-c M-h`

## 3. Code Reloading & "Reloaded" Workflow

The "Reloaded" pattern (popularized by Stuart Sierra blog) is essential for interactive development:

### Commands
- `C-c M-n r`: Reload current namespace (cider-ns-refresh)
- `C-c M-n n`: Reload all namespaces (cider-ns-refresh-all)
- `C-c M-n l`: Reload with fresh JVM state (cider-refresh)

### Workflow Pattern
1. Define start/stop functions in your reloadable namespaces
2. Use `:reload-namespaces` or `cider-refresh-before-fn` hook
3. Reload during development to eliminate stale definitions
4. Combine with `test` or `:clj-kondo/config` for safe reloads

### Why Reload?
- Clojure doesn't automatically undefine vars when redefined
- Stale definitions can mask bugs
- Interactive dev relies on clean state
- Essential for hot-reload workflows

## 4. REPL Features & History

### REPL Buffer (`*cider-repl babashka*`)
- Code completion via `M-TAB`
- Font-locking (same as clojure-mode)
- Quick access to CIDER commands
- Persistent history across sessions
- Pretty-printed results

### History Navigation
- `M-p` / `M-n`: Previous/next history entry
- `C-c M-h`: Open REPL history browser (search + filter)
- `C-c M-l`: Clear REPL buffer

### REPL State
- Namespace context: `(in-ns 'user)` to switch namespaces
- Clear definitions: Use `(ns/reset)` helper or reload
- Multiple buffers: Each REPL is independent with own session

## 5. Middleware & cider-nrepl

CIDER's advanced features depend on `cider-nrepl` middleware:

### What cider-nrepl Provides
- Code completion
- Source/documentation lookup
- Profiling (sampled + statistical)
- Debugging (breakpoints, step-over)
- Code reloading/refreshing
- Find references & usages
- Running tests from editor
- Stacktrace filtering
- Semantic navigation (jump-to-def)

### Setup for cider-connect
If using manual nREPL server (not cider-jack-in), add to `deps.edn`:
```clojure
:nrepl
{:extra-deps {nrepl/nrepl {:mvn/version "1.3.1"}
              cider/cider-nrepl {:mvn/version "0.49.0"}}}
```

Then start with:
```bash
clj -M:nrepl
```

## 6. Multi-Project Management

### Multiple Connections
- Each project gets dedicated REPL buffer
- Switching: `C-c M-o` (Clojure/ClojureScript toggle) or `C-c M-s` (select connection)
- Disconnect: `C-c M-d` (cider-disconnect)

### Server vs Client
- **Server**: Your nREPL process (babashka, lein, clj, etc.)
- **Client**: Emacs CIDER connecting via socket
- Both must use compatible versions

### Variable Scoping
- Each REPL has isolated vars (unless explicitly shared)
- Use `require` in REPL to load code
- Use `:require [:reload]` to reload during iteration

## 7. Debugging & Profiling

### Debugging
- `#break` macro: Pause execution (requires cider-nrepl)
- Locals inspection: View local variables in paused state
- Step through code: Step-in, step-over, resume
- Conditional breakpoints: Pause on specific conditions

### Profiling
- Statistical profiling: Sample-based (low overhead)
- Flame graphs: Visualize CPU time distribution
- Memory tracking: Track allocation patterns
- Command: `C-c M-p`

## 8. Vigilant CIDER Integration

### Security Guarantees
```elisp
;; Hijack Detection: Only localhost + verified ports
(asi-vigilant--check-connection-safety "127.0.0.1" 1667)  ;; ✅ SAFE

;; Eval Boundary Crossing: Track source file for code
(asi-vigilant--record-source-file "/path/to/file.clj")
(asi-cider-eval-region-safe start end)  ;; Verifies file context

;; Socket Integrity: Monitor nREPL writes
;; Alerts on >100KB messages, unexpected patterns

;; Sentinel Process: Background verification every 5s
(asi-vigilant-enable)  ;; Starts sentinel, enables advice
```

### Audit Log
- View: `M-x asi-vigilant-show-audit-log`
- Logs: connection attempts, boundary crossings, socket ops
- Format: Org-mode table with timestamps + event types

### Disabling (if needed)
```elisp
(asi-vigilant-disable)  ;; Stops sentinel + advice
```

## 9. Performance Tips

### Lazy Sequence Handling
- Don't realize entire sequences in REPL (causes memory bloat)
- Use `take(n)` to preview: `(take 10 my-lazy-seq)`
- Use `sequence` or `realize` explicitly when needed

### Large Result Handling
- CIDER truncates by default (set `cider-result-buffer-size`)
- Use `cider-eval-last-sexp-and-replace` (`C-c M-e`) to replace expression with result

### Classpath & Loading
- Use `cider-load-file` (C-c M-l) for loading source files
- Reload via `cider-ns-refresh` for clean state
- Profile with `cider-profile-query` to find bottlenecks

## 10. Testing Integration

### Running Tests
- `C-c C-t C-t`: Run test at point
- `C-c C-t C-n`: Run all tests in namespace
- `C-c C-t C-a`: Run all tests in project
- `C-c C-t C-l`: Run last-run tests

### Test Results
- Failures: Colored + stacktrace
- Errors: Full exception trace
- Coverage: Visual highlight of tested code

### Test Reloading
- Use `cider-ns-refresh` before running tests
- Combine with `:test-reload` alias in `deps.edn`

## 11. Keyboard Shortcuts Reference

| Binding | Command | Purpose |
|---------|---------|---------|
| C-c C-k | cider-eval-buffer | Eval buffer |
| C-c C-r | cider-eval-region | Eval region |
| C-x C-e | cider-eval-last-sexp | Eval last sexp |
| C-M-x | cider-eval-defun | Eval defun |
| C-c C-c | cider-eval-top-level-form | Eval with deps |
| C-c C-e | asi-cider-eval-region-safe | Eval with vigilance |
| C-c C-b | cider-interrupt | Interrupt evaluation |
| C-c M-n r | cider-ns-refresh | Reload namespace |
| C-c M-n l | cider-refresh | Full reload |
| C-c M-h | cider-repl-history | Open history browser |
| C-c M-d | cider-disconnect | Disconnect REPL |
| C-c M-o | cider-repl-toggle-pretty-print | Toggle pretty-print |
| M-x asi-vigilant-show-audit-log | Security audit | View security events |

## 12. Troubleshooting

### "nREPL connection lost"
- Check: `lsof -i :1667` (babashka still running?)
- Restart: `bb --nrepl-server 1667`
- Reconnect: `M-x cider-connect`

### Stale Definitions
- Use `cider-ns-refresh` (C-c M-n r)
- Check namespace load order: `:require` vs `:require-macros`
- Restart nREPL if reload fails: `C-c M-n l`

### Completion Not Working
- Verify middleware: `cider-nrepl` must be loaded
- Check: `(cider.nrepl.middleware/info)` in REPL
- Restart: `cider-restart`

### "Hijack Alert" in Vigilant CIDER
- Port 1667 is not listening? Start: `bb --nrepl-server 1667`
- Non-localhost? Use 127.0.0.1 or localhost only
- Process swapped? Check: `lsof -i :1667`

## 13. References
- **Official**: https://docs.cider.mx/ (CIDER 1.20+, nREPL 0.49+)
- **Code Evaluation**: https://docs.cider.mx/cider/usage/code_evaluation.html
- **Middleware Setup**: https://docs.cider.mx/cider/basics/middleware_setup.html
- **Managing Connections**: https://docs.cider.mx/cider/usage/managing_connections.html
- **Code Reloading**: https://docs.cider.mx/cider/usage/code_reloading.html
- **Vigilant CIDER**: `/Users/bob/i/asi/skills/asi-transient-agenda/asi-vigilant-cider.el`

---

**Setup Status**: ✅ CIDER 1.20+, babashka nREPL :1667, Vigilant monitoring enabled
