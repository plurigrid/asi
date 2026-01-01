---
name: shell-guard
description: Shell ENOENT prevention with fallback chain and environment validation
metadata:
  trit: 0
  interface_ports:
    - babashka-clj
    - flox
    - autopoiesis
---
# shell-guard

Prevent the #1 anti-pattern across AMP accounts: `ENOENT spawn /bin/bash|zsh`.

**Trit**: 0 (ERGODIC/Coordinator)
**Seed**: 137508
**Anti-Patterns Addressed**: 15+ occurrences across account threads

---

## Problem Statement

```
Tool Error: {"message":"ENOENT: no such file or directory, posix_spawn '/bin/bash'"}
Tool Error: {"message":"spawn /bin/zsh ENOENT"}
```

These errors occur when:
1. Shell path differs between environments (Nix, macOS, Linux)
2. Flox/Nix environment not activated
3. CWD parameter incorrect or missing
4. Shell not in expected location

---

## Solution: Fallback Chain

```
/bin/zsh → /bin/bash → /bin/sh → /usr/bin/env sh → python3 subprocess
```

---

## Usage

### Babashka (Recommended)

```clojure
#!/usr/bin/env bb
(require '[shell-guard :refer [safe-shell find-shell validate-env]])

;; Simple command execution with automatic fallback
(safe-shell "ls -la")

;; With options
(safe-shell "npm install" 
  :cwd "/path/to/project"
  :timeout 120000
  :env {"NODE_ENV" "production"})

;; Pre-flight environment check
(when-not (validate-env ["git" "gh" "julia"])
  (println "Missing dependencies, activating flox...")
  (safe-shell "flox activate -- git --version"))
```

### Integration with autopoiesis

```clojure
;; Add to .ruler/skills/shell-guard.cljs
(require '[autopoiesis.prompt :refer [modify-prompt!]])

(modify-prompt! :claude "shell-safety"
  "## Shell Safety Rules
   1. Never assume /bin/bash or /bin/zsh exists
   2. Always use shell-guard for subprocess calls
   3. Check flox activate for Nix-managed tools
   4. Provide explicit cwd parameter
   5. Handle ENOENT gracefully with retry")

(modify-prompt! :codex "shell-safety"
  "Use shell-guard.bb for all shell operations.")

(modify-prompt! :amp "shell-safety"  
  "Prefer shell-guard safe-shell over raw Bash tool.")
```

---

## Core Implementation

### shell_guard.bb

```clojure
#!/usr/bin/env bb
(ns shell-guard
  (:require [babashka.process :as p]
            [babashka.fs :as fs]
            [clojure.string :as str]))

;; ═══════════════════════════════════════════════════════════════
;; SHELL DETECTION
;; ═══════════════════════════════════════════════════════════════

(def SHELL-PREFERENCE
  "Ordered preference for shell discovery"
  ["/bin/zsh"
   "/bin/bash"
   "/bin/sh"
   "/usr/bin/env"
   (System/getenv "SHELL")])

(defn find-shell
  "Find first available shell from preference list"
  []
  (first 
    (filter 
      (fn [path]
        (and path 
             (fs/exists? path)
             (fs/executable? path)))
      SHELL-PREFERENCE)))

(defn shell-info
  "Get shell metadata for debugging"
  []
  (let [shell (find-shell)]
    {:found shell
     :env-shell (System/getenv "SHELL")
     :user (System/getenv "USER")
     :home (System/getenv "HOME")
     :path (System/getenv "PATH")}))

;; ═══════════════════════════════════════════════════════════════
;; ENVIRONMENT VALIDATION
;; ═══════════════════════════════════════════════════════════════

(defn which
  "Find executable in PATH"
  [cmd]
  (try
    (let [result (p/shell {:out :string :err :string :continue true}
                          "which" cmd)]
      (when (zero? (:exit result))
        (str/trim (:out result))))
    (catch Exception _ nil)))

(defn validate-env
  "Check if required executables are available"
  [required-cmds]
  (let [results (map (fn [cmd] {:cmd cmd :path (which cmd)}) required-cmds)
        missing (filter #(nil? (:path %)) results)]
    {:valid (empty? missing)
     :missing (map :cmd missing)
     :found (filter :path results)}))

(defn flox-activate-prefix
  "Generate flox activate prefix if needed"
  [cmd]
  (if (which cmd)
    ""
    "flox activate -- "))

;; ═══════════════════════════════════════════════════════════════
;; SAFE SHELL EXECUTION
;; ═══════════════════════════════════════════════════════════════

(defn safe-shell
  "Execute command with shell fallback and error recovery"
  [cmd & {:keys [cwd timeout env out err continue]
          :or {timeout 60000 out :string err :string continue false}}]
  (let [shell (find-shell)
        opts (cond-> {:out out :err err :continue true}
               cwd (assoc :dir cwd)
               timeout (assoc :timeout timeout)
               env (assoc :extra-env env))]
    
    ;; Guard: no shell found
    (when-not shell
      (throw (ex-info "No shell found in system" 
                      {:tried SHELL-PREFERENCE
                       :env (shell-info)})))
    
    (try
      ;; Attempt 1: Use discovered shell
      (let [result (p/shell opts shell "-c" cmd)]
        (if (and (not continue) (not (zero? (:exit result))))
          (throw (ex-info "Command failed" {:exit (:exit result) :err (:err result)}))
          result))
      
      (catch Exception e
        (let [msg (str e)]
          (cond
            ;; ENOENT on primary shell - try /bin/sh
            (str/includes? msg "ENOENT")
            (do
              (println "⚠️ Shell ENOENT, trying /bin/sh fallback...")
              (try
                (p/shell opts "/bin/sh" "-c" cmd)
                (catch Exception e2
                  ;; Final fallback: python subprocess
                  (println "⚠️ /bin/sh failed, trying python3 fallback...")
                  (let [py-cmd (format "import subprocess; subprocess.run(['sh', '-c', '''%s'''], check=True)"
                                       (str/replace cmd "'" "\\'"))]
                    (p/shell opts "python3" "-c" py-cmd)))))
            
            ;; Timeout - useful info but rethrow
            (str/includes? msg "timeout")
            (throw (ex-info "Command timed out" 
                            {:cmd cmd :timeout timeout :shell shell}))
            
            ;; Other error - rethrow with context
            :else
            (throw (ex-info "Shell execution failed"
                            {:cmd cmd :shell shell :error msg}))))))))

;; ═══════════════════════════════════════════════════════════════
;; FLOX INTEGRATION
;; ═══════════════════════════════════════════════════════════════

(defn with-flox
  "Execute command with flox environment"
  [cmd & opts]
  (apply safe-shell (str "flox activate -- " cmd) opts))

(defn ensure-flox-env
  "Ensure flox environment is available, activate if needed"
  [required-cmds]
  (let [validation (validate-env required-cmds)]
    (if (:valid validation)
      {:status :ready :cmds required-cmds}
      (do
        (println (str "⚠️ Missing: " (str/join ", " (:missing validation))))
        (println "Activating flox environment...")
        (safe-shell "flox activate")
        (let [recheck (validate-env required-cmds)]
          (if (:valid recheck)
            {:status :activated :cmds required-cmds}
            {:status :failed :missing (:missing recheck)}))))))

;; ═══════════════════════════════════════════════════════════════
;; GF(3) TRIT DERIVATION
;; ═══════════════════════════════════════════════════════════════

(def SEED 137508)

(defn derive-trit
  "Derive GF(3) trit from command hash"
  [cmd]
  (let [h (hash cmd)
        m (mod (Math/abs h) 3)]
    (- m 1)))  ; -1, 0, or 1

;; ═══════════════════════════════════════════════════════════════
;; CLI INTERFACE
;; ═══════════════════════════════════════════════════════════════

(defn -main [& args]
  (cond
    (empty? args)
    (do
      (println "shell-guard: Shell ENOENT prevention")
      (println)
      (println "Usage:")
      (println "  bb shell_guard.bb exec <command>")
      (println "  bb shell_guard.bb validate <cmd1> <cmd2> ...")
      (println "  bb shell_guard.bb info")
      (println)
      (println "Current shell info:")
      (prn (shell-info)))
    
    (= (first args) "exec")
    (let [cmd (str/join " " (rest args))
          result (safe-shell cmd)]
      (print (:out result))
      (System/exit (:exit result)))
    
    (= (first args) "validate")
    (let [cmds (rest args)
          result (validate-env cmds)]
      (if (:valid result)
        (println "✓ All commands available")
        (do
          (println (str "✗ Missing: " (str/join ", " (:missing result))))
          (System/exit 1))))
    
    (= (first args) "info")
    (prn (shell-info))
    
    :else
    (println (str "Unknown command: " (first args)))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
```

---

## Ruler Propagation

```toml
# .ruler/ruler.toml

[skills.shell-guard]
enabled = true
trit = 0
propagate = ["claude", "codex", "amp", "cursor", "goose"]

[agents.claude.skills]
shell-guard = { inject_prompt = true }

[agents.codex.skills]
shell-guard = { inject_prompt = true }
```

---

## Anti-Pattern Prevention Matrix

| Anti-Pattern | Detection | Prevention | Recovery |
|--------------|-----------|------------|----------|
| ENOENT /bin/bash | find-shell returns nil | Fallback chain | python3 subprocess |
| ENOENT /bin/zsh | shell-info check | Try /bin/bash first | /bin/sh fallback |
| Missing executable | validate-env | ensure-flox-env | flox activate |
| Timeout | :timeout option | Batch operations | Retry with longer timeout |
| Wrong CWD | :cwd parameter | Explicit path | Error with context |

---

## Integration Examples

### With autopoiesis DuckDB tracking

```clojure
(require '[autopoiesis.duckdb :refer [log-change!]])

(defn tracked-shell [cmd & opts]
  "Shell execution with DuckDB logging"
  (let [trit (derive-trit cmd)
        result (apply safe-shell cmd opts)]
    (log-change! "system" "shell" cmd nil 
                 {:exit (:exit result) :trit trit})
    result))
```

### With gay-mcp coloring

```clojure
(require '[gay :refer [color-at]])

(defn colored-shell [cmd & opts]
  "Shell with deterministic color output"
  (let [color (color-at SEED (hash cmd))
        result (apply safe-shell cmd opts)]
    (println (str "\033[38;2;" (color-rgb color) "m" 
                  "$ " cmd "\033[0m"))
    result))
```

---

## Files

| Path | Description |
|------|-------------|
| `shell_guard.bb` | Core Babashka implementation |
| `SKILL.md` | This documentation |

---

## References

- Anti-pattern analysis: `/Users/bob/ies/ANTI_PATTERN_SKILL_INTEGRATION.md`
- ExpensiveLoopsACSet: `/Users/bob/ies/asi/src/expensive_loops_acset.jl`
- Ruler: https://github.com/intellectronica/ruler
- Autopoiesis skill: `~/.claude/skills/autopoiesis/`
