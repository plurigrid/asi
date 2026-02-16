---
name: jo-clojure
description: Clojure skill orchestration and polyglot bridge. Coordinates cross-language skill composition, manages JVM-based skills, and provides Clojure tooling integration. Use for skill coordination, polyglot composition, and Clojure ecosystem management.
license: MIT
compatibility: Requires Clojure 1.11+, Java 11+, and clojure CLI. Works with all JVM-based tools (joker, babashka, nbb, etc.). Integrates with Gay.jl color generation and Boxxy skill system.
metadata:
  version: 1.0.0
  author: Claude via Boxxy
  gf3-trit: 0
  trit-role: ERGODIC (Coordinator)
  build-system: "clojure CLI with deps.edn"
  jvm-version: "11+"
  clojure-version: "1.11+"
allowed-tools: "Bash(clojure:*) Bash(java:*) Read"
---

# jo-clojure - Polyglot Skill Coordinator

## Overview

**jo-clojure** coordinates polyglot skill ecosystems using Clojure as the orchestration layer. It bridges JVM-based skills (Clojure, Babashka, Joker), provides skill composition abstractions, and manages cross-language capability routing.

**Role**: ERGODIC coordinator in triadic consensus - balances validation (joker) and generation (hy-regime) in skill pipelines.

## Quick Start

### Set Up Clojure Tooling

```bash
# Check Clojure CLI installation
clojure -version

# Create/update project structure
cd /Users/bob/i/boxxy
clojure -X:deps tree

# List available aliases
clojure -X:deps list-aliases
```

### Key Commands

```bash
# Start Clojure REPL
clojure

# Run a script
clojure -X user/my-function :arg1 value1

# Evaluate expression
clojure -e '(+ 1 2 3)'

# Run tests
clojure -X:test
```

## Installation

### 1. Install Clojure CLI (if not already)

```bash
# macOS with Homebrew
brew install clojure/tools/clojure

# Or download from https://clojure.org/guides/install_clojure
```

### 2. Configure ~/.clojure/deps.edn

The global deps.edn file coordinates all Clojure projects:

```edn
{
  :aliases {
    ;; Polyglot skill ecosystem
    :skill-validate  {:extra-deps {org.clojure/clojure {:mvn/version "1.11.1"}
                                    clojure.spec.alpha {:mvn/version "0.2.207"}}}
    :skill-test      {:extra-deps {org.clojure/clojure {:mvn/version "1.11.1"}
                                    expectations/clojure-test {:mvn/version "1.2.1"}}}
    :skill-repl      {:extra-deps {org.clojure/clojure {:mvn/version "1.11.1"}
                                    nrepl/nrepl {:mvn/version "0.9.1"}
                                    cider/cider-nrepl {:mvn/version "0.28.4"}}}

    ;; Polyglot tools
    :bb              {:extra-deps {org.babashka/babashka {:mvn/version "1.3.192"}}}
    :joker           {:extra-deps {candelbp/joker {:mvn/version "0.15.7"}}}

    ;; Color generation (Gay.jl integration)
    :color-gen       {:extra-deps {org.clojure/clojure {:mvn/version "1.11.1"}}}

    ;; GF(3) skill validation
    :gf3-validate    {:extra-deps {org.clojure/clojure {:mvn/version "1.11.1"}
                                    org.clojure/math.numeric-tower {:mvn/version "0.0.4"}}}
  }
}
```

## Polyglot Skill Composition

### Pattern 1: Validator → Coordinator → Generator

```clojure
(defn triadic-skill-pipeline
  "Compose three skills in GF(3) consensus."
  [{:keys [validator coordinator generator]}]
  (let [v-result (validator/run)
        c-state (coordinator/process v-result)
        g-output (generator/produce c-state)]
    {:validation v-result
     :coordination c-state
     :generation g-output
     :gf3-sum (+ (validator/trit)
                 (coordinator/trit)
                 (generator/trit))}))
```

### Pattern 2: Skill to Color Mapping

Uses Gay.jl deterministic color generation:

```clojure
(defn skill->color
  "Map skill name deterministically to color via splitmix RNG."
  [skill-name seed]
  (let [gen (SplitMixTernary. seed)
        idx (hash skill-name)]
    (gen/color-at idx)))
```

### Pattern 3: Cross-Language Dispatch

Routes to Clojure, Babashka, or compiled binaries:

```clojure
(defmulti invoke-skill (fn [{:keys [language]}] language))

(defmethod invoke-skill :clojure [spec]
  (require (symbol (:module spec)))
  (apply (resolve (symbol (:function spec))) (:args spec)))

(defmethod invoke-skill :babashka [spec]
  (shell/sh "bb" "-e" (:code spec)))

(defmethod invoke-skill :go [spec]
  (shell/sh (:binary spec) (concat (:flags spec))))
```

## Skill Registry Operations

### Reading Skill Metadata

```clojure
(defn read-skill-properties [skill-dir]
  "Extract SKILL.md frontmatter as Clojure map."
  (let [skill-md (slurp (str skill-dir "/SKILL.md"))
        [_ frontmatter _] (string/split skill-md #"---\n?" 3)
        yaml (yaml/parse frontmatter)]
    yaml))

(defn list-all-skills [skills-root]
  "Enumerate all skills with metadata."
  (->> (io/file skills-root)
       .listFiles
       (filter #(.isDirectory %))
       (map read-skill-properties)))
```

### Validating GF(3) Balance

```clojure
(defn validate-gf3-triad [skills-map]
  "Check that three skills sum to 0 mod 3."
  (let [trit-sum (->> skills-map
                      vals
                      (map #(get % :gf3-trit 0))
                      (apply +))]
    (= (mod trit-sum 3) 0)))

(defn suggest-balancer [two-skills]
  "Given two skills, find trit needed for third."
  (let [current-sum (apply + (map #(get % :gf3-trit 0) two-skills))
        needed (- (mod (- current-sum) 3))]
    needed))
```

## Clojure Tooling Setup

### Project Structure

```
/Users/bob/i/boxxy/
├── deps.edn                  # Global Clojure config
├── skills/
│   ├── jo-clojure/
│   │   ├── SKILL.md
│   │   ├── scripts/
│   │   │   ├── skill_registry.clj    # Skill discovery
│   │   │   ├── gf3_validator.clj     # GF(3) checking
│   │   │   └── polyglot_dispatch.clj # Multi-language dispatch
│   │   └── references/
│   │       ├── CLOJURE_SETUP.md
│   │       ├── SKILL_COMPOSITION.md
│   │       └── GF3_SEMANTICS.md
│   ├── joker-sims-parser/
│   ├── hy-regime/
│   └── zig-systems/
└── .clojure/
    ├── deps.edn              # User-level aliases
    └── tools/                # Clojure tools
```

### REPL Startup

Create `~/.clojure/repl-init.clj`:

```clojure
; Load commonly used skills
(require '[clojure.java.io :as io])
(require '[clojure.string :as str])
(require '[clojure.pprint :as pp])

(defn skills-dir []
  "/Users/bob/i/boxxy/skills")

(defn load-skill [name]
  (println (format "Loading skill: %s" name)))

(println "Boxxy skill coordinator ready")
(println "  skills-dir    - show skills directory")
(println "  load-skill    - load a skill by name")
```

## When to Use

- **Coordinating multi-language skills**: Compose Go, Clojure, Hy, and Zig tools
- **GF(3) validation**: Check that skill triads maintain conservation
- **Skill discovery**: List and inspect available skills
- **Dynamic dispatch**: Route to different implementations based on input
- **JVM ecosystem integration**: Manage Clojure, Babashka, and other JVM tools
- **REPL-based development**: Interactive skill testing and composition

## When NOT to Use

- Simple single-language tasks (use language-specific skills directly)
- Performance-critical code (use native Go/Zig skills)
- Tasks not requiring triadic balance (simpler coordination systems exist)

## GF(3) Conservation

jo-clojure is assigned **trit = 0 (ERGODIC)** for coordinator role:

```
Validator (-1) + Coordinator (0) + Generator (+1) ≡ 0 (mod 3)
 [joker]        [jo-clojure]      [hy-regime]
```

Ensures every triadic composition maintains GF(3) sum ≡ 0 (mod 3).

## Common Tasks

### Load All Skills and Check Balance

```clojure
(let [skills (skills/list-all-skills "/Users/bob/i/boxxy/skills")
      trits (map :gf3-trit skills)]
  (println "Total trits:" (apply + trits))
  (println "Balanced?" (zero? (mod (apply + trits) 3))))
```

### Compose Three Skills

```clojure
(let [validator (skills/find "joker-sims-parser")
      coordinator (skills/find "jo-clojure")
      generator (skills/find "hy-regime")]
  (triadic/validate-triad [validator coordinator generator])
  (triadic/execute [validator coordinator generator] input-data))
```

### Dynamic Skill Invocation

```clojure
(invoke-skill {:language :go
               :binary "/Users/bob/i/boxxy/bin/joker"
               :flags ["parse" "save.sims3pack"]})
```

## Troubleshooting

**"command not found: clojure"**
- Install Clojure CLI: `brew install clojure/tools/clojure`
- Verify: `clojure -version`

**Dependency resolution errors**
- Clear cache: `rm -rf ~/.m2/repository`
- Update indices: `clojure -X:deps list-aliases`

**REPL not starting**
- Check Java version: `java -version` (requires 11+)
- Verify Clojure: `clojure -e '(clojure-version)'`

**GF(3) validation failures**
- Check trit assignments in skill metadata
- Verify sum: `(+ -1 0 1)` should equal 0

## References

- [Clojure Official Docs](https://clojure.org)
- [Clojure CLI Guide](https://clojure.org/guides/deps_and_cli)
- [deps.edn Reference](https://clojure.org/reference/deps_edn)
- [Babashka](https://github.com/babashka/babashka)
- [Joker (Clojure on GCP/Go)](https://github.com/candelbp/joker)
- [Gay.jl Color Generation](https://github.com/bmorphism/gay.jl)
