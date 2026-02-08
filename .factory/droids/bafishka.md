---
name: bafishka
description: 🐟 Rust-native Fish shell-friendly file operations with Steel-backed SCI
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Bafishka - Fish Shell + Clojure File Operations

🐟 Rust-native Fish shell-friendly file operations with Steel-backed SCI Clojure evaluation.

## Repository
- **Source**: https://github.com/bmorphism/bafishka
- **Language**: Clojure (SCI) + Rust
- **Seed**: 1069 (deterministic)

## Core Concept

Bafishka bridges Fish shell ergonomics with Clojure's data processing power:

```fish
# Fish shell with Clojure evaluation
baf '(map inc [1 2 3])'  # => [2 3 4]

# File operations with Clojure
baf '(fs/glob "**/*.clj" | count)'  # => 42
```

## Architecture

```
┌────────────────────────────────────────────────────┐
│                    Bafishka                        │
├────────────────────────────────────────────────────┤
│  ┌──────────┐   ┌──────────┐   ┌──────────────┐   │
│  │  Fish    │   │  Steel   │   │  SCI         │   │
│  │  Shell   │──▶│  (Rust)  │──▶│  (Clojure)   │   │
│  └──────────┘   └──────────┘   └──────────────┘   │
│       │              │               │             │
│       ▼              ▼               ▼             │
│   Readline       File I/O        Data Xform       │
└────────────────────────────────────────────────────┘
```

## Key Features

### Steel Backend
Steel is a Rust Scheme implementation providing:
- Fast native execution
- Seamless Rust FFI
- Async I/O support

### SCI Clojure
Small Clojure Interpreter for:
- Full Clojure core library
- REPL evaluation
- Babashka compatibility

## Usage Examples

```fish
# List files with Clojure processing
baf '(->> (fs/list-dir ".")
         (filter #(str/ends-with? % ".md"))
         (map fs/file-name))'

# JSON processing
baf '(-> (slurp "data.json")
         json/parse-string
         :items
         count)'

# With deterministic seed (1069)
baf '(gay/color 1069)'  # Deterministic color
```

## Integration with plurigrid/asi

### With gay-mcp
```clojure
;; File operations with color coding
(defn colored-ls [dir]
  (->> (fs/list-dir dir)
       (map (fn [f] 
              {:file f 
             