---
name: jank-llvm
description: Jank - Clojure dialect targeting LLVM with seamless C++ interoperability
trit: 1
metadata:
  interface_ports:
  - References
  - Related Skills
  - GF(3) Triads
  - Integration with
---
# Jank LLVM Skill

> jank-lang/jank: A Clojure dialect hosted on LLVM with native C++ interop

**Trit**: +1 (PLUS) - Forward compilation to native code

## Overview

Jank is a Clojure dialect that:
- **Targets LLVM** for native machine code generation
- **Seamless C++ interop** via `c++/` namespace
- **JIT compilation** with clang::Interpreter
- **Load native libraries** (.o, .dylib, .so)
- **Persistent data structures** like Clojure

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                         JANK COMPILATION PIPELINE                        │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  Source Code                                                             │
│      │                                                                   │
│      ▼                                                                   │
│  ┌─────────┐     ┌──────────┐     ┌──────────┐     ┌─────────────┐     │
│  │  Lexer  │ ──► │  Parser  │ ──► │ Analyzer │ ──► │ LLVM Codegen│     │
│  └─────────┘     └──────────┘     └──────────┘     └──────┬──────┘     │
│                                                           │             │
│                                                           ▼             │
│                                                    ┌──────────────┐     │
│                                                    │ Optimization │     │
│                                                    │    Passes    │     │
│                                                    └──────┬───────┘     │
│                                                           │             │
│                                                           ▼             │
│                                                    ┌──────────────┐     │
│                                                    │     JIT      │     │
│                                                    │  Execution   │     │
│                                                    └──────────────┘     │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

## C++ Interoperability

### Calling C++ from Jank
```clojure
;; Access C++ namespaces with c++/ prefix
(c++/std.cout "Hello from C++!")

;; Use chrono
(def duration (c++/std.chrono.milliseconds 100))

;; Call C++ functions
(c++/my.namespace.my-function arg1 arg2)
```

### Name Mangling
Jank automatically handles:
- `kebab-case` → `snake_case`
- Namespace dots → C++ `::`
- Symbol escaping for special characters

### Loading Native Code
```clojure
;; Load object file
(native-load "/path/to/mylib.o")

;; Load dynamic library
(native-load "/path/to/mylib.dylib")  ; macOS
(native-load "/path/to/mylib.so")     ; Linux
```

## C++ REPL Mode

```bash
jank cpp_repl

# Now you can evaluate C++ directly:
cpp> #include <iostream>
cpp> std::cout << "Hello from C++ REPL!" << std::endl;
Hello from C++ REPL!
```

## LLVM Optimization Passes

Jank applies these optimization passes:
- `InstCombinePass` - Instruction combining
- `ReassociatePass` - Reassociate expressions
- `GVNPass` - Global value numbering
- `SimplifyCFGPass` - Simplify control flow

## Unique Features

### 1. Persistent Data Structures
```clojure
;; Just like Clojure
(def m {:a 1 :b 2})
(def m2 (assoc m :c 3))
;; m is unchanged, m2 has :c
```

### 2. Native Performance
- No JVM startup overhead
- Direct machine code execution
- C++ level performance for hot paths

### 3. Ray Tracer Example
```clojure
;; From jank examples - demonstrates performance
(ns ray-tracer)

(defn render [width height]
  (for [y (range height)
        x (range width)]
    (compute-pixel x y)))
```

## Build from Source

```bash
git clone https://github.com/jank-lang/jank.git
cd jank

# Requires LLVM 17+, Clang
mkdir build && cd build
cmake ..
make -j$(nproc)
```

---

## End-of-Skill Interface

## Integration with Interaction Entropy

```clojure
;; Track jank compilations
(def JANK_DB "~/.jank/interactions.duckdb")

(defn log-compilation [source-file llvm-ir-size opt-level]
  {:file source-file
   :ir-size llvm-ir-size
   :optimization opt-level
   :entropy-bits (* 2.0 (Math/log llvm-ir-size))
   :trit 1  ; PLUS - forward compilation
   :timestamp (System/currentTimeMillis)})
```

## GF(3) Triads with Jank

```
Triad 1: Native Performance
  Jank (+1) ←→ SCI (0) ←→ Scittle (-1)
  
  Interface:
    Jank: Native LLVM compilation
    SCI: Interpreted sandboxed execution
    Scittle: Browser script tags
  
  Sum: +1 + 0 + (-1) = 0 ✓

Triad 2: C++ Bridge
  Jank (+1) ←→ Joker (0) ←→ clj-kondo (-1)
  
  Interface:
    Jank: C++ interop, native code
    Joker: Go-based linting
    clj-kondo: Static analysis
  
  Sum: +1 + 0 + (-1) = 0 ✓

Triad 3: Compilation Spectrum
  Jank (+1) ←→ Babashka (0)* ←→ nbb (-1)
  
  *Babashka acts as ergodic bridge here
  Interface:
    Jank: AOT to LLVM
    Babashka: GraalVM native-image
    nbb: Node.js interpreted
  
  Sum: +1 + 0 + (-1) = 0 ✓
```

## Related Skills

- [joker-lint](file:///Users/bob/.claude/skills/joker-lint/SKILL.md) - Go-based linting
- [babashka-clj](file:///Users/bob/.claude/skills/babashka-clj/SKILL.md) - Fast scripting
- [borkdude](file:///Users/bob/.claude/skills/borkdude/SKILL.md) - Runtime selector
- [clj-kondo-3color](file:///Users/bob/.claude/skills/clj-kondo-3color/SKILL.md) - Deep linting

## References

- [jank-lang/jank](https://github.com/jank-lang/jank)
- [Jank Blog](https://jank-lang.org/blog/)
- [LLVM Documentation](https://llvm.org/docs/)


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
