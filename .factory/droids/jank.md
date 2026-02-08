---
name: jank
description: "jank-lang: native Clojure on LLVM with seamless C++ interop. Use when writing native Clojure, bridging C/C++ libraries, or applying SICP Ch4-5 metalinguistic abstraction concretely."
model: inherit
tools: read-only
---

# jank

> Write Clojure for humans, compile to LLVM IR for machines.

Native Clojure on LLVM. Seamless C++ interop. 3,117 stars. Alpha January 2026. Jeaye Wilkerson.

**Use:** native perf, C/C++ libs, AOT binaries, SICP Ch4-5 concretely.
**Don't use:** pure JVM (`clojure`), scripting (`babashka`), browser (`shadow-cljs`).

## Theoretical Foundations

| Source | Concept | jank |
|--------|---------|------|
| SICP 1 | λ, higher-order fns | fns → LLVM IR; closures = GC'd C++ objects |
| SICP 2 | Abstraction barriers | Persistent data in C++; `convert<T>` = barriers |
| SICP 3 | State, concurrency | `future` (#674); atom/ref/agent; thread-safe |
| SICP 4 | Metacircular eval | jank IS it — Clojure evaluating Clojure → native |
| SICP 5 | Register machines, GC | LLVM IR = registers; Boehm GC = 5.3; AOT = 5.5 |
| SDF 1-2 | Combinators, DSLs | `cpp/raw`,`cpp/cast`,`cpp/box` compose; `cpp/` = sub-DSL |
| SDF 3-4 | Generic ops, matching | `convert<T>` traits + Clang overload resolution |
| SDF 7 | Propagators | Bidirectional: jank string ↔ `std::string` |
| SDF 8 | Degeneracy | REPL → JIT → AOT = multiple paths, same result |

Compile AND interpret simultaneously. C++ interop = escape hatch into the machine.

## Pipeline

Statically typed. Zero overhead. No reflection. Four stages per interop call:

1. **Wrapper** — C++ helper (unpack args, box return)
2. **`convert<T>`** — trait-resolved type conversion at compile time
3. **Pointer adj** — `this`, const/ref for members
4. **IR** — [CppInterOp](https://github.com/compiler-research/CppInterOp) → LLVM IR → linked

Bootstrap: Phase 1 builds compiler (C++/LLVM), Phase 2 compiles jank's stdlib with itself.

## Interop

`::` → `.` (`std::string` → `std.string`). Clojure resolves first; `cpp/` disambiguates.

```clojure
;;; HEADERS — cpp/raw: global scope, returns nil, workaround escape hatch
(cpp/raw "#include <cstdlib>")
(cpp/raw "struct vec2 { float x{}, y{}; };
          vec2 operator+(vec2 const &l, vec2 const &r)
          { r