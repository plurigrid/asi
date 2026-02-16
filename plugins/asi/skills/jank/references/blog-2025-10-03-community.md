# The jank community has stepped up!

**Date:** October 3, 2025
**Source:** jank blog

## Overview

This post covers C++ interop stability improvements, distribution packaging, the two-phase compiler build, and significant community contributions. An alpha release is targeted for December 2025.

## C++ Interop Stability

### Enums
C++ enums (both scoped `enum class` and unscoped `enum`) are now supported in interop. Enum values can be passed to and returned from C++ functions.

### Pointers
Pointer types are handled correctly across the interop boundary, including pointer-to-pointer, const pointers, and void pointers.

### Lambda Captures
C++ lambdas with captures can be created and used from jank. The compiler correctly handles capture semantics (by value, by reference).

### `cpp/aget`
Array element access via `cpp/aget` provides indexed access into C++ arrays and containers:

```clojure
(cpp/aget my-array idx)
```

## Distribution

### Ubuntu PPA
jank is available via a Personal Package Archive for Ubuntu users:

```bash
sudo add-apt-repository ppa:jank-lang/jank
sudo apt update
sudo apt install jank
```

### macOS Homebrew

```bash
brew install jank-lang/jank/jank
```

### AUR (Arch Linux)
Available as an AUR package for Arch Linux and derivatives.

### Nix Binary Cache
A Nix binary cache is provided so Nix users get pre-built binaries rather than compiling from source.

## Two-Phase Compiler Building

The jank compiler uses a two-phase build process:

1. **Phase 1:** Build the compiler itself (C++ codebase, LLVM/Clang integration, CppInterOp).
2. **Phase 2:** Use the Phase 1 compiler to compile jank's standard library and runtime (written in jank + C++).

This bootstrapping approach ensures the standard library is compiled with the same interop machinery that user code will use.

## Community Contributions

### nREPL Server (Kyle Cesare)
Kyle Cesare implemented an nREPL server for jank, enabling:

- REPL-driven development from editors (Emacs CIDER, Calva, Conjure, etc.).
- Standard nREPL protocol compatibility.

Kyle also built an **imgui wrapper** using jank's C++ interop, demonstrating immediate-mode GUI development from jank.

### `#cpp` String Literals
Support for `#cpp` tagged string literals, allowing ergonomic inline C++ values:

```clojure
#cpp/int 42
#cpp/float 3.14
#cpp/str "hello"
```

### Big Decimals and Big Integers
Arbitrary-precision numeric types matching Clojure's `BigDecimal` and `BigInteger` semantics.

### Regex, UUID, Instant
Standard library additions:

- **Regex:** `re-pattern`, `re-find`, `re-matches`, `re-seq` with C++ regex backend.
- **UUID:** `random-uuid` and UUID parsing.
- **Instant:** `inst` literals and time functions.

### AOT Executable Building
Ahead-of-time compilation to standalone executables:

```bash
lein compile
```

Produces a native binary with no runtime dependency on the jank compiler. This is critical for deployment and distribution of jank applications.

## Alpha Release Target

The project is targeting a **December 2025 alpha release** with:

- Stable C++ interop.
- Package manager distribution across major platforms.
- nREPL support for editor integration.
- AOT compilation to native executables.
- Core Clojure compatibility (most of `clojure.core`).
