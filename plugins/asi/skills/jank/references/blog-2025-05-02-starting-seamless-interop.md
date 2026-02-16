# Starting on seamless C++ interop in jank

**Date:** May 2, 2025
**Source:** jank blog

## Overview

jank aims to be the first Lisp to seamlessly reach into C++ -- not through FFI bindings or wrappers, but by understanding C++ types, overloads, and templates directly. This post covers the foundational interop mechanisms.

## C++ Values via `cpp/raw`

`cpp/raw` embeds literal C++ code within jank source. It operates at global scope and is used for including headers and injecting C++ definitions:

```clojure
(cpp/raw "#include <iostream>")
```

The form always evaluates to `nil`. It is the primary escape hatch for anything jank cannot yet express natively.

## Conversion Traits (`jank::runtime::convert<T>`)

jank defines a trait system for converting between jank runtime values and C++ types:

- **Intrinsic conversions** are built in for `int`, `float`, `double`, `bool`, `std::string`, etc.
- **Custom conversions** can be defined by specializing `jank::runtime::convert<T>`.
- Conversions are applied implicitly when passing jank values to C++ functions or returning C++ values to jank.

This trait-based approach avoids runtime reflection -- all conversions are resolved at compile time.

## Constructors with Overload Resolution

C++ constructors can be called from jank using standard function-call syntax. The compiler performs overload resolution:

- Matches argument count and types against available constructors.
- Applies implicit conversions (via the convert trait) when needed.
- Reports errors at compile time for ambiguous or missing overloads.

## Casting (`cpp/cast`)

`cpp/cast` provides the equivalent of C++ `static_cast`, extended with jank's convert traits:

```clojure
(cpp/cast target-type value)
```

This performs safe, compile-time-checked type conversions between C++ types and between jank/C++ boundary types.

## LLVM IR Generation Pipeline

Under the hood, jank compiles interop calls through several stages:

1. **Helper functions** -- The compiler generates small C++ helper functions that wrap each interop call site. These helpers handle argument unpacking, type conversion, and return value boxing.

2. **Type conversion** -- Each argument is run through the convert trait machinery. The compiler emits the appropriate conversion code in the helper function body.

3. **Pointer adjustment** -- For member functions, the compiler adjusts `this` pointers and handles const/ref qualifiers.

4. **LLVM IR emission** -- The helper functions are compiled to LLVM IR using CppInterOp (built on top of Clang/LLVM). The resulting IR is linked into the running jank process.

## CppInterOp Library

jank leverages the [CppInterOp](https://github.com/compiler-research/CppInterOp) library, which provides:

- Programmatic access to Clang's AST for querying C++ declarations.
- Function lookup by name, including overload sets.
- Type information for arguments, return types, and template parameters.
- JIT compilation of C++ code via the Clang interpreter infrastructure.

CppInterOp acts as the bridge between jank's Clojure-like frontend and the full complexity of C++ semantics.

## Key Insight

All interop is **statically typed**. jank does not use runtime reflection or dynamic dispatch for C++ calls. The compiler resolves types, overloads, and conversions at compile time, emitting efficient LLVM IR that calls C++ directly.
