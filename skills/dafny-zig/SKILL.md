---
name: dafny-zig
description: Dafny-to-Zig compiler backend development skill with verified runtime safety ("Zig-syrup")
---

# Dafny-Zig Compiler Backend

*Title: Performant, Readable and Interoperable Zig from Dafny*

Specialized skill for developing `dafny-zig`, a backend compiling Dafny's intermediate representation (DAST) to safe, idiomatic Zig code.

## Core Philosophy: "Zig-Syrup"

This project bridges Dafny's **infinite assumptions** (unbounded ints, memory, termination) with Zig's **finite reality** (systems programming). The binding agent ("syrup") is **Runtime Safety**.

### Abstract
We bridge the gap between Dafny's verification guarantees and Zig's explicit resource management through "Zig-Syrup" (`runtime.zig`), a lightweight runtime layer.

1.  **Safety First**: `rt.BigInt` and `rt.RcSlice` provide Dafny-like semantics with Zig safety.
2.  **Explicit Allocation**: Use `std.ArrayListUnmanaged` and pass allocators explicitly.
3.  **Formal Verification**: Respect DAST semantics. If Dafny verified it, Zig must implement it faithfully or trap safely.

## Workflow (Tweag Standard)

Follow the **Three Experts Method** for all significant changes:

1.  **Verifier (Dafny Expert)**: Analyze DAST requirements (infinite ints, immutability).
2.  **Systems Engineer (Zig Expert)**: Propose safe implementation (`RcSlice`, `Unmanaged`).
3.  **Compiler Dev**: Bridge the two in `compiler.zig`.

**Validation Loop:**
1.  `zig build test` (Must pass)
2.  `dafny verify` (on source `.dfy` if available)
3.  Review `src/runtime.zig` for memory leaks (use `std.testing.allocator`).

## Key Components

### 1. DAST (Dafny AST)
- **`src/dast.zig`**: Accurate reflection of Dafny's JSON IR.
- **Rules**: Immutable by default. Use `parseModuleJson`.

### 2. ZAST (Zig AST)
- **`src/zast.zig`**: Generates idiomatic Zig source.
- **Rules**: Supports `StructDecl`, `UnionDecl` (for Datatypes), `FnDecl`.

### 3. Runtime Library (`rt`)
- **`src/runtime.zig`**: The "Syrup" (Sticky Binding Agent).
- **`BigInt`**: Uses `std.ArrayListUnmanaged(u64)`. Handles OOM.
- **`RcSlice(T)`**: O(1) slicing and safe sharing for `Seq<T>`.
- **`Set/Map`**: `std.AutoHashMap` wrappers with value semantics.

## Readability & Interoperability
Generated code should not look like "compiler vomit." It should look like Zig.
- **Structs & Unions**: Dafny `datatype` maps cleanly to Zig `union(enum)`.
- **Modules**: Dafny modules map to Zig files/structs.
- **Native Types**: Where Dafny proves bounds, we emit native `u8`/`u64`.

## Scientific Skill Interleaving

### Plurigrid ASI Integration
- **Role**: `dafny-zig` acts as a **Verifier (MINUS -1)** in the Plurigrid ecosystem.
- **Connection**: Consumes `acsets` (via DAST) and produces `zig` (systems).

### SDF Interleaving
- **Chapter**: 5. Evaluation (Compiler as Evaluator).
- **Pattern**: `compileModule` is a recursive evaluator transforming DAST -> ZAST.

## Commands

```bash
# Build and test compiler
zig build test

# Compile a DAST file
zig build run -- compile module.dast.json output.zig
```

## References

- **Mathpix**: Used for OCR of formal specs (`mathpix-gem/`).
- **Research**: See `.topos/` for bibliography (CakeML, Verified VCG).
