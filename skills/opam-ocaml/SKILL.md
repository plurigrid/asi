---
name: opam-ocaml
description: "OPAM package manager for OCaml. Switch management, dependency resolution, and OCaml toolchain."
metadata:
  trit: -1
  version: "1.0.0"
  bundle: tooling
geodesic: true
moebius: "μ(n) ≠ 0"
---

# OPAM OCaml Skill

**Trit**: -1 (MINUS - package constraint verification)  
**Foundation**: OPAM + OCaml + dune  

## Core Concept

OPAM manages OCaml development:
- Compiler switches (versions)
- Package dependencies
- Build system integration
- Repository management

## Common Commands

```bash
# Switch management
opam switch create 5.1.0
opam switch list
opam switch 5.1.0

# Package operations
opam install dune merlin ocaml-lsp-server
opam upgrade
opam remove <pkg>

# Environment
eval $(opam env)

# Repository
opam repo add coq-released https://coq.inria.fr/opam/released
```

## Dune Integration

```
; dune-project
(lang dune 3.0)
(name my_project)

; dune
(library
 (name my_lib)
 (libraries core))
```

## GF(3) Integration

```ocaml
type trit = Minus | Ergodic | Plus

let trit_of_build_status = function
  | Build_error _ -> Minus
  | Build_warning _ -> Ergodic
  | Build_success -> Plus

let gf3_conserved trits =
  let sum = List.fold_left (fun acc t ->
    acc + match t with Minus -> -1 | Ergodic -> 0 | Plus -> 1
  ) 0 trits in
  sum mod 3 = 0
```

## Canonical Triads

```
opam-ocaml (-1) ⊗ nickel (0) ⊗ geb (+1) = 0 ✓
opam-ocaml (-1) ⊗ lispsyntax-acset (0) ⊗ free-monad-gen (+1) = 0 ✓
```

## Non-Backtracking Geodesic Qualification

**Condition**: μ(n) ≠ 0 (Möbius squarefree)

This skill is qualified for non-backtracking geodesic traversal:

1. **Prime Path**: No state revisited in skill invocation chain
2. **Möbius Filter**: Composite paths (backtracking) cancel via μ-inversion
3. **GF(3) Conservation**: Trit sum ≡ 0 (mod 3) across skill triplets
4. **Spectral Gap**: Ramanujan bound λ₂ ≤ 2√(k-1) for k-regular expansion

```
Geodesic Invariant:
  ∀ path P: backtrack(P) = ∅ ⟹ μ(|P|) ≠ 0
  
Möbius Inversion:
  f(n) = Σ_{d|n} g(d) ⟹ g(n) = Σ_{d|n} μ(n/d) f(d)
```
