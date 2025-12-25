---
name: ocaml
description: OCaml ecosystem = opam + dune + merlin + ocamlformat.
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
---

# ocaml

OCaml ecosystem = opam + dune + merlin + ocamlformat.

## Atomic Skills

| Skill | Commands | Domain |
|-------|----------|--------|
| opam | 45 | Package manager |
| dune | 20 | Build system |
| merlin | 1 | Editor support |
| ocamlformat | 1 | Formatter |

## Workflow

```bash
opam switch create 5.1.0
eval $(opam env)
opam install dune merlin
dune init project myapp
cd myapp
dune build
dune test
```

## dune-project

```lisp
(lang dune 3.0)
(name myapp)

(library
 (name mylib)
 (libraries str unix))

(executable
 (name main)
 (libraries mylib))
```

## REPL

```bash
utop
dune utop
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
