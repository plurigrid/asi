---
name: opam
description: OCaml package manager (45 subcommands).
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
---

# opam

OCaml package manager (45 subcommands).

## Install

```bash
opam install dune merlin
opam remove package
opam upgrade
```

## Switch

```bash
opam switch create 5.1.0
opam switch list
opam switch set 5.1.0
```

## Environment

```bash
eval $(opam env)
opam exec -- dune build
```

## Pin

```bash
opam pin add pkg ./local-path
opam pin add pkg git+https://...
opam pin remove pkg
```

## Repository

```bash
opam repo add name url
opam repo list
opam update
```

## Query

```bash
opam list --installed
opam show package
opam search term
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
