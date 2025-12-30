---
name: opam
description: OCaml package manager (45 subcommands).
metadata:
  trit: 0
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


## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: ⊗
Kan Role: Adj
Color: #26D826
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

This ensures compositional coherence in the Cat# equipment structure.
