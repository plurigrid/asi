---
name: opam
description: OCaml package manager (45 subcommands).
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
