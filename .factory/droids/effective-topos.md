---
name: effective-topos
description: FloxHub publication `bmorphism/effective-topos` - a comprehensive development
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# effective-topos

FloxHub publication `bmorphism/effective-topos` - a comprehensive development environment with 606 man pages, 97 Emacs info manuals, and deep integration across Scheme (Guile/Goblins/Hoot), functional languages (OCaml, Haskell, Racket), systems tools (Rust, Go), and Gay.jl deterministic coloring.

## Interleaving Index

This skill interconnects:
- **Man pages**: 606 command-line tool references
- **Info manuals**: 97 Emacs/Guile/GNU texinfo documents (278K+ lines)
- **Gay.jl colors**: Deterministic seed-based coloring for all tools

### Triadic Tool Categories (GF(3) = {0,1,2})

| Trit | Domain | Tools | Info Manuals |
|------|--------|-------|--------------|
| **0** | Lisp/Scheme | guile, racket, emacs, elisp | guile.info, elisp.info, goblins.info, hoot.info, r5rs.info |
| **1** | ML/Functional | ocaml, ghc, cabal, opam, agda | - |
| **2** | Systems/DevOps | cargo, gh, tmux, radare2, just | autoconf.info, libtool.info, m4.info |

---

## Quick Activation

```bash
# Pull from FloxHub
flox pull bmorphism/effective-topos

# Activate
flox activate -d ~/.topos

# Access man pages
man gh
man cargo
man opam

# Access info docs (in Emacs)
C-h i  # then select manual
```

## Installed Packages (62)

### Development Languages
| Package | Description | Man Pages |
|---------|-------------|-----------|
| ghc | Glasgow Haskell Compiler | ghc(1), 3226 lines |
| cabal-install | Haskell build tool | cabal(1), 41536 lines |
| ocaml | OCaml compiler | ocaml(1), ocamlopt(1), ... |
| opam | OCaml package manager | opam(1) + 45 subcommands |
| racket-minimal | Racket language | racket(1) |
| guile | GNU Scheme | guile(1) + guile.info (67K lines) |
| guile-hoot | Scheme→WebAssembly | hoot.info (4K lines) |
| guile-goblins | Actor model | goblins.info (6.5K lines) |
| agda | Dependent types | - |
| dart | Dart language | dart(1) |
| go | Go language | go(1) |
| cargo | Rust package manager | cargo(1) + 36 subcommands |
| clang | C/C++ compiler | clang(1) |

### Emacs E