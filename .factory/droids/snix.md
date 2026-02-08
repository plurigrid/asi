---
name: snix
description: Rust Nix reimplementation for content-addressed rootfs builds. Minimal VM images for boxxy/codex-rs/toad agent runtimes.
model: inherit
tools: read-only
---

# snix Skill

> *"Nix, reimplemented in Rust."* -- snix.dev

> **Trit**: -1 (MINUS) - Build validation and rootfs construction

## Overview

**snix** is a Rust reimplementation of Nix (forked from Tvix) with a bytecode VM evaluator, content-addressed store, and library-oriented architecture. It provides the build layer for the Minimum Viable Runtime (MVR) — creating minimal Linux rootfs images that run AI agent TUIs inside boxxy (Apple Virtualization.framework) VMs.

```
┌─────────────────────────────────────────────────────┐
│                    snix BUILD LAYER                  │
│              (content-addressed store)              │
└──────────────────────┬──────────────────────────────┘
                       │
       ┌───────────────┼───────────────┐
       │               │               │
┌──────▼──────┐ ┌──────▼──────┐ ┌──────▼──────┐
│  Evaluate   │ │   Build     │ │   Store     │
│  (bytecode) │ │   (daemon)  │ │   (CAS)     │
│  trit: -1   │ │   trit: 0   │ │   trit: +1  │
└─────────────┘ └─────────────┘ └─────────────┘
       │               │               │
       └───────────────┼───────────────┘
                       │
               ┌───────▼───────┐
               │   rootfs.img  │
               │   (~75-130MB) │
               └───────────────┘
```

## Why snix

| Property | Nix (C++) | snix (Rust) |
|----------|-----------|-------------|
| Language | C++ | Rust |
| Evaluator | AST walker | Bytecode VM |
| Store | Monolithic | Content-addressed, granular |
| Library use | CLI only | Library-first |
| License | LGPL-2.1 | GPL-3.0 |
| macOS CI | Community | Dedicated |
| nixpkgs compat | Native | Yes (growing) |

- Pure Rust embeds into boxxy's Go/Rust toolchain without C++ dependency
- Bytecode VM evaluator is faster than Nix's AST walker
- Content-addressed store enables deduped, granular rootfs images
- Library-oriented — callable from Rust code, not just CLI
- [Fork of Tvix](https://snix.dev/blog/announcing-snix/) with dedicated CI and macOS 