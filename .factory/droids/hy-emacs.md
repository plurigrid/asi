---
name: hy-emacs
description: Hylang Emacs integration with hy-mode, Hyuga LSP, and DisCoPy sexp coloring
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# hy-emacs - Hylang Emacs Integration

> **Trit**: 0 (ERGODIC - Coordinator)
>
> Complete Hy development environment for Emacs with LSP, REPL,
> and deterministic sexp coloring via Gay.jl patterns.

## Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                    Hy → Emacs → LSP Pipeline                    │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   .hy files                 Hyuga LSP              Gay.jl       │
│      │                         │                      │         │
│      ▼                         ▼                      ▼         │
│  ┌────────┐    ┌───────────────────────────┐    ┌──────────┐   │
│  │hy-mode │───▶│ completion, diagnostics,  │───▶│ rainbow  │   │
│  │ (MELPA)│    │ hover, go-to-definition   │    │ parens   │   │
│  └────────┘    └───────────────────────────┘    └──────────┘   │
│      │                         │                      │         │
│      │         jedhy           │                      │         │
│      ▼         (IDE)           ▼                      ▼         │
│  ┌────────┐    ┌───────────────────────────┐    ┌──────────┐   │
│  │hy-shell│───▶│ company-mode, eldoc-mode  │───▶│ depth→   │   │
│  │ (REPL) │    │ hy-describe-thing-at-pt   │    │ color    │   │
│  └────────┘    └───────────────────────────┘    └──────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## Triadic Structure

| Role | Component | Trit | Function |
|------|-----------|------|----------|
| **Validator** | slime-lisp | -1 | Common Lisp reference semantics |
| **Coordinator** | hy-emacs | 0 | Hy ↔ Python ↔ Emacs bridge |
| **Generator** | geiser-chicken | +1 | Scheme REPL with SplitMixTernary |

**GF(3) Conservation**: `slime-lisp (-1) ⊗ hy-emacs (0) ⊗ geiser-chicken (+1) = 0 ✓`

## Installation

### 1. Install