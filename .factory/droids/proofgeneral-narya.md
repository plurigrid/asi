---
name: proofgeneral-narya
description: "Proof General + Narya: Higher-dimensional type theory proof assistant with observational bridge types for version control."
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# ProofGeneral + Narya Skill

> *"Observational type theory: where equality is what you can observe, not what you can prove."*

## bmorphism Contributions

> *"universal topos construction for social cognition and democratization of mathematical approach to problem-solving to all"*
> — [Plurigrid: the story thus far](https://gist.github.com/bmorphism/a400e174b9f93db299558a6986be0310)

**Active Inference via String Diagrams**: Narya's observational bridge types connect to the [Active Inference in String Diagrams](https://arxiv.org/abs/2308.00861) framework where perception and action form bidirectional loops. The bridge types implement:
- **Reafference** (self-caused) → observationally equivalent paths
- **Exafference** (externally-caused) → bridge types with non-trivial structure

**Narya Reference** (from hatchery-papers):
- GitHub: https://github.com/mikeshulman/narya (225+ stars)
- Higher observational type theory proof assistant
- Interval-free, dimension-aware type checking

## Overview

This skill combines:
- **Proof General** (543⭐): The universal Emacs interface for proof assistants
- **Narya** (225⭐): Higher-dimensional type theory proof assistant

## Proof General Basics

```elisp
;; Install via straight.el or package.el
(use-package proof-general
  :mode ("\\.v\\'" . coq-mode)
  :config
  (setq proof-splash-enable nil
        proof-three-window-mode-policy 'hybrid))
```

### Key Bindings

| Key | Action | Description |
|-----|--------|-------------|
| `C-c C-n` | `proof-assert-next-command-interactive` | Step forward |
| `C-c C-u` | `proof-undo-last-successful-command` | Step backward |
| `C-c C-RET` | `proof-goto-point` | Process to cursor |
| `C-c C-b` | `proof-process-buffer` | Process entire buffer |
| `C-c C-.` | `proof-goto-end-of-locked` | Jump to locked region end |

### Proof State Visualization

```
┌─────────────────────────────────────────────────────────────┐
│  ████████████████████░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░  │
│  ▲ Locked (proven) 