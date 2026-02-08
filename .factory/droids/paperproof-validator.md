---
name: paperproof-validator
description: Formal Proof Visualization and Verification for Lean 4
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# paperproof-validator

> Formal Proof Visualization and Verification for Lean 4

**Version**: 1.0.0
**Trit**: -1 (Validator - verifies proof correctness)
**Bundle**: verification
**Status**: ✅ New (Lean 4 theorem proof visualization)
**Repository**: [Paper-Proof/paperproof](https://github.com/Paper-Proof/paperproof)

---

## Overview

**Paperproof Validator** transforms formal Lean 4 proofs into intuitive, paper-like visualizations. It bridges the gap between abstract formal proofs and human understanding by displaying how hypotheses and goals evolve throughout a proof.

**Key Innovation**: Makes formal proofs accessible by visualizing proof structure in a way that mirrors mathematical notation on paper.

### What Paperproof Does

Instead of abstract Lean code:
```lean
theorem example : P → Q := by
  intro h
  apply some_lemma
  exact h.right
```

Paperproof shows:
```
┌─────────────────────────────────────┐
│ Hypotheses (green nodes):           │
│  - h : P                            │
├─────────────────────────────────────┤
│ Goal (red node):                    │
│  - Q                                │
├─────────────────────────────────────┤
│ Tactics (transparent):              │
│  - apply some_lemma                 │
│  - exact h.right                    │
└─────────────────────────────────────┘
```

---

## Architecture

### Three Core Components

#### 1. **Lean 4 Library Integration**

```lean
import Paperproof

theorem my_theorem : P ∧ Q → R := by
  -- Paperproof automatically extracts proof state
  intro ⟨hp, hq⟩
  -- Visualization tracks hypotheses and goals
  exact some_proof_term
```

**Capabilities**:
- Integrates with Lean 4 InfoTree
- Extracts proof state at each tactic
- Provides proof metadata to VS Code extension

---

#### 2. **VS Code Extension**

**Responsibilities**:
- Tracks cursor position (detects which theorem is being visualized)
- Communicates with Lean server for proof data
- Hosts webview panel for visualization
- Provides commands and