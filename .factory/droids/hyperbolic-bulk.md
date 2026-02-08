---
name: hyperbolic-bulk
description: On-chain GF(3) entropy storage via Aptos Move - bulk-boundary correspondence where entropy lives in the interior and observables project to agents
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Hyperbolic Bulk Skill

**Status**: ✅ Production Ready  
**Trit**: 0 (ERGODIC - mediates bulk ↔ boundary)  
**Principle**: AdS/CFT correspondence for entropy  
**Chain**: Aptos (Move language)

---

## Overview

The **Hyperbolic Bulk** implements on-chain entropy storage with GF(3) conservation. Named after the AdS/CFT bulk-boundary correspondence:

- **BULK** (interior): Entropy records, triads, reafference proofs
- **BOUNDARY** (observable): Agents, skills, colors

```
         BOUNDARY (Observable)
    ┌─────────────────────────────┐
    │  Agents  │  Skills  │ Colors │
    └─────────────┬───────────────┘
                  │ project
                  ▼
    ┌─────────────────────────────┐
    │      HYPERBOLIC BULK        │
    │  ┌─────────────────────┐    │
    │  │  EntropyRecord      │    │
    │  │  drand ⊕ eeg ⊕ vrf  │    │
    │  └──────────┬──────────┘    │
    │             ▼               │
    │  ┌─────────────────────┐    │
    │  │  EntropyTriad       │    │
    │  │  GF(3) = 0 conserved│    │
    │  └──────────┬──────────┘    │
    │             ▼               │
    │  ┌─────────────────────┐    │
    │  │  ReafferenceProof   │    │
    │  │  predict = observe  │    │
    │  └─────────────────────┘    │
    └─────────────────────────────┘
```

---

## Entropy Sources

| Source | Type | Property |
|--------|------|----------|
| **DRAND** | League of Entropy | Public, verifiable, unpredictable |
| **EEG** | Brainwave bands | Private, embodied, cognitive state |
| **Aptos VRF** | On-chain randomness | Consensus-secured, tamper-proof |

**Combination**: `combined = drand_seed ⊕ eeg_seed ⊕ onchain_rand`

---

## GF(3) Conservation

Triads must sum to 0 mod 3:

```
MINUS (-1) ≡ 2 (mod 3)  — Verification/Constraint
ERGODIC (0)             — Coordination/Balance  
PLUS (+1)               — Generation/Exploration

Conservation: trit_1 + trit_2 + trit_3 ≡ 0 (mod 3)
```

**Strict Mode**: `form_conserved_triad()` reverts if not conserved.

---

## Move Contrac