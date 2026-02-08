---
name: lhott-cohesive-linear
description: Cohesive Linear HoTT patterns for interaction entropy with diagram generation. Implements Schreiber's cohesive modalities (♯,♭,ʃ) and Riley's linear modality (♮) for quantum-classical bridging.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# LHoTT Cohesive Linear Skill

Synthesizes Urs Schreiber's cohesive ∞-topos framework with Mitchell Riley's linear HoTT for interaction entropy formalization.

## Modal Operators

| Modality | Symbol | Action | Interaction Use |
|----------|--------|--------|-----------------|
| Sharp | ♯ | Discretize | Extract trit from color |
| Flat | ♭ | Embed continuously | Full LCH embedding |
| Shape | ʃ | Quotient by homotopy | Walk trajectory class |
| Linear | ♮ | Self-adjoint tangent | One-use interaction |

## GF(3) Triad Placement

This skill is **ERGODIC (0)**, forming triads with:

```
persistent-homology (-1) ⊗ lhott-cohesive-linear (0) ⊗ topos-generate (+1) = 0 ✓
sheaf-cohomology (-1) ⊗ lhott-cohesive-linear (0) ⊗ gay-mcp (+1) = 0 ✓
three-match (-1) ⊗ lhott-cohesive-linear (0) ⊗ rubato-composer (+1) = 0 ✓
```

## Core Types (Pseudo-HoTT)

```hott
-- Cohesive interaction type
CohesiveInteraction : Type
  content : String
  hash : ♯ SHA256           -- discrete
  seed : ♭ UInt64           -- continuous embedding
  color : ♮ LCH             -- linear (used once)
  position : ʃ (ℤ × ℤ)      -- shape-invariant

-- Linear function (no copy/delete)
walk_step : CohesiveInteraction ⊸ Position × Color

-- Bunched triplet (entangled context)
Γ₁ ⊗ Γ₂ ⊗ Γ₃ ⊢ conserved : GF3Zero
  where trit(Γ₁) + trit(Γ₂) + trit(Γ₃) ≡ 0 (mod 3)
```

## Diagram Generation

### Mermaid Templates

**Cohesive Quadruple:**
```mermaid
flowchart LR
    subgraph "Cohesive ∞-Topos H"
        A[Type] -->|ʃ shape| B[Shape Type]
        A -->|♭ flat| C[Codiscrete]
        C -->|Γ sections| D[Discrete]
        D -->|♯ sharp| A
    end
    style A fill:#26D826
    style B fill:#2626D8
    style C fill:#D82626
    style D fill:#2626D8
```

**Linear Walk:**
```mermaid
stateDiagram-v2
    [*] --> I1: seed₁
    I1 --> I2: ⊸ (linear)
    I2 --> I3: ⊸ (linear)
    I3 --> [*]: triplet complete
    
    note right of I1: trit = +1
    note right of I2: trit = 0
    note right of I3: trit = -1
```

**Bunched Context T