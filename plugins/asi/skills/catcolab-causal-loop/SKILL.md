---
name: catcolab-causal-loop
description: CatColab Causal Loop Diagrams - systems dynamics modeling with reinforcing (R) and balancing (B) feedback loops, delays, and Lotka-Volterra semantics for strategic analysis.
version: 1.0.0
---

# CatColab Causal Loop Diagrams: Systems Dynamics

**Trit**: 0 (ERGODIC - coordinator/mediator)
**Color**: Yellow (#FFD700)

## Overview

Causal Loop Diagrams (CLDs) in CatColab model feedback systems:
- **Variables**: System quantities that change over time
- **Positive links (+)**: Same-direction influence (increase→increase)
- **Negative links (-)**: Opposite-direction influence (increase→decrease)
- **Loops**: Reinforcing (R) or Balancing (B) feedback

CLDs are essential for understanding system behavior, policy analysis, and strategic planning.

## Mathematical Foundation

A causal loop diagram is a **signed directed graph** with loop classification:

```
┌─────────────────────────────────────────────────────┐
│            CAUSAL LOOP DIAGRAM                       │
├─────────────────────────────────────────────────────┤
│  Variables:                                          │
│    Population, Resources, Pollution, Quality         │
│                                                      │
│  Positive Links (+):                                 │
│    Population ──(+)──► Pollution                     │
│    Resources ──(+)──► Quality                        │
│                                                      │
│  Negative Links (-):                                 │
│    Pollution ──(-)──► Quality                        │
│    Quality ──(-)──► Population (emigration)          │
│                                                      │
│  Loops:                                              │
│    R1: Population→Births→Population (reinforcing)    │
│    B1: Population→Resources→Quality→Pop (balancing)  │
└─────────────────────────────────────────────────────┘
```

## Loop Classification

**Reinforcing Loop (R)**: Even number of negative links
- Exponential growth or collapse
- "Snowball effect" or "vicious/virtuous cycle"

**Balancing Loop (B)**: Odd number of negative links
- Goal-seeking behavior
- Homeostasis, equilibrium

```
REINFORCING (R):              BALANCING (B):
   A ──(+)──► B                  A ──(+)──► B
   ▲          │                  ▲          │
   │          │                  │          │
   └──(+)─────┘                  └──(-)─────┘
   (exponential)                 (equilibrium)
```

## Double Theory

```rust
// Causal loop double theory with decorated edges
pub fn th_causal_loop() -> DiscreteDblTheory {
    let mut cat = FpCategory::new();

    // Object type
    cat.add_ob_generator(name("Variable"));

    // Morphism types (polarized links)
    cat.add_mor_generator(name("Positive"), name("Variable"), name("Variable"));
    cat.add_mor_generator(name("Negative"), name("Variable"), name("Variable"));

    // Decorations (CatColab 0.2)
    cat.add_mor_generator(name("Delay"), name("Variable"), name("Variable"));
    cat.add_mor_generator(name("Indeterminate"), name("Variable"), name("Variable"));

    cat.into()
}
```

## CatColab Implementation

### Variable Declaration

```typescript
{
  "type": "ObDecl",
  "name": "MarketShare",
  "theory_type": "Variable",
  "description": "company's percentage of total market"
}
```

### Positive Link

```typescript
{
  "type": "MorDecl",
  "name": "growth_effect",
  "dom": "MarketShare",
  "cod": "Revenue",
  "theory_type": "Positive",
  "description": "higher market share increases revenue"
}
```

### Negative Link

```typescript
{
  "type": "MorDecl",
  "name": "saturation_effect",
  "dom": "MarketShare",
  "cod": "GrowthRate",
  "theory_type": "Negative",
  "description": "higher share reduces growth potential"
}
```

### Delay (CatColab 0.2)

```typescript
{
  "type": "MorDecl",
  "name": "investment_lag",
  "dom": "RnD_Spending",
  "cod": "ProductQuality",
  "theory_type": "Delay",
  "delay_time": 12,  // months
  "description": "R&D takes time to improve products"
}
```

## Lotka-Volterra Semantics

CatColab generates **Lotka-Volterra ODEs** from causal loops:

```
For variables X, Y with positive link X→Y:
  dY/dt = α·X·Y

For negative link X→Y:
  dY/dt = -β·X·Y

General form:
  dXᵢ/dt = Xᵢ · Σⱼ aᵢⱼ·Xⱼ
```

## Practical Examples

### Example 1: Adoption Dynamics

```
     Word of Mouth
          ↗ (+)
    Users ────────► Adoption Rate
      ▲                 │
      │                 │
      └────(+)──────────┘
           R1: Viral Growth

    Adoption Rate ──(+)──► Users
         │
         └──(-)──► Potential Users
                       │
              B1: Market Saturation
```

### Example 2: Thermostat (Balancing)

```
    Desired Temp ──(+)──► Gap
         ▲                 │
         │                 │
         │                (+)
         │                 ▼
    Actual Temp ◄──(+)── Heating
         │
         └──(-)──► Gap
              B1: Temperature Control
```

### Example 3: Arms Race (Reinforcing)

```
    Country A Arms ──(+)──► Country A Threat Perception
           ▲                        │
           │                       (+)
           │                        ▼
    Country B Arms ◄──(+)── Country B Arms Spending
           │
           └──(+)──► Country A Threat Perception
                R1: Escalation Spiral
```

## Analysis Capabilities

- **Loop identification**: Automatic detection of R and B loops
- **Dominant loop analysis**: Which loops drive behavior
- **Policy leverage points**: Where interventions are most effective
- **Scenario simulation**: Lotka-Volterra dynamics

## GF(3) Triads

```
catcolab-regulatory-networks (-1) ⊗ catcolab-causal-loop (0) ⊗ catcolab-stock-flow (+1) = 0 ✓
open-games (-1) ⊗ catcolab-causal-loop (0) ⊗ dynamical-system-functor (+1) = 0 ✓
```

## Commands

```bash
# Create causal loop diagram
just catcolab-new causal-loop "market-dynamics"

# Identify all loops
just catcolab-analyze market-dynamics --loops

# Simulate Lotka-Volterra
just catcolab-simulate market-dynamics --lotka-volterra

# Export to Vensim format
just catcolab-export market-dynamics --format=mdl
```

## References

- Sterman (2000) "Business Dynamics: Systems Thinking and Modeling"
- Meadows (2008) "Thinking in Systems"
- [CatColab Causal Loop Help](https://catcolab.org/help/logics/causal-loop)

---

**Skill Name**: catcolab-causal-loop
**Type**: Systems Dynamics / Feedback Analysis
**Trit**: 0 (ERGODIC)
**GF(3)**: Conserved via triadic composition
