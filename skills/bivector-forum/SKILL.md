---
name: bivector-forum
description: "Community knowledge from bivector.net - GA tutorials, discussions, and best practices"
license: MIT
metadata:
  source: bivector.net + Discord
  trit: 0
  gf3_conserved: true
  version: 1.0.0
---

# bivector-forum

> Curated knowledge from the Geometric Algebra community

**Version**: 1.0.0  
**Trit**: 0 (ERGODIC - knowledge transport)

## Overview

[bivector.net](https://bivector.net/) is the primary community hub for Geometric Algebra practitioners. This skill distills key insights, common pitfalls, and best practices.

## Community Resources

| Resource | URL | Description |
|----------|-----|-------------|
| Forum | bivector.net | Discourse-based Q&A |
| Discord | discord.gg/bivector | Real-time chat |
| Wiki | bivector.net/wiki | Collaborative docs |
| GAlculator | enkimute.github.io/ganja.js/examples/galculator.html | Online calculator |

## Key Contributors

- **Steven De Keninck** (@enkimute) - ganja.js author
- **Leo Dorst** - "Geometric Algebra for Computer Science"
- **Charles Gunn** - PGA for graphics
- **Eric Lengyel** - Game engine applications

## Common Patterns

### 1. Choosing the Right Algebra

| Use Case | Algebra | Signature |
|----------|---------|-----------|
| 2D graphics | PGA2D | Cl(2,0,1) |
| 3D graphics | PGA3D | Cl(3,0,1) |
| Circles/spheres | CGA | Cl(n+1,1) |
| Rotations only | Quaternions | Cl(0,2) |
| Rigid body | Dual Quaternions | Cl(0,2,1) |
| Relativity | Spacetime | Cl(1,3) |

### 2. Dual vs Homogeneous

**PGA (Projective)**: Points are bivectors, planes are vectors
- Pro: Unified treatment of points at infinity
- Con: Counterintuitive grading

**CGA (Conformal)**: Points are null vectors
- Pro: Circles/spheres as blades
- Con: Higher dimensional, slower

### 3. Sign Conventions

Different sources use different conventions:

| Convention | e₀² | Point Encoding |
|------------|-----|----------------|
| "Mathematics" | 0 | e₁₂₃ + xe₀₂₃ + ye₀₁₃ + ze₀₁₂ |
| "Engineering" | 0 | e₁₂₃ - xe₀₂₃ + ye₀₁₃ - ze₀₁₂ |
| ganja.js | 0 | 1e123 - x*1e023 + y*1e013 - z*1e012 |

### 4. Normalization

Always normalize motors/rotors after composition:

```javascript
// WRONG: Drift over time
for (let i = 0; i < 1000; i++) {
  motor = motor.Mul(smallRotor);  // Accumulates error
}

// RIGHT: Normalize periodically
for (let i = 0; i < 1000; i++) {
  motor = motor.Mul(smallRotor);
  if (i % 100 === 0) motor = motor.Normalized;
}
```

### 5. Avoiding Common Pitfalls

#### Pitfall: Wrong Product

```javascript
// WRONG: Using geometric product for join
var line = pointA * pointB;  // Gives rotor, not line!

// RIGHT: Use regressive product
var line = pointA & pointB;  // Vee = join
```

#### Pitfall: Forgetting Reverse

```javascript
// WRONG: Missing reverse in sandwich
var transformed = motor * point;  // Only half the sandwich!

// RIGHT: Full sandwich
var transformed = motor * point * ~motor;
// Or use >>> operator
var transformed = motor >>> point;
```

#### Pitfall: Grade Extraction

```javascript
// WRONG: Assuming grade by position
var scalar = result[0];  // May not be scalar!

// RIGHT: Use grade projection
var scalar = result.Grade(0);
var bivector = result.Grade(2);
```

## Frequently Asked Questions

### Q: PGA or CGA?

**A**: Start with PGA. It's simpler, faster, and covers most needs. Use CGA only when you need circles/spheres as first-class objects.

### Q: Why are my transformations wrong?

**A**: Check:
1. Motor normalization
2. Sandwich product (both sides)
3. Transformation order (right-to-left)
4. Sign conventions

### Q: How to debug multivector issues?

**A**: 
1. Use `console.log(mv.toString())` in ganja.js
2. Check grade with `mv.Grade(k).Length`
3. Verify normalization with `mv.Mul(mv.Reverse).s`

### Q: Performance tips?

**A**:
1. Cache computed motors
2. Use specialized rotors/translators
3. Avoid repeated normalization
4. Pre-compute inverse when possible

## GAlculator Tips

The online [GAlculator](https://enkimute.github.io/ganja.js/examples/galculator.html) is great for:
- Quick experiments
- Verifying formulas
- Learning GA intuitively

```
// Example session
> 1e1 * 1e2
= 1e12

> (1e1 + 1e2).Normalized
= 0.707e1 + 0.707e2

> (1 + 0.5e12).Exp()
= 0.878 + 0.479e12
```

## Integration with Skills Ecosystem

### From bivector.net → Skills

| Forum Topic | Related Skill |
|-------------|---------------|
| "PGA for beginners" | `ganja-wedge-game` |
| "Motor interpolation" | `pga-motor-interpolation` |
| "CGA circles" | `conformal-ga` |
| "Visualization tips" | `ga-visualization` |
| "Code generation" | `ga-codegen` |

### GF(3) Conservation

Community discussions often naturally balance:
- Questions (-1): Seeking understanding
- Answers (0): Sharing knowledge
- Examples (+1): Generating new applications

## Discord Bot Commands

```
!algebra PGA3D     - Show algebra info
!product a b       - Compute geometric product
!explain wedge     - Explain wedge product
!example rotation  - Show rotation example
```

## GF(3) Triads

```
bivector-forum (0) ⊗ ganja-wedge-game (+1) ⊗ conformal-ga (-1) = 0 ✓
bivector-forum (0) ⊗ ga-codegen (+1) ⊗ sheaf-cohomology (-1) = 0 ✓
```

## Commands

```bash
# Open forum
open https://bivector.net/

# Open Discord
open https://discord.gg/vGY6pPk

# Open GAlculator
open https://enkimute.github.io/ganja.js/examples/galculator.html
```

## References

- [bivector.net](https://bivector.net/)
- [GA primer (Dorst)](https://geometricalgebra.org/downloads/PrimerGeometricAlgebra.pdf)
- [PGA cheat sheet](https://bivector.net/PGA3D.html)
- [ganja.js documentation](https://github.com/enkimute/ganja.js/wiki)


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
