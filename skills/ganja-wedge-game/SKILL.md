---
name: ganja-wedge-game
description: "Geometric Algebra game mechanics via ganja.js with implicit player skills for wedge/vee/dot operations"
license: MIT
metadata:
  source: enkimute/ganja.js + open-games + unwiring-arena
  trit: +1
  gf3_conserved: true
  version: 1.0.0
---

# ganja-wedge-game

> Compositional game theory meets Geometric Algebra via ganja.js

**Version**: 1.0.0  
**Trit**: +1 (PLUS - generative/extension)  
**Color**: #8F8 (from wedge game UI)

## Overview

The [Wedge Game](https://enkimute.github.io/ganja.js/examples/example_game_wedge.html) by Steven De Keninck teaches Projective Geometric Algebra (PGA) through direct manipulation. This skill extracts its **implicit player mechanics** and maps them to compositional game theory.

## Core Algebra: PGA2D = Cl(2,0,1)

```javascript
var PGA2D = Algebra(2,0,1);  // 2 positive, 0 negative, 1 zero dimension

// Basis: 1, e0, e1, e2, e01, e02, e12, e012
// Metric: e0²=0, e1²=1, e2²=1

// Points are bivectors (grade 2)
var point = (x,y) => 1e12 - x*1e01 + y*1e02;

// Lines are vectors (grade 1)  
var line = (a,b,c) => a*1e1 + b*1e2 + c*1e0;
```

## Game Operations as Player Skills

### Skill 1: Join (∧ Wedge for Points → Lines)

```
Drag points APART → Join them into a line

P₁ & P₂ = P₁ ∨ P₂ (regressive product = dual of wedge of duals)
```

| Property | Value |
|----------|-------|
| Input | Two points (bivectors) |
| Output | One line (vector) |
| Grade Change | 2 + 2 → 1 (via duality) |
| GF(3) Trit | +1 (extension) |

### Skill 2: Meet (∧ Wedge for Lines → Points)

```
Drag lines TOGETHER → Meet them at a point

l₁ ^ l₂ = l₁ ∧ l₂ (exterior product)
```

| Property | Value |
|----------|-------|
| Input | Two lines (vectors) |
| Output | One point (bivector) |
| Grade Change | 1 + 1 → 2 |
| GF(3) Trit | +1 (extension) |

### Skill 3: Add (+ When Same Grade)

```
Drag same-type elements in SAME direction → Add them

P₁ + P₂ (point addition)
l₁ + l₂ (line addition)
```

| Property | Value |
|----------|-------|
| Input | Two elements of same grade |
| Output | One element of same grade |
| Grade Change | k → k (preserved) |
| GF(3) Trit | 0 (ergodic) |

### Skill 4: Dot (· Contraction)

```
HOLD a point, drag a line TO it → Project line through point

l << P = l · P (left contraction)
```

| Property | Value |
|----------|-------|
| Input | One line + one point (held) |
| Output | Perpendicular line through point |
| Grade Change | 1 + 2 → 1 |
| GF(3) Trit | -1 (contraction) |

## Grade ↔ Trit Mapping

| GA Grade | GF(3) Trit | Operation | Game Gesture |
|----------|------------|-----------|--------------|
| k+1 | +1 (PLUS) | Wedge (∧) | Drag together/apart |
| k | 0 (ERGODIC) | Add (+) | Same direction drag |
| k-1 | -1 (MINUS) | Dot (·) | Hold + drag to |

## Implicit Player Skills (What Players Learn)

### Level 1: Incidence
- Points lie on lines (bivector ∧ vector = 0 test)
- Lines pass through points (same test, dual view)

### Level 2: Construction
- Orthocenter: `((A&B)<<C) ^ ((B&C)<<A)`
- Circumcenter: `((A&B)<<(A+B)) ^ ((B&C)<<(B+C))`
- Euler line: `orthocenter & circumcenter`

### Level 3: Transformations (Not in basic game)
- Rotors: `cos(θ/2) + sin(θ/2)*bivector`
- Translators: `1 + 0.5*ideal_line`

## Open Games Mapping

From [open-games](file:///Users/bob/iii/r2con-integration/skills/open-games/SKILL.md) and [unwiring-arena](file:///Users/bob/iii/r2con-integration/skills/unwiring-arena/SKILL.md):

```haskell
-- Wedge Game as Open Game
WedgeGame : Lens_{(Ω,℧)}(State, Costate)

where:
  Ω = Strategy profiles (drag gestures)
  ℧ = Reward vectors (score: 1000 - time/1000 - moves*10)
  State = Current level elements
  Costate = Target (red) elements
```

### Play/Coplay Structure

```javascript
// Play: Forward pass (player action)
play: (gesture, state) => {
  if (gesture.type === 'apart') return state.Vee(target);  // Join
  if (gesture.type === 'together') return state.Wedge(target);  // Meet
  if (gesture.type === 'hold+drag') return state.Dot(target);  // Project
  return state.Add(target);  // Add
}

// Coplay: Backward pass (score feedback)
coplay: (gesture, state, reward) => {
  // Check if result matches required (red) elements
  const match = required.some(r => 
    state.Sub(r).Length < 0.01 || state.Add(r).Length < 0.01
  );
  return match ? reward + 100 : reward - 10;
}
```

## Arena Protocol Integration

```json
{
  "arena_id": "wedge-game-pga2d",
  "seed": 1069,
  "players": [
    {
      "id": "student",
      "trit": 0,
      "skills": ["join", "meet", "add", "dot"]
    }
  ],
  "channels": {
    "play": "gesture → element construction",
    "coplay": "score → skill reinforcement"
  }
}
```

## Dependencies

| Dependency | Role | Skill |
|------------|------|-------|
| ganja.js | GA runtime | (external) |
| PGA2D | Algebra instance | `Algebra(2,0,1)` |
| open-games | Game semantics | `open-games` |
| unwiring-arena | Arena protocol | `unwiring-arena` |
| gay-mcp | Color generation | `gay-mcp` |

## GF(3) Triads

```
open-games (-1) ⊗ ganja-wedge-game (+1) ⊗ bisimulation-game (0) = 0 ✓
unwiring-arena (0) ⊗ ganja-wedge-game (+1) ⊗ temporal-coalgebra (-1) = 0 ✓
```

## Implementation Sketch

```javascript
// ganja.js Wedge Game with Open Game semantics
Algebra(2,0,1, function() {
  const origin = 1e12, EX = -1e02, EY = 1e01;
  
  // Player skill interface
  class PlayerSkill {
    constructor(name, trit, operation) {
      this.name = name;
      this.trit = trit;  // GF(3): -1, 0, +1
      this.operation = operation;
    }
    
    apply(a, b) {
      return this.operation(a, b);
    }
  }
  
  // Implicit skills from gesture detection
  const skills = {
    join: new PlayerSkill('join', +1, (a,b) => a.Vee(b)),
    meet: new PlayerSkill('meet', +1, (a,b) => a.Wedge(b)),
    add:  new PlayerSkill('add',  0,  (a,b) => a.Add(b)),
    dot:  new PlayerSkill('dot', -1,  (a,b) => a.Dot(b))
  };
  
  // Gesture → Skill mapping (from wedge_game.html)
  function detectSkill(gesture, selection) {
    const [a, b] = selection;
    const apart = gesture.direction === 'divergent';
    const together = gesture.direction === 'convergent';
    const held = gesture.held !== null;
    
    if (apart && a.grade === 2 && b.grade === 2) return skills.join;
    if (together && a.grade === 1 && b.grade === 1) return skills.meet;
    if (held) return skills.dot;
    return skills.add;
  }
  
  // Score function (from wedge game)
  function score(moves, timeMs) {
    return 1000 - timeMs/1000 - moves*10;
  }
  
  return { skills, detectSkill, score };
});
```

## Levels as Skill Progression

| Level | Concept | Skills Used | GF(3) Sum |
|-------|---------|-------------|-----------|
| 1 | Join two points | join (+1) | +1 |
| 2 | Meet two lines | meet (+1) | +1 |
| 3 | Add points | add (0) | 0 |
| 4 | Add lines | add (0) | 0 |
| 5 | Dot (project) | dot (-1) | -1 |
| 6-14 | Composite | mixed | 0 (balanced) |

## Commands

```bash
# Open wedge game in browser
open https://enkimute.github.io/ganja.js/examples/example_game_wedge.html

# Run local ganja.js
npm install ganja.js

# Julia equivalent via Grassmann.jl
julia -e 'using Grassmann; @basis ℝ^(2,0,1)'
```

## References

- [ganja.js GitHub](https://github.com/enkimute/ganja.js) - Steven De Keninck
- [Wedge Game](https://enkimute.github.io/ganja.js/examples/example_game_wedge.html)
- [bivector.net](https://bivector.net/) - GA community
- [Ganja.jl](https://github.com/chakravala/Ganja.jl) - Julia interface
- [Grassmann.jl](https://github.com/chakravala/Grassmann.jl) - Native Julia GA


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
