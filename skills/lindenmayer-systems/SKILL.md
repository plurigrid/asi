---
name: lindenmayer-systems
description: 'L-systems: parallel string rewriting for fractals, plants, and morphogenesis.'
trit: 1
bundle: strange-loops
metadata:
  interface_ports:
  - Related Skills
  - GF(3) Integration
---
# Lindenmayer Systems Skill

> *"All rules fire simultaneously. Growth is parallel."*

## Core Concept

L-systems are parallel rewriting systems where:
1. **Axiom** — initial string
2. **Rules** — character → replacement string
3. **Parallel application** — ALL rules fire at once each generation
4. **Turtle graphics** — interpret string as drawing commands

```
Axiom: A
Rules: A → AB
       B → A

Gen 0: A
Gen 1: AB
Gen 2: ABA
Gen 3: ABAAB
Gen 4: ABAABABA
```

## Why It's Strange

1. **Parallel** — not sequential substitution
2. **Deterministic chaos** — simple rules → complex structures
3. **Biological** — models plant growth
4. **Fractal** — self-similar at all scales

## Classic Examples

### Fibonacci Words
```
A → AB
B → A

Gen 0: A        (1)
Gen 1: AB       (2)
Gen 2: ABA      (3)
Gen 3: ABAAB    (5)
Gen 4: ABAABABA (8)

Lengths follow Fibonacci sequence!
```

### Koch Snowflake
```
Axiom: F
Rules: F → F+F--F+F

F = forward
+ = turn left 60°
- = turn right 60°
```

### Sierpinski Triangle
```
Axiom: F-G-G
Rules: F → F-G+F+G-F
       G → GG

F = forward (draw)
G = forward (draw)
+ = turn left 120°
- = turn right 120°
```

### Dragon Curve
```
Axiom: FX
Rules: X → X+YF+
       Y → -FX-Y

F = forward
+ = turn left 90°
- = turn right 90°
X, Y = no drawing (control)
```

## Turtle Graphics Interpretation

```
F  = Move forward, drawing line
f  = Move forward, no drawing
+  = Turn left by angle
-  = Turn right by angle
[  = Push position/angle to stack
]  = Pop position/angle from stack
|  = Turn 180°
```

## Stochastic L-Systems

```python
rules = {
    'F': [
        (0.5, 'F[+F]F[-F]F'),   # 50%
        (0.3, 'F[+F]F'),         # 30%
        (0.2, 'FF'),             # 20%
    ]
}
```

Each rule fires with probability. Creates natural variation.

## Parametric L-Systems

```
Axiom: A(1)
Rules: A(x) → F(x) [ +A(x*0.7) ] [ -A(x*0.7) ]

Parameters control:
- Line length (x)
- Branch angle
- Growth rate
```

## Context-Sensitive L-Systems

```
Axiom: baaaaaaaa
Rules:
  b < a → b     (a preceded by b becomes b)
  b → a         (isolated b becomes a)

Gen 0: baaaaaaaa
Gen 1: abaaaaaaa
Gen 2: aabaaaaaaa
Gen 3: aaabaaaaa  

Signal propagates!
```

## Implementation

```python
def lsystem(axiom: str, rules: dict, generations: int) -> str:
    """Apply L-system rules for n generations."""
    current = axiom
    
    for _ in range(generations):
        # PARALLEL: all substitutions at once
        next_gen = ""
        for char in current:
            next_gen += rules.get(char, char)
        current = next_gen
    
    return current

def turtle_draw(commands: str, angle: float = 90):
    """Interpret L-system string as turtle graphics."""
    import turtle
    stack = []
    
    for cmd in commands:
        if cmd == 'F':
            turtle.forward(10)
        elif cmd == 'f':
            turtle.penup()
            turtle.forward(10)
            turtle.pendown()
        elif cmd == '+':
            turtle.left(angle)
        elif cmd == '-':
            turtle.right(angle)
        elif cmd == '[':
            stack.append((turtle.pos(), turtle.heading()))
        elif cmd == ']':
            pos, heading = stack.pop()
            turtle.penup()
            turtle.setpos(pos)
            turtle.setheading(heading)
            turtle.pendown()

# Example: Fractal plant
axiom = "X"
rules = {
    'X': 'F+[[X]-X]-F[-FX]+X',
    'F': 'FF'
}
result = lsystem(axiom, rules, 6)
turtle_draw(result, 25)
```

## Famous L-Systems

| Name | Axiom | Rules | Angle |
|------|-------|-------|-------|
| **Koch** | F | F→F+F−F−F+F | 90° |
| **Sierpinski** | A | A→B−A−B, B→A+B+A | 60° |
| **Dragon** | FX | X→X+YF+, Y→−FX−Y | 90° |
| **Plant** | X | X→F+[[X]−X]−F[−FX]+X, F→FF | 25° |
| **Hilbert** | A | A→−BF+AFA+FB−, B→+AF−BFB−FA+ | 90° |

## D0L vs Other Types

| Type | Description |
|------|-------------|
| **D0L** | Deterministic, context-free |
| **S0L** | Stochastic, context-free |
| **IL** | Context-sensitive |
| **T0L** | Table (multiple rule sets) |
| **Parametric** | Rules with parameters |

## Music with L-Systems

```python
# Map symbols to notes
NOTE_MAP = {
    'A': 'C4',
    'B': 'E4', 
    'F': 'G4',
    '+': 'A4',
    '-': 'D4',
}

def lsystem_to_melody(lstring):
    return [NOTE_MAP.get(c, 'rest') for c in lstring]

# Fibonacci melody
axiom = "A"
rules = {'A': 'AB', 'B': 'A'}
fib_string = lsystem(axiom, rules, 7)
melody = lsystem_to_melody(fib_string)
# → Fibonacci-structured melody
```

## 3D L-Systems

```
&  = pitch down
^  = pitch up
\  = roll left
/  = roll right
|  = turn 180°

Used for realistic 3D plant models.
```

## Literature

1. **Lindenmayer (1968)** - "Mathematical Models for Cellular Interaction"
2. **Prusinkiewicz & Lindenmayer (1990)** - "The Algorithmic Beauty of Plants"
3. **Rozenberg & Salomaa (1980)** - "The Mathematical Theory of L Systems"

---

## End-of-Skill Interface

## GF(3) Integration

```python
# Assign trits to L-system symbols
SYMBOL_TRITS = {
    'F': 1,   # Growth (positive)
    '+': 0,   # Rotation (neutral)
    '-': 0,   # Rotation (neutral)
    '[': -1,  # Branch start (decrease depth)
    ']': 1,   # Branch end (increase to parent)
    'X': 0,   # Control (neutral)
}

def verify_gf3_conservation(rules):
    """Check if rules preserve GF(3) sum."""
    for lhs, rhs in rules.items():
        lhs_trit = SYMBOL_TRITS.get(lhs, 0)
        rhs_trit = sum(SYMBOL_TRITS.get(c, 0) for c in rhs)
        if lhs_trit % 3 != rhs_trit % 3:
            return False, (lhs, rhs)
    return True, None
```

## Related Skills

- `fractals` - Self-similar structures
- `generative-art` - Procedural generation
- `parallel-rewriting` - Grammar systems
- `morphogenesis` - Biological modeling
