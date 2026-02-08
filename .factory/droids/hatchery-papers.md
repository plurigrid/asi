---
name: hatchery-papers
description: Chicken Scheme Hatchery eggs and academic papers for color logic, 2TDX,
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Hatchery & Papers: Research Resources

## Chicken Scheme Hatchery Eggs

Relevant eggs from http://wiki.call-cc.org/ and https://eggs.call-cc.org/:

### Core SRFIs (Built-in)

| SRFI | Name | Use |
|------|------|-----|
| SRFI-1 | List library | List operations |
| SRFI-4 | Homogeneous vectors | Color arrays |
| SRFI-9 | Records | Structured data |
| SRFI-18 | Multithreading | Parallel color streams |
| SRFI-27 | Random numbers | Base RNG |
| SRFI-69 | Hash tables | Color caching |

### SRFI-194: Random Data Generators (Final 2020)

```scheme
;; From SRFI-194
(import (srfi 194))

;; Custom generator for SplitMixTernary
(define (make-ternary-generator seed)
  (let ((rng (make-splitmix64 seed)))
    (lambda () (splitmix-ternary rng))))
```

### Math Egg

From https://wiki.call-cc.org/eggref/5/math:
- Random number generation
- Flonum operations
- Log-space arithmetic

```scheme
(import (math base))
(import (math flonum))
```

### Color/Graphics Eggs

| Egg | Description |
|-----|-------------|
| `colors` | Color space conversions |
| `cairo` | Vector graphics |
| `opengl` | 3D graphics |

## Academic Papers

### Colored Operads

1. **"Theta Theory: operads and coloring"** (Marcolli & Larson, 2025)
   - arXiv:2503.06091
   - Colored operad for theta theory
   - Coloring algorithm for syntactic objects
   - Merge operation with color filtering

2. **"On the homotopy theory of equivariant colored operads"** (Bonventre & Pereira, 2021)
   - arXiv:2004.01352
   - Model structures on equivariant operads
   - Weak equivalences by families of subgroups
   - Norm map data

3. **"Combinatorial Homotopy Theory for Operads"** (Obradović, 2019)
   - arXiv:1906.06260
   - Minimal model of colored operad O
   - Hypergraph polytopes
   - A∞-operad generalization

4. **"Operads: Hopf algebras and coloured Koszul duality"** (van der Laan, 2004)
   - Koszul duality for colored operads
   - Hopf algebra structure

### 2-Dimensional Type Theory / Higher Observational Type Theory

1. **"H