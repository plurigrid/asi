---
name: rank-polymorphism
description: 'APL/BQN rank polymorphism: implicit iteration via array rank, no explicit
  loops.'
trit: 1
bundle: strange-loops
metadata:
  interface_ports:
  - Related Skills
  - GF(3) Integration
---
# Rank Polymorphism Skill

> *"Loops are for peasants. Rank is for kings."*

## Core Concept

In rank-polymorphic languages:
1. **Operations apply to arrays automatically**
2. **Rank** (number of dimensions) determines how operations distribute
3. **No explicit loops** — shape determines iteration
4. **Composition** replaces control flow

```apl
      1 2 3 + 10 20 30     ⍝ Vectorized: 11 22 33
      +/ 1 2 3 4           ⍝ Reduce: 10
      1 2 ∘.× 3 4 5        ⍝ Outer product: 2×3 matrix
```

## Why It's Strange

1. **No for-loops** — operations "just work" on any shape
2. **Rank as type** — scalar, vector, matrix, tensor treated uniformly
3. **Tacit programming** — point-free, no variable names
4. **Right-to-left** — `3×2+1` = `3×(2+1)` = 9

## APL Basics

```apl
⍝ Scalar extension
2 + 1 2 3          ⍝ → 3 4 5

⍝ Vector operations  
1 2 3 + 4 5 6      ⍝ → 5 7 9

⍝ Reduction
+/ 1 2 3 4         ⍝ → 10 (sum)
×/ 1 2 3 4         ⍝ → 24 (product)

⍝ Scan (cumulative)
+\ 1 2 3 4         ⍝ → 1 3 6 10

⍝ Outer product
1 2 ∘.× 3 4 5      ⍝ → 2×3 matrix: 3 4 5 / 6 8 10

⍝ Inner product
1 2 3 +.× 4 5 6    ⍝ → 1×4 + 2×5 + 3×6 = 32
```

## BQN (Modern APL)

```bqn
# Cleaner syntax, same ideas
+´ 1‿2‿3‿4         # Sum: 10
×˝ 2‿3⥊⟨1,2,3,4,5,6⟩  # Product of rows

# Rank operator (⎉)
+⎉1 mat            # Apply + to rank-1 cells (rows)

# Under (⌾) - apply, transform, unapply
10 ⌾(2⊸⊑) 1‿2‿3    # → 1‿10‿3 (modify at index 2)
```

## Rank Operator

The **rank operator** `⍤` (APL) or `⎉` (BQN) controls how functions distribute:

```apl
      f⍤0 ⍝ Apply to scalars (rank 0)
      f⍤1 ⍝ Apply to vectors (rank 1)  
      f⍤2 ⍝ Apply to matrices (rank 2)
```

Example:
```apl
      mat ← 3 4 ⍴ ⍳12       ⍝ 3×4 matrix
      +/⍤1 mat              ⍝ Sum each row: 10 26 42
      +/⍤2 mat              ⍝ Sum entire matrix: 78
```

## Leading Axis Theory

Arrays are organized by **leading axes**:
```
Shape: 2 3 4 5
       │ │ │ └─ Innermost (columns)
       │ │ └─── Third axis
       │ └───── Second axis (rows)
       └─────── Leading axis (frames)

Rank-1 cells: 5-vectors
Rank-2 cells: 4×5 matrices
Rank-3 cells: 3×4×5 cubes
```

## J Language

```j
   +/ 1 2 3 4           NB. 10
   */ 1 2 3 4           NB. 24
   1 2 */ 3 4 5         NB. Outer product
   
   NB. Tacit (point-free)
   mean =: +/ % #        NB. sum divided by count
   mean 1 2 3 4 5        NB. 3
```

## Implementation Strategy

```python
import numpy as np

def rank_apply(f, k, arr):
    """Apply f to rank-k cells of arr."""
    if arr.ndim <= k:
        return f(arr)
    
    # Split into cells, apply, recombine
    result = np.array([rank_apply(f, k, cell) for cell in arr])
    return result

# Example
mat = np.arange(12).reshape(3, 4)
row_sums = rank_apply(np.sum, 1, mat)  # Sum each row
```

## Key Combinators

| APL | BQN | J | Meaning |
|-----|-----|---|---------|
| `/` | `´` | `/` | Reduce (fold) |
| `\` | `` ` `` | `\` | Scan (cumulative) |
| `¨` | `¨` | `"0` | Each (map) |
| `∘.` | `⌜` | `*/` | Outer product |
| `⍤` | `⎉` | `"` | Rank |
| `⍥` | `○` | `&.:` | Under |
| `⍣` | `⍟` | `^:` | Power (iterate) |

## Example: Game of Life

```apl
⍝ APL Game of Life in one line
life ← {↑1 ⍵∨.∧3 4=+/,¯1 0 1∘.⊖¯1 0 1∘.⌽⊂⍵}
```

No loops! The neighbor sum and rule application happen via rank.

## Why No Loops?

```apl
⍝ Instead of:
⍝   for i in range(n):
⍝       for j in range(m):
⍝           result[i,j] = f(a[i], b[j])

⍝ Just write:
a ∘.f b            ⍝ Outer product

⍝ Instead of:
⍝   total = 0
⍝   for x in arr:
⍝       total += x

⍝ Just write:
+/ arr             ⍝ Reduce
```

## Literature

1. **Iverson (1962)** - "A Programming Language" (APL)
2. **Slepak et al. (2014)** - "An Array-Oriented Language with Static Rank Polymorphism"
3. **Hui & Iverson (2004)** - "J Dictionary"
4. **Marshall (2022)** - "BQN: An APL for the Present"

---

## End-of-Skill Interface

## GF(3) Integration

```python
# Trit arrays with rank polymorphism
import numpy as np

def gf3_sum(arr, axis=None):
    """Sum in GF(3) = sum mod 3."""
    return np.sum(arr, axis=axis) % 3

def gf3_reduce(f, arr, axis=None):
    """Reduce with GF(3) conservation check."""
    result = f(arr, axis=axis)
    # Verify conservation
    if (np.sum(arr) % 3) != (np.sum(result) % 3):
        raise ValueError("GF(3) not conserved!")
    return result

# Example: trit matrix
trits = np.array([[1, -1, 0], [0, 1, -1], [-1, 0, 1]])
row_sums = gf3_sum(trits, axis=1)  # [0, 0, 0] - each row balanced!
```

## Related Skills

- `numpy-broadcasting` - Python's limited version
- `einsum` - Einstein summation (tensor rank)
- `tacit-programming` - Point-free style
- `concatenative` - Also combinator-based
