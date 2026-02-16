---
name: ga-codegen
description: "Geometric Algebra code generation for C++, C#, Rust, Python from ganja.js templates"
license: MIT
metadata:
  source: ganja.js/codegen
  trit: +1
  gf3_conserved: true
  version: 1.0.0
---

# ga-codegen

> Generate Clifford Algebra implementations for any language from ganja.js

**Version**: 1.0.0  
**Trit**: +1 (PLUS - generative)

## Overview

ganja.js includes a **template-based code generator** that produces optimized Geometric Algebra implementations for:
- C++ (header-only)
- C# (.NET)
- Rust (no-std compatible)
- Python (numpy-based)

## Supported Algebras

Pre-generated algebras in `ganja.js/codegen/`:

| Algebra | Signature | File Pattern |
|---------|-----------|--------------|
| R2 | Cl(2,0,0) | `R2.{cpp,cs,rs,py}` |
| R3 | Cl(3,0,0) | `R3.{cpp,cs,rs,py}` |
| R4 | Cl(4,0,0) | `R4.{cpp,cs,rs,py}` |
| PGA2D | Cl(2,0,1) | `PGA2D.{cpp,cs,rs,py}` |
| PGA3D | Cl(3,0,1) | `PGA3D.{cpp,cs,rs,py}` |
| CGA2D | Cl(3,1,0) | `CGA2D.{cpp,cs,rs,py}` |
| CGA3D | Cl(4,1,0) | `CGA3D.{cpp,cs,rs,py}` |
| Quaternions | Cl(0,2,0) | `H.{cpp,cs,rs,py}` |
| Dual Quaternions | Cl(0,2,1) | `DQ.{cpp,cs,rs,py}` |

## Code Structure

Each generated file contains:

```cpp
// C++ Example: PGA3D.cpp
namespace PGA3D {
  
  // Multivector with flat storage
  struct Multivector {
    float data[16];  // 2^4 components
    
    // Constructors
    static Multivector scalar(float s);
    static Multivector vector(float e1, float e2, float e3, float e0);
    static Multivector bivector(...);
    
    // Products
    Multivector operator*(const Multivector& b) const;  // Geometric
    Multivector operator^(const Multivector& b) const;  // Wedge
    Multivector operator|(const Multivector& b) const;  // Dot
    Multivector operator&(const Multivector& b) const;  // Vee
    
    // Involutions
    Multivector reverse() const;
    Multivector conjugate() const;
    Multivector dual() const;
    
    // Transformations
    Multivector sandwich(const Multivector& v) const;
    Multivector exp() const;
    Multivector log() const;
  };
  
  // Helper constructors
  Multivector point(float x, float y, float z);
  Multivector line(float px, float py, float pz, float dx, float dy, float dz);
  Multivector plane(float a, float b, float c, float d);
  Multivector rotor(float angle, Multivector axis);
  Multivector translator(float dist, Multivector dir);
}
```

## Rust Implementation

```rust
// PGA3D.rs
#![no_std]

#[derive(Clone, Copy, Debug)]
pub struct Multivector([f32; 16]);

impl Multivector {
    pub const fn zero() -> Self { Self([0.0; 16]) }
    pub const fn scalar(s: f32) -> Self { 
        let mut m = [0.0; 16]; m[0] = s; Self(m) 
    }
    
    // Geometric product - generated multiplication table
    pub fn mul(&self, b: &Self) -> Self {
        let mut res = [0.0; 16];
        // Generated from Cayley table
        res[0] = self.0[0]*b.0[0] + self.0[1]*b.0[1] + ...;
        // ... 16 lines of optimized multiplications
        Self(res)
    }
    
    pub fn wedge(&self, b: &Self) -> Self { ... }
    pub fn dot(&self, b: &Self) -> Self { ... }
    pub fn dual(&self) -> Self { ... }
    pub fn reverse(&self) -> Self { ... }
    
    pub fn exp(&self) -> Self {
        // Closed-form for bivectors
        let theta = self.norm();
        if theta < 1e-6 {
            return Self::scalar(1.0).add(&self);
        }
        Self::scalar(theta.cos())
            .add(&self.scale(theta.sin() / theta))
    }
}

// Operator overloading
impl core::ops::Mul for Multivector {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self { self.mul(&rhs) }
}
```

## Python Implementation

```python
# PGA3D.py
import numpy as np

class Multivector:
    def __init__(self, data=None):
        self.data = np.zeros(16) if data is None else np.array(data)
    
    @classmethod
    def scalar(cls, s): 
        m = cls(); m.data[0] = s; return m
    
    def __mul__(self, other):
        """Geometric product"""
        res = Multivector()
        # Generated multiplication
        res.data[0] = self.data[0]*other.data[0] + ...
        return res
    
    def __xor__(self, other):
        """Wedge product (^)"""
        return self.wedge(other)
    
    def __and__(self, other):
        """Vee product (&)"""
        return self.dual().wedge(other.dual()).dual()
    
    def exp(self):
        """Exponential map"""
        theta = np.sqrt(abs(self.dot(self).data[0]))
        if theta < 1e-6:
            return Multivector.scalar(1) + self
        return Multivector.scalar(np.cos(theta)) + self * (np.sin(theta)/theta)

def point(x, y, z):
    m = Multivector()
    m.data[14] = 1  # e123
    m.data[11] = -x  # e023
    m.data[12] = y   # e013  
    m.data[13] = -z  # e012
    return m
```

## Template System

The generator uses Node.js templates:

```javascript
// codegen/generate.js
const Algebra = require('../ganja.js');

function generateCPP(p, q, r, name) {
  const A = Algebra({p, q, r});
  const {basis, mulTable} = A.describe(true);
  
  // Generate multiplication code
  const mulCode = mulTable.map((row, i) => 
    `res[${i}] = ` + row.map((term, j) => 
      term !== '0' ? `a[${j}]*b[${getBasisIndex(term)}]` : null
    ).filter(Boolean).join(' + ') + ';'
  ).join('\n');
  
  return `
namespace ${name} {
  struct Multivector {
    float data[${basis.length}];
    
    Multivector operator*(const Multivector& b) const {
      Multivector res;
      ${mulCode}
      return res;
    }
  };
}`;
}
```

## Custom Algebra Generation

```javascript
// Generate algebra for your signature
const Algebra = require('ganja.js');

// Generate Cl(1,3) for spacetime
const spacetime = Algebra({p:1, q:3});

// Get multiplication table
const info = spacetime.describe(true);
console.log('Basis:', info.basis);
console.log('Cayley table:', info.mulTable);

// Use template to generate code
const code = generateRust(1, 3, 0, 'Spacetime');
```

## GF(3) Integration

Assign trits to generated algebras:

```javascript
const algebraTrits = {
  'R2':    0,   // Real 2D - ergodic
  'PGA2D': +1,  // Projective 2D - generative
  'CGA2D': -1,  // Conformal 2D - contractive
};

function getAlgebraTrit(name) {
  return algebraTrits[name] || 0;
}
```

## Build Integration

### CMake (C++)

```cmake
add_library(pga3d INTERFACE)
target_include_directories(pga3d INTERFACE 
  ${CMAKE_CURRENT_SOURCE_DIR}/ganja.js/codegen/cpp)
```

### Cargo (Rust)

```toml
[dependencies]
pga3d = { path = "ganja.js/codegen/rust/pga3d" }
```

### pip (Python)

```bash
pip install ganja-algebras  # Hypothetical package
```

## GF(3) Triads

```
ga-codegen (+1) ⊗ clifford-acset-bridge (0) ⊗ sheaf-cohomology (-1) = 0 ✓
ga-codegen (+1) ⊗ pga-motor-interpolation (0) ⊗ conformal-ga (-1) = 0 ✓
```

## Commands

```bash
# Generate all algebras
cd ganja.js/codegen && node generate.js

# Generate specific algebra
node -e "require('./generate').cpp(3,0,1,'PGA3D')" > PGA3D.hpp

# List available pre-generated
ls ganja.js/codegen/{cpp,rust,python,csharp}/
```

## Files

- **Generator**: `ganja.js/codegen/generate.js`
- **C++ output**: `codegen/cpp/*.hpp`
- **Rust output**: `codegen/rust/*/src/lib.rs`
- **Python output**: `codegen/python/*.py`

## References

- [ganja.js codegen](https://github.com/enkimute/ganja.js/tree/master/codegen)
- [klein C++ library](https://github.com/jeremyong/klein) (alternative)
- [Grassmann.jl](https://github.com/chakravala/Grassmann.jl) (Julia native)


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
