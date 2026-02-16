---
name: conformal-ga
description: "Conformal Geometric Algebra (CGA) for circles, spheres, and Möbius transformations"
license: MIT
metadata:
  source: ganja.js + clifford + Grassmann.jl
  trit: -1
  gf3_conserved: true
  version: 1.0.0
---

# conformal-ga

> CGA: Embed Euclidean space into a higher-dimensional conformal space

**Version**: 1.0.0  
**Trit**: -1 (MINUS - contractive/measurement)

## Overview

Conformal Geometric Algebra (CGA) extends PGA by adding two extra dimensions that encode **scale** and **infinity**. This allows representing circles and spheres as simple blades.

## Algebra Signatures

| Algebra | Signature | Euclidean Dim | Total Dim |
|---------|-----------|---------------|-----------|
| CGA2D | Cl(3,1) | 2D | 4D → 16 basis |
| CGA3D | Cl(4,1) | 3D | 5D → 32 basis |
| DCGA3D | Cl(6,2) | 3D (double) | 8D → 256 basis |

## Null Basis

The key insight: two null vectors encode the origin and infinity:

```javascript
Algebra(4,1, () => {
  // Standard basis: e1, e2, e3 (Euclidean), e4 (+), e5 (-)
  
  // Null vectors
  var no = 0.5*(1e5 - 1e4);  // Origin (null)
  var ni = 1e4 + 1e5;         // Infinity (null)
  
  // Key property: no · ni = -1
  console.log((no << ni).s);  // -1
  
  // Point embedding: x ↦ no + x + (x²/2)ni
  var point = (x,y,z) => {
    var x2 = x*x + y*y + z*z;
    return no + x*1e1 + y*1e2 + z*1e3 + 0.5*x2*ni;
  };
});
```

## Geometric Objects as Blades

### Points (Grade 1 OPNS)

```javascript
var P = point(1, 2, 3);  // Null vector
// P · P = 0 (null)
```

### Point Pairs (Grade 2)

```javascript
var A = point(0,0,0), B = point(1,0,0);
var pointPair = A ^ B;  // Wedge of two points
```

### Circles (Grade 3)

```javascript
var A = point(0,0,0), B = point(1,0,0), C = point(0,1,0);
var circle = A ^ B ^ C;  // Through three points

// Or: dual sphere intersected with plane
var sphere = dualSphere(center, radius);
var plane = dualPlane(normal, distance);
var circle2 = sphere ^ plane;
```

### Spheres (Grade 4 OPNS / Grade 1 IPNS)

```javascript
// OPNS: 4 points define a sphere
var sphere = A ^ B ^ C ^ D;

// IPNS (dual): center + radius encoding
var dualSphere = (c, r) => point(c.x, c.y, c.z) - 0.5*r*r*ni;
```

### Planes (Grade 4 OPNS)

```javascript
// OPNS: 3 points + infinity
var plane = A ^ B ^ C ^ ni;

// IPNS (dual): normal + distance
var dualPlane = (n, d) => n.x*1e1 + n.y*1e2 + n.z*1e3 + d*ni;
```

## Conformal Transformations

All Möbius transformations are motors in CGA!

### Rotation

```javascript
// Same as PGA - bivector in Euclidean part
var rotor = Math.cos(angle/2) + Math.sin(angle/2)*1e12;
var rotated = rotor * object * ~rotor;
```

### Translation

```javascript
// Translator uses ni (infinity)
var translator = 1 - 0.5*distance*(direction ^ ni);
var translated = translator * object * ~translator;
```

### Dilation (Scaling)

```javascript
// Unique to CGA - uses no and ni
var dilator = Math.cosh(s/2) + Math.sinh(s/2)*(no ^ ni);
var scaled = dilator * object * ~dilator;
// Scales by e^s
```

### Inversion (Circle/Sphere)

```javascript
// Reflect in a sphere - a versor!
var inverted = sphere * point * sphere;
// Maps inside to outside
```

## Distance and Angle Extraction

### Distance Between Points

```javascript
function distance(P, Q) {
  return Math.sqrt(-2 * (P << Q).s);
}
```

### Radius of Sphere/Circle

```javascript
function radius(sphere) {
  var s2 = (sphere * sphere).s;
  var sni = (sphere << ni).s;
  return Math.sqrt(Math.abs(s2)) / Math.abs(sni);
}
```

## OPNS vs IPNS

| Representation | Meaning | Grade |
|----------------|---------|-------|
| **OPNS** (Outer Product Null Space) | Object = span of null vectors | Higher |
| **IPNS** (Inner Product Null Space) | Object = things with zero inner product | Lower |

```javascript
// Convert between them via dualization
var ipns = !opns;  // Dual
var opns = !ipns;  // UnDual
```

## ganja.js CGA Examples

```javascript
Algebra(4,1, () => {
  var no = 0.5*(1e5-1e4), ni = 1e4+1e5;
  var point = (x,y,z) => no + x*1e1 + y*1e2 + z*1e3 + 0.5*(x*x+y*y+z*z)*ni;
  
  // Three points define a circle
  var A = point(1,0,0), B = point(0,1,0), C = point(-1,0,0);
  var circle = A ^ B ^ C;
  
  // Render it
  return this.graph([
    0xFF0000, A, B, C,
    0x00FF00, circle
  ], {conformal: true, gl: true});
});
```

## GF(3) Role

CGA is MINUS (-1) because it primarily **measures** and **contracts**:
- Distance computation uses inner product (contraction)
- Sphere/circle radius extraction
- Intersection (meet) operations

### Conservation Triad

```
conformal-ga (-1) ⊗ pga-motor-interpolation (0) ⊗ ga-visualization (+1) = 0 ✓
```

## Applications

1. **Computer Vision**: Circle/sphere fitting
2. **Robotics**: Kinematics with scaling
3. **Graphics**: Ray-sphere intersection
4. **Physics**: Conformal field theory

## Related Algebras

| Name | Signature | Use Case |
|------|-----------|----------|
| CGA2D | Cl(3,1) | 2D circles |
| CGA3D | Cl(4,1) | 3D spheres |
| DCGA | Cl(6,2) | Quadric surfaces |
| TCGA | Cl(9,3) | Cubic surfaces |
| QCGA | Cl(9,6) | Quartic surfaces |

## Commands

```bash
# ganja.js CGA demo
node -e "var A=require('ganja.js'); A(4,1,()=>{
  var no=0.5*(1e5-1e4), ni=1e4+1e5;
  var pt=(x,y,z)=>no+x*1e1+y*1e2+z*1e3+0.5*(x*x+y*y+z*z)*ni;
  console.log('Origin:', pt(0,0,0));
  console.log('ni:', ni);
})()"

# Python clifford
python3 -c "from clifford.g3c import *; print(eo, einf)"
```

## References

- [ganja.js CGA examples](https://enkimute.github.io/ganja.js/examples/coffeeshop.html#cga3d_points_spheres_planes)
- [Geometric Algebra for Computer Science](https://www.geometricalgebra.net/) - Dorst, Fontijne, Mann
- [clifford Python library](https://github.com/pygae/clifford)
- [bivector.net CGA tutorials](https://bivector.net/)


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
