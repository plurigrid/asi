---
name: pga-motor-interpolation
description: "Motor interpolation (slerp/nlerp) for smooth rigid body transformations in PGA"
license: MIT
metadata:
  source: ganja.js + klein + Grassmann.jl
  trit: 0
  gf3_conserved: true
  version: 1.0.0
---

# pga-motor-interpolation

> Smooth interpolation of rotations and translations via motor logarithms

**Version**: 1.0.0  
**Trit**: 0 (ERGODIC - transport between states)

## Overview

**Motors** in Projective Geometric Algebra (PGA) unify rotations and translations into a single algebraic object. This skill provides interpolation methods for smooth animation and trajectory planning.

## Motor Structure

A motor M ∈ Cl(3,0,1)⁺ (even subalgebra) has the form:

```
M = s + B + I·t

where:
  s = scalar (cos(θ/2))
  B = bivector (sin(θ/2)·axis)  
  I = pseudoscalar
  t = translation bivector
```

### Decomposition

```javascript
// ganja.js PGA3D motor
Algebra(3,0,1, () => {
  // Rotor: pure rotation about line l
  var rotor = (angle, l) => Math.cos(angle/2) + Math.sin(angle/2)*l.Normalized;
  
  // Translator: pure translation along ideal line
  var translator = (dist, dir) => 1 + (dist/2)*(dir.e01*1e01 + dir.e02*1e02 + dir.e03*1e03);
  
  // Motor: composition of rotor and translator
  var motor = (R, T) => T * R;  // Order matters!
});
```

## Exp/Log Maps

The exponential map converts bivectors (infinitesimal transformations) to motors:

```
Exp: 𝔪 → M
     b ↦ e^b = cos|b| + sin|b|·b/|b| + ...

Log: M → 𝔪  
     M ↦ log(M) = arccos(s)·B/|B| + ...
```

### ganja.js Implementation

```javascript
// From ganja.js source (lines 489-547)
Exp(taylor = false) {
  // Closed form for 3D PGA
  if (tot==4 && r==1) {
    var u = Math.sqrt(Math.abs(this.Dot(this).s));
    if (Math.abs(u) < 1E-5) return this.Add(Element.Scalar(1));
    var v = this.Wedge(this).Scale(-1/(2*u));
    return Element.Add(
      Element.Sub(Math.cos(u), v.Scale(Math.sin(u))),
      Element.Div(
        Element.Mul(Element.Add(Math.sin(u), v.Scale(Math.cos(u))), this),
        Element.Add(u, v)
      )
    );
  }
  // Taylor series fallback
  var res = Element.Scalar(1), y=1, M=this.Scale(1), N=this.Scale(1);
  for (var x=1; x<15; x++) { 
    res = res.Add(M.Scale(1/y)); 
    M = M.Mul(N); 
    y = y*(x+1); 
  }
  return res;
}

Log(compat = false) {
  // Inverse of Exp - extract bivector from motor
  // See: https://www.researchgate.net/publication/360528787
}
```

## Interpolation Methods

### 1. NLERP (Normalized Linear Interpolation)

Fast but not constant-speed:

```javascript
function nlerp(m1, m2, t) {
  return m1.Scale(1-t).Add(m2.Scale(t)).Normalized;
}
```

### 2. SLERP (Spherical Linear Interpolation)

Constant angular velocity:

```javascript
function slerp(m1, m2, t) {
  var omega = Math.acos(m1.Dot(m2).s);
  if (Math.abs(omega) < 1e-6) return m1;
  return m1.Scale(Math.sin((1-t)*omega)/Math.sin(omega))
           .Add(m2.Scale(Math.sin(t*omega)/Math.sin(omega)));
}
```

### 3. Screw Linear Interpolation

Uses Log/Exp for true geodesic on motor manifold:

```javascript
function screwLerp(m1, m2, t) {
  // Geodesic on motor manifold
  var delta = m1.Reverse.Mul(m2);  // Relative motor
  var logDelta = delta.Log();       // To Lie algebra
  return m1.Mul(logDelta.Scale(t).Exp());  // Interpolate in algebra
}
```

## Sandwich Product

The sandwich product applies a motor to any element:

```
X' = M · X · M̃

where M̃ = reverse of M
```

### Implementation

```javascript
// ganja.js uses >>> operator
var transformedPoint = motor >>> point;

// Explicit form
var transformedPoint = motor.Mul(point).Mul(motor.Reverse);
```

## Application: Skeletal Animation

From [klein documentation](https://jeremyong.com/klein/):

```cpp
// C++ with klein library
kln::motor interpolate_joint(
    kln::motor const& rest_pose,
    kln::motor const& animated_pose,
    float weight
) {
    // Screw linear interpolation
    kln::motor delta = ~rest_pose * animated_pose;
    kln::line log_delta = delta.log();
    return rest_pose * (weight * log_delta).exp();
}
```

## GF(3) Motor Decomposition

Motors decompose into three trit-aligned components:

| Component | Description | GF(3) Trit |
|-----------|-------------|------------|
| Translation | Ideal bivector (e₀ᵢ) | +1 (PLUS) |
| Rotation | Euclidean bivector (eᵢⱼ) | 0 (ERGODIC) |
| Identity | Scalar | -1 (MINUS) |

### Conservation Check

```javascript
function verifyMotorGF3(motor) {
  var translationWeight = motor.Grade(2).filter(isIdeal).length > 0 ? 1 : 0;
  var rotationWeight = motor.Grade(2).filter(isEuclidean).length > 0 ? 0 : 0;
  var identityWeight = Math.abs(motor.s) > 0.01 ? -1 : 0;
  
  return (translationWeight + rotationWeight + identityWeight) % 3 === 0;
}
```

## Integration with Open Games

```haskell
-- Motor interpolation as open game
MotorGame : OpenGame (Motor, Motor) (Motor, Float)

play (m1, m2) t = screwLerp m1 m2 t
coplay _ (result, reward) = 
  if result.isNormalized then reward + 10 else reward - 5
```

## GF(3) Triads

```
ganja-wedge-game (+1) ⊗ pga-motor-interpolation (0) ⊗ temporal-coalgebra (-1) = 0 ✓
clifford-acset-bridge (0) ⊗ pga-motor-interpolation (0) ⊗ bisimulation-game (0) → need rebalance
```

## Commands

```bash
# ganja.js motor demo
node -e "var A=require('ganja.js'); A(3,0,1,()=>{
  var R = (1+0.5*1e12).Normalized;  // Rotor
  var T = 1 + 0.5*1e01;              // Translator  
  var M = T.Mul(R);                  // Motor
  console.log('Motor:', M);
  console.log('Log:', M.Log());
})()"

# Julia equivalent
julia -e 'using Grassmann; @basis ℝ^(3,0,1); 
  R = exp(π/4 * v12); println("Rotor: ", R)'
```

## References

- [ganja.js Exp/Log](https://github.com/enkimute/ganja.js/blob/master/ganja.js#L489)
- [klein motor interpolation](https://jeremyong.com/klein/case_studies/ga_skeletal_animation/)
- [Normalization, Square Roots, and the Exponential Map](https://www.researchgate.net/publication/360528787)
- [Grassmann.jl algebra of space](https://chakravala.github.io/Grassmann.jl/tutorials/algebra-of-space/)


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
