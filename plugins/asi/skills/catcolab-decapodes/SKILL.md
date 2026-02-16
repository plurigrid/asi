---
name: catcolab-decapodes
description: CatColab Decapodes - Discrete Exterior Calculus for PDE modeling on meshes via Decapodes.jl integration. Model physics equations compositionally with automatic code generation.
version: 1.0.0
---

# CatColab Decapodes: Discrete Exterior Calculus

**Trit**: -1 (MINUS - validator/verifier)
**Color**: Purple (#8A2BE2)

## Overview

Decapodes in CatColab enable **Discrete Exterior Calculus (DEC)** for modeling PDEs:
- **Differential forms**: 0-forms (scalars), 1-forms (vectors), 2-forms (flux)
- **Operators**: d (exterior derivative), ★ (Hodge star), Δ (Laplacian)
- **Multiphysics**: Compose PDEs from different domains
- **Automatic code generation**: Export to AlgebraicJulia/Decapodes.jl

This is CatColab's most advanced logic, connecting category theory to numerical PDE simulation.

## Mathematical Foundation

Discrete Exterior Calculus discretizes differential geometry on meshes:

```
┌─────────────────────────────────────────────────────┐
│              DISCRETE EXTERIOR CALCULUS              │
├─────────────────────────────────────────────────────┤
│  Spaces (Differential Forms):                        │
│    Ω⁰ (0-forms): Scalars on vertices (temperature)  │
│    Ω¹ (1-forms): Vectors on edges (velocity)        │
│    Ω² (2-forms): Flux through faces (flow rate)     │
│                                                      │
│  Operators:                                          │
│    d: Ωᵏ → Ωᵏ⁺¹  (exterior derivative)              │
│    ★: Ωᵏ → Ωⁿ⁻ᵏ  (Hodge star)                       │
│    δ = ★d★: Ωᵏ → Ωᵏ⁻¹ (codifferential)              │
│    Δ = dδ + δd: Laplacian                           │
│                                                      │
│  De Rham Complex:                                    │
│    Ω⁰ ──d──► Ω¹ ──d──► Ω² ──d──► Ω³                 │
│     │         │         │         │                  │
│     ★         ★         ★         ★                  │
│     ▼         ▼         ▼         ▼                  │
│    Ω³ ◄──d── Ω² ◄──d── Ω¹ ◄──d── Ω⁰                 │
└─────────────────────────────────────────────────────┘
```

## Double Theory

```rust
// DEC double theory (simplified)
pub fn th_decapodes() -> DiscreteDblTheory {
    let mut cat = FpCategory::new();

    // Form spaces
    cat.add_ob_generator(name("Form0"));  // Scalars
    cat.add_ob_generator(name("Form1"));  // 1-forms
    cat.add_ob_generator(name("Form2"));  // 2-forms

    // Differential operators
    cat.add_mor_generator(name("d0"), name("Form0"), name("Form1"));
    cat.add_mor_generator(name("d1"), name("Form1"), name("Form2"));

    // Hodge star
    cat.add_mor_generator(name("star0"), name("Form0"), name("Form2"));
    cat.add_mor_generator(name("star1"), name("Form1"), name("Form1"));
    cat.add_mor_generator(name("star2"), name("Form2"), name("Form0"));

    // Constraint: d ∘ d = 0
    cat.add_equation(
        compose(name("d0"), name("d1")),
        zero_morphism(name("Form0"), name("Form2"))
    );

    cat.into()
}
```

## CatColab Implementation

### Form Space Declaration

```typescript
{
  "type": "ObDecl",
  "name": "Temperature",
  "theory_type": "Form0",
  "description": "scalar temperature field on vertices"
}
```

### Operator Declaration

```typescript
{
  "type": "MorDecl",
  "name": "gradient_T",
  "dom": "Temperature",
  "cod": "HeatFlux",
  "theory_type": "d0",
  "description": "gradient of temperature"
}
```

### PDE Declaration

```typescript
{
  "type": "EqDecl",
  "name": "heat_equation",
  "equation": "∂T/∂t = κ·Δ(T)",
  "description": "heat diffusion equation"
}
```

## Physics Examples

### Example 1: Heat Equation

```
∂T/∂t = κ·ΔT

Where:
  T: Form0 (temperature)
  κ: diffusivity constant
  Δ = ★d★d (Laplace-Beltrami)

CatColab composition:
  T ──d──► dT ──★──► ★dT ──d──► d★dT ──★──► ★d★dT = ΔT
```

### Example 2: Navier-Stokes (2D)

```
∂ω/∂t + (v·∇)ω = ν·Δω

Where:
  ω: Form2 (vorticity)
  v: Form1 (velocity)
  ν: viscosity

Composition:
  Advection: v ──∧──► v∧ω (wedge product)
  Diffusion: ω ──Δ──► Δω
```

### Example 3: Maxwell's Equations

```
dE = -∂B/∂t    (Faraday)
dB = 0         (no monopoles)
δE = ρ/ε₀     (Gauss)
δB = μ₀J + μ₀ε₀∂E/∂t  (Ampère-Maxwell)

Where:
  E: Form1 (electric field)
  B: Form2 (magnetic field)
  J: Form1 (current density)
```

### Example 4: Shallow Water Equations

```
∂h/∂t + ∇·(hv) = 0         (continuity)
∂v/∂t + (v·∇)v = -g∇h      (momentum)

Where:
  h: Form0 (water height)
  v: Form1 (velocity)
```

## Multiphysics Composition

Decapodes compose via **operad algebras**:

```
┌─────────────────────────────────────────────────────┐
│              MULTIPHYSICS COMPOSITION                │
├─────────────────────────────────────────────────────┤
│  Physics 1: Heat Transfer                            │
│    ∂T/∂t = κ·ΔT                                      │
│                                                      │
│  Physics 2: Advection                                │
│    ∂c/∂t = -v·∇c                                     │
│                                                      │
│  Composed: Advection-Diffusion                       │
│    ∂c/∂t = κ·Δc - v·∇c                               │
│                                                      │
│  Interface: Shared Form1 velocity v                  │
└─────────────────────────────────────────────────────┘
```

## CatColab 0.2 Integration

CatColab 0.2 (Wren) introduced Decapodes integration:

```typescript
// Export to Decapodes.jl
const analysis = await model.analyze({
  type: "decapodes-export",
  mesh: "sphere_mesh.obj",
  time_span: [0, 100],
  parameters: { κ: 0.1 }
});

// Returns animated solution visualization
```

## GF(3) Triads

```
catcolab-decapodes (-1) ⊗ topos-catcolab (0) ⊗ catcolab-stock-flow (+1) = 0 ✓
fokker-planck-analyzer (-1) ⊗ catcolab-decapodes (0) ⊗ langevin-dynamics (+1) = 0 ✓
```

## Commands

```bash
# Create Decapodes model
just catcolab-new decapodes "heat-transfer"

# Generate Julia code
just catcolab-export heat-transfer --format=decapodes

# Simulate on mesh
just catcolab-simulate heat-transfer --mesh sphere.obj --time 100

# Compose physics models
just catcolab-compose heat-transfer advection --interface velocity
```

## Integration with Decapodes.jl

```julia
using Decapodes
using CombinatorialSpaces

# Load CatColab model
decapode = load_decapode("heat-transfer.json")

# Create mesh
mesh = loadmesh(Icosphere(3))

# Generate simulation code
sim = evalsim(decapode)

# Run simulation
u0 = initial_conditions(mesh)
prob = ODEProblem(sim, u0, (0.0, 10.0))
sol = solve(prob, Tsit5())

# Visualize
animate(sol, mesh, "heat_animation.mp4")
```

## References

- Hirani (2003) "Discrete Exterior Calculus" (PhD thesis)
- Desbrun et al. (2005) "Discrete Differential Forms for Computational Modeling"
- Patterson et al. (2023) "Decapodes: A diagrammatic framework for multiphysics"
- [Decapodes.jl](https://algebraicjulia.github.io/Decapodes.jl/)
- [CatColab DEC Help](https://catcolab.org/help/logics/decapodes)

---

**Skill Name**: catcolab-decapodes
**Type**: Discrete Exterior Calculus / PDE Modeling
**Trit**: -1 (MINUS)
**GF(3)**: Conserved via triadic composition
