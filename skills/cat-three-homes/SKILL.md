---
name: cat-three-homes
description: 'The double category of polynomial comonads where:'
---
# Cat# Three Homes Skill

> "All Concepts are Cat#" — Spivak (ACT 2023)

**Trit**: 0 (ERGODIC)  
**Color**: #49EE54  
**Source**: Spivak, Lynch, Shapiro - "All concepts are Cat#" ACT 2023

## Core Definition

```
Cat# = Comod(Poly, y, ◁)
```

The double category of polynomial comonads where:
- **Poly** = free completely distributive category on one object
- **y** = identity polynomial
- **◁** = composition (substitution) of polynomials

## The Three Homes

### Home 1: Polynomial Comonads (Objects of Cat#)

Categories ARE the objects of Cat#.

```
A category C becomes polynomial: Σ_{A:Ob(C)} y^{C[A]}
where C[A] = Σ_{B:Ob(C)} C(A,B) = "maps out of A"

• Counit ε: c → y supplies identities
• Comult δ: c → c◁c supplies codomains and composition
```

**Skill mapping**: `gay-mcp` (+1) — inject deterministic state

### Home 2: Monads in Span (Linear restriction)

```
Comod(Set, 1, ×) ≅ Span
Mod(Span) ≅ Prof(Cat)
```

Linear polynomials only: `c = Cy` (just a set of objects)
Bicomodules: `Cy ◁──Py──▷ Dy` (spans of sets)

**Categories = monads in Span**

**Skill mapping**: `acsets` (0) — schema as span

### Home 3: Path Algebras (Most familiar)

```
Graph category G = (• ⇉ •) with polynomial g = y³ + y
g-Set ≅ Grph (category of graphs)

path: g◁ ──→ ◁g is a monad (prafunctor Grph → Grph)
```

**Categories = path-algebras = path-complete graphs**

**Skill mapping**: `bisimulation-game` (-1) — validate path equivalence

## GF(3) Triad

```
bisimulation-game (-1) ⊗ cat-three-homes (0) ⊗ gay-mcp (+1) = 0 ✓
```

| Trit | Home | Skill | Role |
|------|------|-------|------|
| -1 | Path Algebras | bisimulation-game | Validate equivalences |
| 0 | Span/Prof | acsets, cat-three-homes | Schema bridge |
| +1 | Poly Comonads | gay-mcp | State injection |

## Key Structures

### Bicomodules (Horizontal morphisms in Cat#)

```
c ◁ p ◁ d  with maps satisfying laws w.r.t. ε, δ
```

These are precisely **prafunctors** `d-Set → c-Set` (data migrations).

### The Mod Construction

```
If D has nice local coequalizers → Mod(D)
If P has nice local equalizers → Comod(P)

Poly has ◁-preserved local equalizers: e → p ⟹ q
So we can form Comod(Poly) = Cat#
```

### Org (Dynamic Arrangements)

```
Org ↪ Cat#  (fully faithful)

Objects: p : Poly → cofree comonoid 𝔠_p
Horizontals: [p,q]-coalgebras (dynamic arrangements)
```

Models neural networks, prediction markets, rewiring diagrams.

## Multivariate Extension

For any category E with pullbacks:

```
Poly_E embeds into Cat#
by sending I : E to slice category A/I
```

Discrete categories in Cat# ≅ multivariate polynomials in Set.

## Commands

```bash
# Query homes
bb cat-three-homes.bb --home 1  # Polynomial comonads
bb cat-three-homes.bb --home 2  # Span/Prof
bb cat-three-homes.bb --home 3  # Path algebras

# Dispatch concept to home
bb cat-three-homes.bb --dispatch "functor"

# Show all triads
bb cat-three-homes.bb --triads
```

## DuckDB Schema

```sql
CREATE TABLE cat_homes (
    home_id INT PRIMARY KEY,
    name VARCHAR,
    structure VARCHAR,
    skill VARCHAR,
    trit TINYINT
);

INSERT INTO cat_homes VALUES
(1, 'Polynomial Comonads', 'Comod(Poly,y,◁)', 'gay-mcp', 1),
(2, 'Monads in Span', 'Mod(Span)≅Prof', 'acsets', 0),
(3, 'Path Algebras', 'path-complete graphs', 'bisimulation-game', -1);
```

## Related Skills

| Skill | Trit | Relation |
|-------|------|----------|
| `catsharp` | 0 | Core Cat# skill |
| `kan-extensions` | 0 | Universal property source |
| `infinity-operads` | +1 | Higher categorical extension |
| `topos-catcolab` | 0 | CatColab double theories |
| `polynomial-functors` | 0 | Poly foundation |

## References

1. Spivak, Lynch, Shapiro - "All concepts are Cat#" (ACT 2023)
2. Niu & Spivak - "Polynomial Functors" (Cambridge 2024)
3. Shulman - "Framed Bicategories and Monoidal Fibrations"
4. Ahman-Uustalu - Polynomial comonads are categories
5. Garner - Prafunctors (HoTTEST video)

## 2-Torial Integration

Concepts from Topos 2-torials map to homes:

| 2-Torial | Concept | Home |
|----------|---------|------|
| Doctrinal Adjunctions | doctrine, lax | Home 2 (Span) |
| Instances of Models | double category, model | Home 1 (Poly) |
| Coalgebraic-Modal | coalgebra, monad | Home 3 (Path) |


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
