---
metadata:
  interface_ports:
  - References
  - Commands
  - GF(3) Triads
  - Integration with
trit: 0
color: '#49EE54'
---
# Just Monad Skill

> Justfile as Free Monad for compositional task orchestration

**Trit**: 0 (ERGODIC)  
**Color**: #49EE54 (Green)  
**Role**: Coordinator/Orchestrator

## Core Concept

The **Just Monad** treats `just` recipes as monadic actions:

```haskell
data JustF next
  = Recipe String [String] next     -- name, deps, continuation
  | Shell String next               -- command, continuation
  | Parallel [JustF next] next      -- concurrent recipes

type Just = Free JustF
```

**Universal Property**: `Just` is the free monad over the Justfile signature functor.

## Monad Laws in Justfiles

```just
# Left identity: just (pure a) >>= f  ≡  f a
pure-then-use: other
    @echo "Equivalent to just running 'other'"

# Right identity: m >>= pure  ≡  m
action-then-pure: action
    # Returns result of action unchanged

# Associativity: (m >>= f) >>= g  ≡  m >>= (λx. f x >>= g)
a-then-b-then-c: a b c
    # Order doesn't matter for composition
```

## Pattern: Dependency as Bind

```just
# Pure: no dependencies
leaf:
    @echo "I am a leaf node"

# Bind: depends on other recipes
branch: leaf
    @echo "I depend on leaf"

# Nested bind
root: branch
    @echo "I depend on branch (transitively on leaf)"
```

Execution order: `leaf` → `branch` → `root` (topological sort)

## The Three Arrows (α/β/γ)

From Narya structural diffing:

| Arrow | Just Recipe Pattern | Meaning |
|-------|---------------------|---------|
| α (−1) | `test:` | Behavioral verification |
| β (0) | `build:` | Structural transformation |
| γ (+1) | `deploy:` | Bridge/coherence action |

```just
# α: Verify behavior hasn't changed
test:
    julia --project -e 'using Test; @testset "all" begin include("test/runtests.jl") end'

# β: Transform structure
build: test
    julia --project -e 'using Pkg; Pkg.build()'

# γ: Bridge to production (coherence check)
deploy: build
    @echo "Deploying if tests pass and build succeeds"
```

**GF(3)**: (−1) + 0 + (+1) = 0 ✓ CONSERVED

## Parallel Composition (Applicative)

```just
# Parallel: independent recipes can run concurrently
parallel-test:
    just test-unit &
    just test-integration &
    wait

# Applicative: f <*> x
apply-all: build
    just deploy-a &
    just deploy-b &
    just deploy-c &
    wait
```

## Justfile Random Walk

Navigate justfiles via deterministic random walk:

```bash
# Find all justfiles
find ~/worlds -name "justfile" | shuf -n 3

# Extract recipes
just --list --justfile /path/to/justfile

# Run random recipe
just --justfile /path/to/justfile $(just --list | shuf -n 1 | awk '{print $1}')
```

## Skill Graph Rewilding

When adding a new skill that uses justfiles:

1. **α-diff**: Does the new recipe preserve existing test behavior?
2. **β-diff**: Does the recipe structure fit the existing graph?
3. **γ-diff**: Is there a bridge connecting new ↔ existing recipes?

```just
# Verify transitivity when adding skill C between A and B
verify-transitivity a b c:
    @echo "Checking: {{a}} → {{c}} → {{b}}"
    just {{a}}
    just {{c}}
    just {{b}}
    @echo "Transitivity verified if all pass"
```

## TeglonLabs Justfile Patterns

Found across TeglonLabs repos:

| Repo | Pattern | Trit |
|------|---------|------|
| topoi | Python ML pipeline | −1 |
| vibespace | Go MCP server | 0 |
| codex | Rust workspace | +1 |
| autofoom | Agent orchestration | 0 |

## Cofree Comonad Dual

The dual of `Just` (Free Monad) is the **Cojust** (Cofree Comonad):

```haskell
data Cojust a = a :< JustF (Cojust a)
-- Infinite stream of possible continuations
```

**Cojust** represents:
- The environment/context in which recipes run
- The history of all past executions
- The space of possible futures

---

## End-of-Skill Interface

## Commands

```bash
# List all recipes
just --list

# Run with variables
just test seed=1069

# Dry run (show commands)
just --dry-run build

# Evaluate expression
just --evaluate '{{arch()}}'

# Export as shell script
just --dump --format=just
```

## Integration with Gay.jl

```julia
# Just Monad in Julia
struct JustMonad{A}
    recipe::String
    deps::Vector{String}
    action::Function
end

function just_pure(recipe, action)
    JustMonad{Any}(recipe, String[], action)
end

function just_bind(m::JustMonad, recipe, action)
    JustMonad{Any}(recipe, [m.recipe; m.deps], action)
end

# Color each recipe by trit
function just_color(m::JustMonad, seed::UInt64)
    idx = hash(m.recipe) % 1000
    gay_color_at(seed, idx)
end
```

## GF(3) Triads

```
narya-proofs (-1) ⊗ just-monad (0) ⊗ free-monad-gen (+1) = 0 ✓
three-match (-1) ⊗ just-monad (0) ⊗ gay-mcp (+1) = 0 ✓
temporal-coalgebra (-1) ⊗ just-monad (0) ⊗ topos-generate (+1) = 0 ✓
```

## References

- [Just Manual](https://just.systems/man/en/)
- Swierstra, "Data Types à la Carte"
- Kiselyov & Ishii, "Freer Monads"
- ALIFE 2025, "Structural Rewilding via Diffs"


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*


## CT lattice atlas

Part of: `para-mensch-commons` (CT lattice family).
