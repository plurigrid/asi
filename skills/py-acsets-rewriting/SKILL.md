# py-acsets-rewriting

Python bridge to AlgebraicRewriting.jl for DPO/SPO/SqPO graph rewriting over ACSets.

## GF(3) Assignment

**Trit: -1 (MINUS)** - Validator/constraint role

Triad: `algebraic-rewriting(-1) ⊗ acsets-hatchery(0) ⊗ zulip-cogen(+1) = 0`

## Core Components

```python
from py_acsets_rewriting import (
    PyACSet, ACSetSchema, ACSetMorphism, RewriteRule,
    RewriteType, find_homomorphisms, rewrite,
    GraphSchema, LabeledGraphSchema,
    make_edge_contraction_rule, make_vertex_duplication_rule
)
```

## Rewrite Types

| Type | Description | Gluing Condition |
|------|-------------|------------------|
| DPO  | Double Pushout - safe deletion | Required |
| SPO  | Single Pushout - greedy deletion | Not checked |
| SqPO | Sesqui-Pushout - cloning + deletion | Extended |

## Usage Pattern

```python
# Create graph
G = PyACSet(GraphSchema)
vs = G.add_parts("V", 4)
for i in range(3):
    e = G.add_part("E")
    G.set_subpart(e, "src", i)
    G.set_subpart(e, "tgt", i + 1)

# Create rewriter and apply rule
rewriter = PyACSetRewriter()
rewriter.add_rule(make_edge_contraction_rule())
H = rewriter.apply("edge_contraction", G)
```

## Rule Structure (L ← K → R)

- **L**: Pattern to match (left-hand side)
- **K**: Interface to preserve
- **R**: Replacement (right-hand side)
- **l**: K → L morphism
- **r**: K → R morphism

## Color Integration

All ACSets receive deterministic Gay.jl colors via SplitMix64:
```python
GAY_SEED = 0x6761795f636f6c6f
color = seed_to_color(hash(str(acset.parts)) ^ GAY_SEED)
```

## File Location

`/Users/bob/ies/py_acsets_rewriting.py`

## Dependencies

- `py-acsets` (pip install)
- Python 3.10+


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
