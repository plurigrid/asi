---
name: gh-interactome
description: "github social graph analysis, contribution prediction, and regret-weighted pr prioritization via gf(3) conservation"
metadata:
  trit: 1
  version: "1.0.0"
  bundle: tooling
---

# gh-interactome skill

**trit**: +1 (plus - generator)
**color**: warm (0-60°)
**role**: predict and generate contribution patterns

## overview

analyzes github social graphs and predicts next contributions using:
- regret-weighted pr prioritization
- gf(3) conservation requirements
- interactome pattern recognition
- prediction market mechanics

## core functions

### 1. regret score

```
regret = age_days × impact_factor × (1 - merge_probability)

impact_map:
  feat: 1.5
  test: 1.2
  fix:  1.0
  docs: 0.8
  chore: 0.6
```

### 2. contribution prediction

signals:
- recent commit activity (repos with high commit counts)
- open prs awaiting review
- starred repos (future interest)
- gf(3) balance needs (which trit is underrepresented)

### 3. network acset schema

```clojure
{:objects #{:User :Repo :Follows :Stars}
 :morphisms
 {:src     {:dom :Follows :cod :User}
  :tgt     {:dom :Follows :cod :User}
  :starrer {:dom :Stars :cod :User}
  :starred {:dom :Stars :cod :Repo}}
 :attributes
 {:username    {:dom :User :cod :String}
  :last-active {:dom :User :cod :DateTime}
  :trit        {:dom :User :cod :GF3}
  :hue         {:dom :User :cod :Float}
  :rank        {:dom :User :cod :Int}}}
```

## commands

```bash
# run prediction analysis
python src/interactome_prediction.py

# query network acset
bb dev/github_network_acset.clj

# live github queries
gh api users/bmorphism/repos --jq '.[0:10] | .[] | .name'
gh api repos/plurigrid/asi/pulls --jq '.[] | "#\(.number) \(.title)"'
```

## current state (2025-12-26)

### gf(3) imbalance

```
plus (+1):    7 prs
ergodic (0):  6 prs
minus (-1):   3 prs
sum: 4 | need 4 more minus validators
```

### high regret prs

| regret | pr | repo | trit |
|--------|-----|------|------|
| 6.3 | #14 | plurigrid/asi | 0 |
| 6.3 | #13 | plurigrid/asi | -1 |
| 6.3 | #224 | gay.jl | +1 |
| 6.3 | #218 | gay.jl | +1 |

### predicted next contributions

| prob | repo | trit |
|------|------|------|
| 85% | gay.jl #223 merge | 0 |
| 75% | ezkl-ethglobal2025 | +1 |
| 70% | plurigrid/asi #16 merge | +1 |
| 60% | spi verification suite | -1 |

## canonical triads

```
bisimulation-game (-1) ⊗ gh-cli (0) ⊗ gh-interactome (+1) = 0 ✓
temporal-coalgebra (-1) ⊗ open-games (0) ⊗ gh-interactome (+1) = 0 ✓
```

## files

- `src/interactome_prediction.py` - prediction engine
- `dev/github_network_acset.clj` - 69-account network acset
- `dev/MOVE_INTERACTOME.md` - move file interaction analysis



## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Graph Theory
- **networkx** [○] via bicomodule

### Bibliography References

- `general`: 734 citations in bib.duckdb

## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: ⊗
Kan Role: Adj
Color: #26D826
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

This ensures compositional coherence in the Cat# equipment structure.
