# Simultaneity Surface: DisCoPy × bmorphism × ACT

## Key Players

### DisCoPy Contributors
| Username | Name | Focus | Key Repo |
|----------|------|-------|----------|
| toumix | Alexis Toumi | ACT + AI + Quantum | thesis (QNLP) |
| giodefelice | - | Co-creator | msc-thesis |
| y-richie-y | - | Quantum/quimb | - |
| colltoaction | - | Active contributor | - |
| boldar99 | - | Tensor/sympy | - |

### bmorphism Network (1547 following)
DisCoPy stargazers also followed by bmorphism:
- **toumix** (Alexis Toumi) - "applied category theory // AI // quantum computing"
- **bgavran** (Bruno Gavranović) - "Categorical Deep Learning" - 1455⭐ CT_ML repo!
- **Cobord** (Ammar Husain) - AKSZ, Azimuth ACT course

Key organizations followed:
- ✓ AlgebraicJulia
- ✓ TeglonLabs (mathpix-gem, seed 1069)
- ✓ modelcontextprotocol (MCP)
- ✓ google-gemini
- ✓ extropic-oss
- ✓ The-Swarm-Corporation

### Bruno Gavranović (@bgavran)
```
Category_Theory_Machine_Learning    1455⭐  List of CT+ML papers
autodiff                             75⭐  Automatic differentiation
Agda_Category_Theory                 17⭐  Formalization in Agda
-Co-AlgebraCheatSheet                 8⭐  Initial algebras / final coalgebras
```

### Ammar Husain (@Cobord)
```
Azimuth-Applied-Category-Theory      6⭐  John Baez's ACT course
AKSZ                                 1⭐  Topological field theory
BookDrafts                           2⭐  SUSY field theories, integrable physics
```

### Benjamin Merlin Bumpus (@benjaminmerlinbumpus)
```
StructuredDecompositions.jl          AlgebraicJulia sheaves for decision problems
composing-algorithms                 Blog on algorithmic composition
```

---

## December 2025 Simultaneity

### DisCoPy Merged PRs (Dec 17-18, 2025)
```
2025-12-18T14:08:55Z: PR #302 by colltoaction - Fix generic type handling
2025-12-18T08:45:16Z: PR #303 by colltoaction - Fix autoray dependency
2025-12-17T07:26:33Z: PR #298 by y-richie-y - quimb tensor network fix
```

### music-topos Creation (Dec 12-21, 2025)
```
Dec 12: Gay.jl color foundation
Dec 17: First Mazzola/topos mention
Dec 20: Sonic Pi + Overtone implementation (bmorphism: 1 contribution)
Dec 21: DuckDB meta-analysis, Rubato discovery
```

---

## DisCoPy Module Structure
```
discopy/
├── monoidal.py      # Monoidal categories
├── braided.py       # Braided monoidal
├── balanced.py      # Balanced categories
├── compact.py       # Compact closed
├── closed.py        # Closed categories
├── frobenius.py     # Frobenius algebras
├── pivotal.py       # Pivotal categories
├── markov.py        # Markov categories
├── hypergraph.py    # Hypergraph categories
├── tensor.py        # Tensor network backend
├── quantum/         # Quantum circuits
├── grammar/         # Categorical grammar (QNLP)
└── drawing/         # String diagram rendering
```

---

## Structural Correspondence

```
DisCoPy (Python)           AlgebraicJulia (Julia)        music-topos (Ruby/Clj)
─────────────────────────────────────────────────────────────────────────────────
monoidal.py           ←→   Catlab.jl                ←→   free_monad.rb
compact.py            ←→   Catlab (compact closed)  ←→   pattern_runs_on_matter.rb
quantum/              ←→   QuantumClifford.jl       ←→   quantum_patterns
tensor.py             ←→   ACSets.jl                ←→   rubato_bridge.rb
grammar/              ←→   GATlab.jl                ←→   world_broadcast.rb
                           StructuredDecomp.jl      ←→   rama_acset_parallel.jl
```

---

## The Topos Triangle

```
            DisCoPy (Python)
               ╱    ╲
              ╱      ╲
             ╱        ╲
    ACT Papers ←──────→ Rubato Composer (Java)
    (bgavran)            (Mazzola/Milmeister)
             ╲        ╱
              ╲      ╱
               ╲    ╱
         AlgebraicJulia
               │
               ↓
          music-topos
    (Gay.jl colors + sound)
```

---

## Cloned Repositories

```bash
~/worlds/o/
├── discopy/                    # DisCoPy source
├── rubato-composer/            # Mazzola's implementation
├── StructuredDecompositions.jl # Bumpus sheaves
├── aloksingh/                  # aloksingh repos
│   ├── cesium/
│   ├── clojure/
│   ├── jedis/
│   └── ...
└── overtone/                   # Clojure audio
```

---

## Key Insight: The Simultaneity Surface

The December 2025 period shows convergent activity:
1. **DisCoPy** advancing quantum/tensor integration (y-richie-y, colltoaction)
2. **music-topos** discovering categorical music theory (Mazzola → Rubato)
3. **bmorphism** following this exact network (AlgebraicJulia, toumix, bgavran)

The "newtheory" people are the **applied category theory** researchers:
- Bruno Gavranović (categorical deep learning)
- Alexis Toumi (categorical QNLP)
- Benjamin Bumpus (structured decompositions)
- Ammar Husain (AKSZ, Azimuth)

All connected through the bmorphism following graph to:
- TeglonLabs (mathpix-gem, seed 1069)
- modelcontextprotocol (MCP)
- AlgebraicJulia ecosystem

---

## See Also

- `GENESIS_QUERY_PATTERN.md` - How we discovered this
- `.ruler/skills/rubato-composer/SKILL.md` - Rubato integration
- `lib/rubato_bridge.rb` - Form/Denotator → Sonic Pi
