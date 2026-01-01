# 🎭 DISSONANCE MATRIX: Conceptual Tensions Across Discovered Repos

> *Where ideas collide, insight crystallizes*

## Overview

This matrix maps conceptual tensions and contradictions between discovered repos/domains. 
Like DuckLake creates snapshots on each insert, we create **harmonization snapshots** on each conceptual evolution.

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         DISSONANCE SPECTRUM                                  │
├─────────────────────────────────────────────────────────────────────────────┤
│  CONSONANT ◄─────────────────────────────────────────────────► DISSONANT    │
│  (shared axioms)                                    (incompatible worldviews)│
│                                                                              │
│  DisCoPy ↔ HoTT    │ ALife ↔ Active Inference │ GFlowNets ↔ Particle-Life  │
│  (categories)      │ (emergence vs prediction)│ (diversity vs maximization) │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 🔴 HIGH DISSONANCE PAIRS

### 1. GFlowNets vs Reinforcement Learning
**Repos**: `zdhNarsil/Awesome-GFlowNets` vs standard RL frameworks

| Aspect | GFlowNets | Reinforcement Learning |
|--------|-----------|----------------------|
| **Objective** | Sample proportionally to reward | Maximize cumulative reward |
| **Diversity** | Intrinsic (explores modes) | Must be engineered (entropy bonus) |
| **Termination** | Generates complete objects | Episodic/continuing |
| **Flow equation** | F(s) = R(s) at terminal | Bellman equation |

**Tension**: RL seeks the **single best** outcome; GFlowNets seek **all good** outcomes proportionally.
**Harmonization**: Both are Markov decision processes with different terminal conditions.

---

### 2. HoTT Univalence vs Set-Theoretic Equality
**Repos**: `HoTT/Coq-HoTT` vs classical mathematics formalization

| Aspect | HoTT/Univalence | Set Theory |
|--------|-----------------|------------|
| **Equality** | Paths = equivalences | Leibniz equality |
| **Isomorphism** | Identical to equality | Distinct from equality |
| **Structure** | Higher-dimensional paths | Flat propositions |
| **Transport** | Data moves along paths | Requires explicit coercion |

**Tension**: In HoTT, `A ≃ B ⟹ A = B`. In set theory, isomorphic ≠ equal.
**Harmonization**: Both satisfy internal logic; HoTT extends set theory's propositions to spaces.

---

### 3. Active Inference vs Particle-Life Emergence
**Repos**: `ActiveInferenceInstitute/CEREBRUM` vs `hunar4321/particle-life`

| Aspect | Active Inference | Particle-Life |
|--------|------------------|---------------|
| **Agency** | Minimizes free energy | No explicit agency |
| **Goals** | Predictive processing | None (emergent patterns) |
| **Dynamics** | Bayesian belief updating | Force-based physics |
| **Emergence** | Top-down (priors drive behavior) | Bottom-up (rules → patterns) |

**Tension**: Active inference presumes goals; particle-life shows goals can emerge from goalless rules.
**Harmonization**: Free energy minimization could describe attractor states in particle dynamics.

---

### 4. CEREBRUM Case System vs Standard Type Theory
**Repos**: `ActiveInferenceInstitute/CEREBRUM` vs `HoTT/Coq-HoTT`

| Aspect | CEREBRUM Cases | Type Theory |
|--------|----------------|-------------|
| **Transformation** | Linguistic cases (NOM, ACC, DAT) | Type constructors |
| **Semantics** | Pragmatic/contextual | Structural/compositional |
| **Change** | Case morphology on models | Explicit type coercion |
| **Precision** | Metaphorical mapping | Formal specification |

**Tension**: CEREBRUM uses linguistic metaphor where type theory demands precision.
**Harmonization**: Cases as dependent types over context; case transitions as path transport.

---

## 🟡 MEDIUM DISSONANCE PAIRS

### 5. DisCoPy String Diagrams vs HoTT Path Types
**Repos**: `discopy/discopy` vs `HoTT/Coq-HoTT`

| Aspect | DisCoPy | HoTT |
|--------|---------|------|
| **1-cells** | Arrows (morphisms) | Paths (identities) |
| **2-cells** | Natural transformations | Homotopies |
| **Composition** | Sequential (>>), parallel (@) | Path concatenation |
| **Semantics** | Functorial (to Hilb, Tensor) | Internal (univalence) |

**Tension**: DisCoPy treats diagrams as syntax; HoTT treats paths as propositions.
**Harmonization**: Both are ∞-categorical; DisCoPy's functors land in HoTT's universe.

---

### 6. Left/Right Duals in Quantum vs Directed Type Theory
**Repos**: `discopy/discopy` (rigid categories) vs directed type theory concepts

| Aspect | DisCoPy Duals | Directed Types |
|--------|---------------|----------------|
| **Left adjoint** | a.l (cup consumer) | Variance inversion |
| **Right adjoint** | a.r (cap producer) | Covariance |
| **Collapse** | In compact closed, l=r | In symmetric, l≃r |
| **Physical** | Time reversal? | Contravariance |

**Tension**: Quantum needs distinct L/R for certain protocols; classical often collapses them.
**Harmonization**: Pivotal categories where l=r unify via coherent isomorphisms.

---

### 7. Composio Tool Router vs MCP Server Patterns
**Repos**: `ComposioHQ/composio` vs standard MCP implementations

| Aspect | Composio Tool Router | Standard MCP |
|--------|---------------------|--------------|
| **Discovery** | NL search + filtering | Explicit tool listing |
| **Auth** | OAuth cascade pattern | Session-based |
| **Execution** | Workbench summarization | Direct response |
| **Mode** | MCP Server + Native dual | Single mode |

**Tension**: Composio abstracts tool selection; pure MCP requires explicit tool choice.
**Harmonization**: Tool Router as higher-order MCP that orchestrates lower MCP servers.

---

## 🟢 LOW DISSONANCE (CONSONANT PAIRS)

### 8. GraphCast Mesh GNN vs DisCoPy Categories
**Repos**: `google-deepmind/graphcast` vs `discopy/discopy`

| Aspect | GraphCast | DisCoPy |
|--------|-----------|---------|
| **Structure** | Icosahedral mesh | String diagrams |
| **Flow** | Grid2Mesh → Process → Mesh2Grid | Dom → Morphism → Cod |
| **Composition** | Layer stacking | Sequential (>>) |
| **Semantics** | Physical prediction | Categorical functor |

**Consonance**: Both are message-passing on graphs with compositional structure.
**Synthesis**: Diagrams as mesh refinement; functors as learned GNN weights.

---

### 9. AlgebraicJulia Petri.jl vs DisCoPy Hypergraph
**Repos**: `AlgebraicJulia/Petri.jl` vs `discopy/discopy`

| Aspect | Petri.jl | DisCoPy Hypergraph |
|--------|----------|-------------------|
| **Nodes** | Places + Transitions | Systems + Processes |
| **Edges** | Token flow | Wires |
| **Rewriting** | DPO on ACSets | Diagram composition |
| **Semantics** | Rate equations | Tensor contraction |

**Consonance**: Both are compositional open systems with categorical semantics.
**Synthesis**: Petri nets as special hypergraph diagrams with reaction semantics.

---

## Harmonization Snapshot Protocol

Like DuckLake snapshots data on each INSERT, we snapshot conceptual state on each evolution:

```python
class ConceptualSnapshot:
    """DuckLake-style snapshot for conceptual evolution."""
    
    def __init__(self, version: int):
        self.version = version
        self.timestamp = datetime.now()
        self.dissonances: dict[tuple[str,str], float] = {}
        self.harmonizations: list[str] = []
        self.new_concepts: list[str] = []
    
    def record_dissonance(self, domain_a: str, domain_b: str, 
                          tension: float, resolution: str):
        """Record a conceptual tension between domains."""
        self.dissonances[(domain_a, domain_b)] = tension
        if resolution:
            self.harmonizations.append(
                f"{domain_a} ↔ {domain_b}: {resolution}"
            )
    
    def evolve(self, new_concept: str) -> 'ConceptualSnapshot':
        """Create new snapshot with evolved concept."""
        next_snap = ConceptualSnapshot(self.version + 1)
        next_snap.dissonances = self.dissonances.copy()
        next_snap.harmonizations = self.harmonizations.copy()
        next_snap.new_concepts = [new_concept]
        return next_snap
```

---

## Dissonance Metrics

```python
def compute_dissonance(repo_a: dict, repo_b: dict) -> float:
    """
    Compute conceptual dissonance between two repos.
    
    Factors:
    - Axiom overlap (fewer shared axioms = more dissonance)
    - Vocabulary overlap (different terms for same concepts)
    - Composition model (how things combine)
    - Goal orientation (what they optimize for)
    """
    axiom_dissonance = 1.0 - jaccard(repo_a['axioms'], repo_b['axioms'])
    vocab_dissonance = semantic_distance(repo_a['terms'], repo_b['terms'])
    compose_dissonance = 0.0 if repo_a['compose'] == repo_b['compose'] else 0.5
    goal_dissonance = 0.0 if repo_a['goal'] == repo_b['goal'] else 0.5
    
    return (axiom_dissonance * 0.3 + 
            vocab_dissonance * 0.3 + 
            compose_dissonance * 0.2 + 
            goal_dissonance * 0.2)
```

---

## DeepWiki Probes Used

| Repo | Status | Key Insight |
|------|--------|-------------|
| `discopy/discopy` | ✅ Indexed | Cups/caps for quantum; functors for semantics |
| `HoTT/Coq-HoTT` | ✅ Indexed | Univalence: equivalence = equality |
| `ActiveInferenceInstitute/CEREBRUM` | ✅ Indexed | Case system as free energy minimization |
| `zdhNarsil/Awesome-GFlowNets` | ✅ Indexed | Sample ∝ reward vs maximize reward |
| `hunar4321/particle-life` | ✅ Indexed | Interaction matrix → emergence |
| `ComposioHQ/composio` | ✅ Indexed | Tool Router with MCP dual mode |
| `google-deepmind/graphcast` | ✅ Indexed | Grid2Mesh→Process→Mesh2Grid GNN |
| `ToposInstitute/poly` | ❌ Not indexed | Visit deepwiki.com to index |
| `AlgebraicJulia/Petri.jl` | ❌ Not indexed | Visit deepwiki.com to index |
| `rzk-lang/rzk` | ❌ Not indexed | Visit deepwiki.com to index |
| `mortberg/cubicaltt` | ❌ Not indexed | Visit deepwiki.com to index |
| `lauriewired/ghidramcp` | ❌ Not indexed | Visit deepwiki.com to index |

---

## Cross-Domain Harmonization Opportunities

### Opportunity 1: Categories as Unifying Language
**Domains**: HoTT, DisCoPy, ACSets, GraphCast
**Synthesis**: All express compositional structure via category theory

### Opportunity 2: Energy/Flow as Dynamics
**Domains**: Active Inference, GFlowNets, Particle-Life, Petri Nets
**Synthesis**: All describe how "stuff" flows through state space

### Opportunity 3: Tool Composition via MCP
**Domains**: Composio, GhidraMCP, ChemMCP, filesystem-mcp
**Synthesis**: MCP as universal adapter for tool orchestration

---

## Next Steps

1. Index missing repos on DeepWiki
2. Build automated dissonance scoring pipeline
3. Create "Harmonization Dance" session format
4. Extend skill with `just harmonize domain-a domain-b` command
