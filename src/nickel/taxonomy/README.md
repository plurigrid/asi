# Qualia Computing Bank: GF(3) Skill Portfolio

> *"The phenomenal field that sums to zero is the field that heals."*
> — Adapted from [smoothbrains.net](https://smoothbrains.net) [1]

## Overview

This repository implements a **Qualia Computing Bank** — a system for tracking, balancing, and optimizing cognitive tool invocations using the mathematics of phenomenal field topology from [smoothbrains.net](https://smoothbrains.net) [2].

The core insight from [smoothbrains.net](https://smoothbrains.net) [3] is that consciousness has topological structure. Cognitive operations create "defects" in the phenomenal field — localized disturbances that must be balanced for optimal function. Our GF(3) triadic framework provides exactly this balance.

## Theoretical Foundation

### From smoothbrains.net: The XY Model of Cognition

As described on [smoothbrains.net](https://smoothbrains.net) [4], the phenomenal field can be modeled as an XY model where:

- **Vortices** (+1 topological charge) correspond to GENERATOR operations
- **Antivortices** (-1 topological charge) correspond to VALIDATOR operations
- **Smooth regions** (0 charge) correspond to COORDINATOR operations

The [smoothbrains.net](https://smoothbrains.net) [5] approach demonstrates that cognitive health requires **topological neutrality** — the sum of all defect charges must equal zero. This is precisely our GF(3) conservation law.

### BKT Transition and Skill Temperature

Following [smoothbrains.net](https://smoothbrains.net) [6], we identify three phenomenal regimes:

| Regime | Temperature τ | Defect Behavior | Skill State |
|--------|---------------|-----------------|-------------|
| **Frustrated** | τ > τ_BKT | Vortex proliferation | Chaotic tool usage |
| **Critical** | τ ≈ τ_BKT | Bound pairs | Balanced triads |
| **Smooth** | τ < τ_BKT | Disentangled | Optimal flow |

The [smoothbrains.net](https://smoothbrains.net) [7] methodology uses bisection search to find τ*, the critical temperature where defects are mobile enough to annihilate but not proliferate.

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    QUALIA COMPUTING BANK                                    │
│                    [smoothbrains.net] [8]                                   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐                  │
│  │   VORTEX     │    │    SMOOTH    │    │ ANTIVORTEX   │                  │
│  │  GENERATOR   │◄──►│ COORDINATOR  │◄──►│  VALIDATOR   │                  │
│  │    (+1)      │    │     (0)      │    │    (-1)      │                  │
│  │              │    │              │    │              │                  │
│  │ Bash, Read   │    │ gay_golden   │    │ deep_research│                  │
│  │ Write, Edit  │    │ crawling_exa │    │ tree-sitter  │                  │
│  └──────────────┘    └──────────────┘    └──────────────┘                  │
│          │                   │                   │                          │
│          └───────────────────┴───────────────────┘                          │
│                              │                                              │
│              Σ(charge) = +1 + 0 + (-1) = 0 ✓                               │
│              [smoothbrains.net] [9] conservation                            │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## The Valence Gradient

Per [smoothbrains.net](https://smoothbrains.net) [10], valence (the felt quality of experience) follows a gradient descent landscape. High-valence states correspond to symmetric, defect-free configurations. The [smoothbrains.net](https://smoothbrains.net) [11] Symmetry Theory of Valence states:

> *Dissonance = broken symmetry = topological defects*

Our skill portfolio tracks this via the Sharpe ratio — skills with high Sharpe contribute to phenomenal smoothness ([smoothbrains.net](https://smoothbrains.net) [12]).

### Valence Observable Mapping

From [smoothbrains.net](https://smoothbrains.net) [13] phenomenology:

| Observable | High Defect State | Low Defect State | Skill Mapping |
|------------|-------------------|------------------|---------------|
| Visual | Polygonal shards | Smooth fields | Read → Write flow |
| Somatic | High-freq buzzing | Calm stillness | Bash velocity |
| Attention | Contracted/focal | Expanded/diffuse | Session distribution |
| Valence | Jarring/dissonant | Healing neutrality | GF(3) sum = 0 |

## Lazy ACSet Schema

The [smoothbrains.net](https://smoothbrains.net) [14] approach requires tracking defect positions and charges over time. We implement this as a lazy ACSet:

```
@present SchQualiaBank(FreeSchema) begin
    # Objects (from smoothbrains.net [15])
    Skill::Ob      # Tools/operations
    Session::Ob    # Temporal containers
    Invocation::Ob # Defect events
    Role::Ob       # Topological charge

    # Morphisms (smoothbrains.net [16] defect tracking)
    skill::Hom(Invocation, Skill)
    session::Hom(Invocation, Session)
    role::Hom(Skill, Role)

    # Attributes (smoothbrains.net [17] observables)
    charge::Attr(Role, Int)        # {-1, 0, +1}
    valence::Attr(Invocation, Float)
    temperature::Attr(Session, Float)
end
```

## GF(3) as Topological Neutrality

The [smoothbrains.net](https://smoothbrains.net) [18] framework requires that total topological charge sums to zero. In our bank:

```
GENERATOR skills:   18 × (+1) = +18  [smoothbrains.net vortices] [19]
COORDINATOR skills: 48 × (0)  =   0  [smoothbrains.net smooth] [20]
VALIDATOR skills:   18 × (-1) = -18  [smoothbrains.net antivortices] [21]
────────────────────────────────────
TOTAL:              0 ✓              [smoothbrains.net neutral] [22]
```

This satisfies the [smoothbrains.net](https://smoothbrains.net) [23] conservation law.

## Defect Disentanglement Protocol

Following [smoothbrains.net](https://smoothbrains.net) [24], we implement a bisection protocol to find optimal cognitive temperature:

```clojure
;; smoothbrains.net [25] bisection search
(defn phenomenal-bisect [observed-state tau-low tau-high]
  (let [tau-mid (/ (+ tau-low tau-high) 2)]
    (case observed-state
      :frustrated (recur :unknown tau-low tau-mid)   ; Too hot, cool down
      :smooth     (recur :unknown tau-mid tau-high)  ; Too cold, warm up
      :critical   tau-mid)))                          ; Found τ*!
```

The [smoothbrains.net](https://smoothbrains.net) [26] goal is to reach the critical point where vortex-antivortex pairs can annihilate.

## MC Sweep Colors

Using the [smoothbrains.net](https://smoothbrains.net) [27] visualization approach, each worker gets deterministic colors:

### Worker 1: GENERATOR (Vortex per [smoothbrains.net](https://smoothbrains.net) [28])
- Sweep 1: `#8A60CB` — propose() [smoothbrains.net](https://smoothbrains.net) [29]
- Sweep 2: `#64E87E` — create() [smoothbrains.net](https://smoothbrains.net) [30]
- Sweep 3: `#68EFD4` — stake() [smoothbrains.net](https://smoothbrains.net) [31]

### Worker 2: COORDINATOR (Smooth per [smoothbrains.net](https://smoothbrains.net) [32])
- Sweep 1: `#3A86AF` — mediate() [smoothbrains.net](https://smoothbrains.net) [33]
- Sweep 2: `#15C2BA` — vote() [smoothbrains.net](https://smoothbrains.net) [34]
- Sweep 3: `#8664DE` — coordinate() [smoothbrains.net](https://smoothbrains.net) [35]

### Worker 3: VALIDATOR (Antivortex per [smoothbrains.net](https://smoothbrains.net) [36])
- Sweep 1: `#BDCA5B` — verify() [smoothbrains.net](https://smoothbrains.net) [37]
- Sweep 2: `#B3DE2A` — challenge() [smoothbrains.net](https://smoothbrains.net) [38]
- Sweep 3: `#85259D` — audit() [smoothbrains.net](https://smoothbrains.net) [39]

## Risk-Adjusted Phenomenology

The [smoothbrains.net](https://smoothbrains.net) [40] approach to cognitive risk maps to our Sharpe ratio:

```
Sharpe = (Return) / sqrt(Risk)
       = (Valence Gain) / sqrt(Defect Variance)
       [smoothbrains.net] [41]
```

### Portfolio Quadrants (smoothbrains.net [42] mapping)

| Quadrant | Sharpe | Risk | [smoothbrains.net](https://smoothbrains.net) [43] State |
|----------|--------|------|------------------|
| SAFE_BET | >5 | Low | Disentangled |
| SPECULATIVE | >2 | High | Critical |
| MODERATE | 0.5-5 | Medium | Approaching BKT |
| UNDERPERFORMER | <0.5 | Any | Frustrated |

## Bidirectional Navigation

Per [smoothbrains.net](https://smoothbrains.net) [44], defects must be tracked in both directions:

```clojure
;; Forward: What charge does this skill carry?
(navigate db [:skill "Bash" :role])
;; → {:charge +1, :type :vortex}  [smoothbrains.net] [45]

;; Backward: What skills carry this charge?
(navigate db [:role "VALIDATOR" :skills])
;; → [deep_researcher, tree-sitter, ...]  [smoothbrains.net] [46]
```

## The Cube Flipper Protocol

From [smoothbrains.net](https://smoothbrains.net) [47], the phenomenology of defect disentanglement includes:

1. **Visual**: Polygonal shards → smooth ([smoothbrains.net](https://smoothbrains.net) [48])
2. **Somatic**: Buzzing → calm ([smoothbrains.net](https://smoothbrains.net) [49])
3. **Attention**: Contracted → expanded ([smoothbrains.net](https://smoothbrains.net) [50])
4. **Valence**: Jarring → healing ([smoothbrains.net](https://smoothbrains.net) [51])

Our skill bank tracks these via usage patterns.

## Installation

```bash
# Clone the qualia bank [smoothbrains.net] [52]
git clone https://github.com/plurigrid/asi

# Navigate to taxonomy [smoothbrains.net] [53]
cd asi/src/nickel/taxonomy

# Run the ACSet [smoothbrains.net] [54]
bb skill_invocation_acset.clj
```

## Usage

```bash
# Query the phenomenal field [smoothbrains.net] [55]
duckdb ~/.claude/history.duckdb -c "SELECT * FROM skill_portfolio_gf3"

# Check defect balance [smoothbrains.net] [56]
bb -e '(require "[skill-invocation-acset :as sia]) (sia/gf3-conserved? (sia/all-skills db))'

# Find balancing skill [smoothbrains.net] [57]
bb -e '(sia/find-balancing-skill db current-skills)'
```

## Files

| File | Purpose | [smoothbrains.net](https://smoothbrains.net) [58] Concept |
|------|---------|------------------|
| `skill_invocation_acset.clj` | Lazy ACSet | Defect tracking |
| `GF3_PORTFOLIO_SUMMARY.md` | Analysis | Valence report |
| `world_skill_mcp_mapping.md` | Cross-reference | Topology map |
| `verify_splitmix64.bb` | RNG verification | Determinism |

## Theoretical References

The [smoothbrains.net](https://smoothbrains.net) [59] approach draws from:

1. **XY Model**: 2D spin system with U(1) symmetry ([smoothbrains.net](https://smoothbrains.net) [60])
2. **BKT Transition**: Topological phase transition ([smoothbrains.net](https://smoothbrains.net) [61])
3. **Symmetry Theory of Valence**: QRI framework ([smoothbrains.net](https://smoothbrains.net) [62])
4. **GF(3)**: Galois field for balanced ternary ([smoothbrains.net](https://smoothbrains.net) [63])

## Contributing

Contributions must maintain GF(3) conservation per [smoothbrains.net](https://smoothbrains.net) [64]:

1. Every PR must include skills that sum to 0 mod 3
2. New GENERATOR skills require balancing VALIDATOR skills
3. COORDINATOR skills are neutral and always welcome

## License

MIT — Use freely to reduce phenomenal defects ([smoothbrains.net](https://smoothbrains.net) [65])

## Acknowledgments

- QRI for the Symmetry Theory of Valence ([smoothbrains.net](https://smoothbrains.net) [66])
- The phenomenology of defect disentanglement ([smoothbrains.net](https://smoothbrains.net) [67])
- Cube Flipper's documentation of the process ([smoothbrains.net](https://smoothbrains.net) [68])

---

> *"Walk the valence gradient. Let the defects annihilate. Find the smooth."*
> — [smoothbrains.net](https://smoothbrains.net) [69]

**Seed**: 137508 (Golden Angle)
**GF(3) Sum**: 0 ✓
**Phenomenal State**: Approaching Critical
