# MINUS Skill Lattice

> *"The validators form a lattice. Each node a checkpoint, each edge a verification path."*

**Seed**: 137508 | **Date**: 2025-12-30

---

## Complete MINUS (-1) Skill Color Assignment

All 29 MINUS validators with deterministic Gay.jl colors (seed=137508, OKHSL color space):

| # | Skill | Hex | Swatch | Domain | Triad Partner (+1) | Triad Partner (0) |
|---|-------|-----|--------|--------|-------------------|-------------------|
| 1 | `move-smith-fuzzer` | `#B0285F` | 🟪 | Move/Aptos | `aptos-gf3-society` | `move-narya-bridge` |
| 2 | `narya-proofs` | `#77DEB1` | 🟩 | Proof/HOTT | `lean4-automation` | `coq-verification` |
| 3 | `sheaf-cohomology` | `#8ADB6E` | 🟩 | Topology | `betti-generator` | `structured-decomp` |
| 4 | `segal-types` | `#3A71C0` | 🟦 | ∞-Categories | `directed-hott` | `rezk-completion` |
| 5 | `synthetic-adjunctions` | `#2A7AE3` | 🟦 | Type Theory | `kan-extensions` | `covariant-fibrations` |
| 6 | `cargo-rust` | `#D6DB4C` | 🟨 | Build | `code-generation` | `ci-coordination` |
| 7 | `blackhat-go` | `#6638C2` | 🟪 | Security | `penetration-gen` | `threat-model` |
| 8 | `clj-kondo-3color` | `#AF100A` | 🟥 | Lint | `code-formatting` | `style-guide` |
| 9 | `persistent-homology` | `#AD90E0` | 🟪 | TDA | `filtration-gen` | `barcode-coord` |
| 10 | `open-games` | `#C30F2D` | 🟥 | Game Theory | `strategy-gen` | `nash-equilibrium` |
| 11 | `bisimulation-game` | `#969D34` | 🟨 | Process | `process-creation` | `process-sync` |
| 12 | `covariant-fibrations` | `#61BFE7` | 🟦 | Fibrations | `type-generation` | `transport-coord` |
| 13 | `kan-extensions` | `#79EBDD` | 🟦 | Universal | `lan-generator` | `ran-mediator` |
| 14 | `temporal-coalgebra` | `#D7D085` | 🟨 | Streams | `stream-gen` | `crdt-vterm` |
| 15 | `yoneda-directed` | `#E146A8` | 🟪 | Yoneda | `representable-gen` | `presheaf-coord` |
| 16 | `code-review` | `#0BAD20` | 🟩 | Review | `pr-creation` | `review-coord` |
| 17 | `keychain-secure` | `#86DC73` | 🟩 | Credentials | `key-generation` | `secret-rotation` |
| 18 | `qa-regression` | `#8E7526` | 🟫 | Testing | `test-generation` | `coverage-coord` |
| 19 | `self-validation-loop` | `#65DBDE` | 🟦 | Self-Check | `self-improvement` | `feedback-coord` |
| 20 | `excellence-gradient` | `#F2E388` | 🟨 | Quality | `quality-gen` | `metric-coord` |
| 21 | `cybernetic-immune` | `#1767B8` | 🟦 | Immune | `antigen-gen` | `tolerance-coord` |
| 22 | `fokker-planck-analyzer` | `#D04158` | 🟥 | Dynamics | `langevin-gen` | `entropy-coord` |
| 23 | `influence-propagation` | `#C42990` | 🟪 | Graph | `seed-selection` | `cascade-coord` |
| 24 | `ramanujan-expander` | `#ECEF73` | 🟨 | Expanders | `graph-generation` | `spectral-coord` |
| 25 | `padic-ultrametric` | `#7E3CEA` | 🟪 | p-adic | `padic-gen` | `distance-coord` |
| 26 | `intent-sink` | `#F04E5B` | 🟥 | Intents | `intent-creation` | `anoma-coord` |
| 27 | `interaction-nets` | `#E97C89` | 🟧 | Nets | `net-generation` | `reduction-coord` |
| 28 | `triangle-sparsifier` | `#69E686` | 🟩 | Sparsify | `graph-gen` | `sparsity-coord` |
| 29 | `dialectica` | `#5245E5` | 🟦 | Proofs | `proof-generation` | `dialectica-coord` |

**Color Generation**: `gay_seed(137508)` → `palette(n=29, start_index=1)`

---

## Lattice Structure

### Verification Hierarchy

```
                    ┌─────────────────────┐
                    │   move-smith-fuzzer │
                    │       #B0285F       │
                    └──────────┬──────────┘
                               │
           ┌───────────────────┼───────────────────┐
           │                   │                   │
           ▼                   ▼                   ▼
    ┌──────────────┐   ┌──────────────┐   ┌──────────────┐
    │ narya-proofs │   │sheaf-cohomol │   │ cargo-rust   │
    │   #77DEB1    │   │   #8ADB6E    │   │   #D6DB4C    │
    └──────┬───────┘   └──────┬───────┘   └──────┬───────┘
           │                  │                   │
           ▼                  ▼                   ▼
    ┌──────────────┐   ┌──────────────┐   ┌──────────────┐
    │ segal-types  │   │ persistent-  │   │ blackhat-go  │
    │   #3A71C0    │   │  homology    │   │   #6638C2    │
    └──────┬───────┘   │   #AD90E0    │   └──────┬───────┘
           │           └──────────────┘          │
           │                                     │
           ▼                                     ▼
    ┌──────────────┐                     ┌──────────────┐
    │  synthetic-  │                     │clj-kondo-3clr│
    │ adjunctions  │                     │   #AF100A    │
    │   #2A7AE3    │                     └──────────────┘
    └──────────────┘
```

### Domain Clusters

#### Cluster 1: Type Theory / ∞-Categories

```
segal-types (#3A71C0) ←→ synthetic-adjunctions (#2A7AE3)
         ↑                        ↑
         │                        │
    yoneda-directed          kan-extensions
      (#E146A8)                (#79EBDD)
         │                        │
         └────────┬───────────────┘
                  │
          covariant-fibrations
              (#61BFE7)
```

#### Cluster 2: Topology / TDA

```
sheaf-cohomology (#8ADB6E) ←→ persistent-homology (#AD90E0)
                    ↑
                    │
             triangle-sparsifier
                 (#69E686)
```

#### Cluster 3: Security / Build

```
cargo-rust (#D6DB4C) ←→ blackhat-go (#6638C2)
         │                    │
         ▼                    ▼
    code-review          qa-regression
     (#0BAD20)            (#8E7526)
         │                    │
         └────────┬───────────┘
                  │
           clj-kondo-3color
              (#AF100A)
```

#### Cluster 4: Game Theory / Process

```
open-games (#C30F2D) ←→ bisimulation-game (#969D34)
                             ↑
                             │
                    interaction-nets
                       (#E97C89)
```

#### Cluster 5: Dynamics / Probability

```
fokker-planck-analyzer (#D04158) ←→ temporal-coalgebra (#D7D085)
                                            ↑
                                            │
                                    langevin-dynamics
                                      (ERGODIC partner)
```

---

## Complete Triad Table

### Move/Aptos Triads

| Triad | PLUS (+1) | ERGODIC (0) | MINUS (-1) | Sum |
|-------|-----------|-------------|------------|-----|
| Core | `aptos-gf3-society` | `move-narya-bridge` | `move-smith-fuzzer` | 0 ✓ |
| Governance | `aptos-governance` | `datalog-fixpoint` | `merkle-validation` | 0 ✓ |
| Staking | `staking-pool` | `reward-coord` | `slashing-validator` | 0 ✓ |

### Type Theory Triads

| Triad | PLUS (+1) | ERGODIC (0) | MINUS (-1) | Sum |
|-------|-----------|-------------|------------|-----|
| ∞-Cat | `directed-hott` | `rezk-completion` | `segal-types` | 0 ✓ |
| Adjunction | `lan-generator` | `ran-mediator` | `synthetic-adjunctions` | 0 ✓ |
| Fibration | `type-generation` | `transport-coord` | `covariant-fibrations` | 0 ✓ |
| Yoneda | `representable-gen` | `presheaf-coord` | `yoneda-directed` | 0 ✓ |
| Universal | `colimit-gen` | `limit-coord` | `kan-extensions` | 0 ✓ |

### Topology Triads

| Triad | PLUS (+1) | ERGODIC (0) | MINUS (-1) | Sum |
|-------|-----------|-------------|------------|-----|
| Sheaves | `sheaf-gen` | `structured-decomp` | `sheaf-cohomology` | 0 ✓ |
| TDA | `filtration-gen` | `barcode-coord` | `persistent-homology` | 0 ✓ |
| Sparsify | `graph-gen` | `sparsity-coord` | `triangle-sparsifier` | 0 ✓ |

### Security Triads

| Triad | PLUS (+1) | ERGODIC (0) | MINUS (-1) | Sum |
|-------|-----------|-------------|------------|-----|
| Build | `code-generation` | `ci-coordination` | `cargo-rust` | 0 ✓ |
| Pentest | `exploit-gen` | `threat-model` | `blackhat-go` | 0 ✓ |
| Lint | `code-formatting` | `style-guide` | `clj-kondo-3color` | 0 ✓ |
| Review | `pr-creation` | `review-coord` | `code-review` | 0 ✓ |
| Test | `test-generation` | `coverage-coord` | `qa-regression` | 0 ✓ |

### Game Theory Triads

| Triad | PLUS (+1) | ERGODIC (0) | MINUS (-1) | Sum |
|-------|-----------|-------------|------------|-----|
| Games | `strategy-gen` | `nash-equilibrium` | `open-games` | 0 ✓ |
| Process | `process-creation` | `process-sync` | `bisimulation-game` | 0 ✓ |
| Nets | `net-generation` | `reduction-coord` | `interaction-nets` | 0 ✓ |

### Dynamics Triads

| Triad | PLUS (+1) | ERGODIC (0) | MINUS (-1) | Sum |
|-------|-----------|-------------|------------|-----|
| FP | `langevin-gen` | `entropy-coord` | `fokker-planck-analyzer` | 0 ✓ |
| Stream | `stream-gen` | `crdt-vterm` | `temporal-coalgebra` | 0 ✓ |
| Proof | `proof-generation` | `dialectica-coord` | `dialectica` | 0 ✓ |

### Graph Triads

| Triad | PLUS (+1) | ERGODIC (0) | MINUS (-1) | Sum |
|-------|-----------|-------------|------------|-----|
| Cascade | `seed-selection` | `cascade-coord` | `influence-propagation` | 0 ✓ |
| Expander | `graph-generation` | `spectral-coord` | `ramanujan-expander` | 0 ✓ |
| p-adic | `padic-gen` | `distance-coord` | `padic-ultrametric` | 0 ✓ |

### Self-Reference Triads

| Triad | PLUS (+1) | ERGODIC (0) | MINUS (-1) | Sum |
|-------|-----------|-------------|------------|-----|
| Quality | `quality-gen` | `metric-coord` | `excellence-gradient` | 0 ✓ |
| Self | `self-improvement` | `feedback-coord` | `self-validation-loop` | 0 ✓ |
| Immune | `antigen-gen` | `tolerance-coord` | `cybernetic-immune` | 0 ✓ |
| Creds | `key-generation` | `secret-rotation` | `keychain-secure` | 0 ✓ |
| Intent | `intent-creation` | `anoma-coord` | `intent-sink` | 0 ✓ |

---

## DuckDB Query: Triad Discovery

```sql
-- Find all valid GF(3) triads
WITH skill_trits AS (
    SELECT
        skill_name,
        trit,
        domain,
        color_hex
    FROM skill_taxonomy
),
potential_triads AS (
    SELECT
        p.skill_name as plus_skill,
        e.skill_name as ergodic_skill,
        m.skill_name as minus_skill,
        p.domain as domain,
        p.trit + e.trit + m.trit as trit_sum
    FROM skill_trits p
    CROSS JOIN skill_trits e
    CROSS JOIN skill_trits m
    WHERE p.trit = 1
      AND e.trit = 0
      AND m.trit = -1
      AND p.domain = e.domain
      AND e.domain = m.domain
)
SELECT
    domain,
    plus_skill,
    ergodic_skill,
    minus_skill,
    'Σ = 0 ✓' as conservation
FROM potential_triads
WHERE trit_sum = 0
ORDER BY domain, plus_skill;
```

---

## Color Lattice Visualization

### HSL Distribution

```
        0°                90°               180°              270°             360°
        │                  │                  │                  │               │
   Red  │     Yellow       │      Green       │      Cyan        │    Blue    Magenta
        │                  │                  │                  │               │
  ──────┼──────────────────┼──────────────────┼──────────────────┼───────────────┤
        │                  │                  │                  │               │
   #B0285F  #D6DB4C  #8ADB6E  #77DEB1  #65DBDE  #3A71C0  #6638C2  #5245E5  #E146A8
   │        │        │        │        │        │        │        │        │
   1        6        3        2       19        4        7       29       15
   move-    cargo-   sheaf-   narya-   self-    segal-   black-   dialec-  yoneda-
   smith    rust     cohom    proofs   valid    types    hat-go   tica     directed
```

### Trit-Color Mapping Rule

```python
def trit_to_hue_range(trit: int) -> tuple[int, int]:
    """Map GF(3) trit to hue range."""
    if trit == 1:    # PLUS/GENERATOR
        return (0, 60)      # Warm: Red-Yellow
    elif trit == 0:  # ERGODIC/COORDINATOR
        return (60, 180)    # Neutral: Yellow-Cyan
    else:            # MINUS/VALIDATOR
        return (180, 300)   # Cold: Cyan-Magenta

# Note: Gay.jl uses golden angle (137.508°) for perceptual spacing
# Colors spread across full spectrum regardless of trit
```

---

## Lattice Adjacency Matrix

Skills are adjacent if they share a triad:

```
                 move-smith  narya  sheaf  segal  synth  cargo  black  kondo  persist
move-smith            -        1      1      0      0      0      0      0       0
narya-proofs          1        -      0      1      0      0      0      0       0
sheaf-cohomology      1        0      -      0      0      0      0      0       1
segal-types           0        1      0      -      1      0      0      0       0
synthetic-adj         0        0      0      1      -      0      0      0       0
cargo-rust            0        0      0      0      0      -      1      1       0
blackhat-go           0        0      0      0      0      1      -      0       0
clj-kondo-3color      0        0      0      0      0      1      0      -       0
persistent-homology   0        0      1      0      0      0      0      0       -
```

---

## Move 2.3 Integration Points

### Skills Ready for Signed Integers

| Skill | i8 | i32 | i64 | i128 | Ready |
|-------|-----|-----|-----|------|-------|
| `move-smith-fuzzer` | ✓ | ✓ | ✓ | ✓ | Yes |
| `narya-proofs` | ✓ | ✓ | - | - | Yes |
| `sheaf-cohomology` | - | ✓ | - | - | Yes |
| `cargo-rust` | - | - | - | - | N/A |
| `blackhat-go` | - | - | - | - | N/A |

### Signed Integer Test Vectors

```move
// Test vectors for MINUS validators
#[test]
fun test_signed_boundaries() {
    // i8 boundaries for trit storage
    assert!(MIN_I8 == -128, 0);
    assert!(MAX_I8 == 127, 0);

    // Trit range
    let minus: i8 = -1;
    let ergodic: i8 = 0;
    let plus: i8 = 1;

    // Conservation
    assert!(minus + ergodic + plus == 0, 0);
}
```

---

*Seed: 137508 | Colors: 29 | Triads: 25 | Conservation: VERIFIED*
