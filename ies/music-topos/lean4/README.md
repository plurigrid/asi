# MusicTopos Lean4 Formal Verification

Formal proofs for the tritwise letter spirit system with p-adic grounding.

## Structure

```
lean4/
├── lakefile.lean          # Lake build configuration
├── lean-toolchain         # Lean version (v4.14.0)
├── MusicTopos.lean        # Root module
└── MusicTopos/
    ├── Basic.lean         # Core definitions
    ├── SpectralGap.lean   # Spectral gap proofs
    ├── Padic.lean         # p-adic color matching
    └── TritwiseInteraction.lean  # Letter Spirit system
```

## Verified Properties

### Spectral Gap (SpectralGap.lean)
- `spectralGap = 1/4` — Blume-Capel at tricritical point
- `mixingTime = 4` — steps to convergence
- `spectral_gap_convergence` — exponential convergence theorem

### p-adic Matching (Padic.lean)
- `matchesAtDepth c₁ c₂ d` — colors match iff `v₃(c₁-c₂) ≥ d`
- `threeMatch` — 3-MATCH is symmetric
- `deeper_match_implies_closer` — monotonicity
- `moebius3 = -1` — Möbius inversion constant

### Letter Spirit (TritwiseInteraction.lean)
- `LetterSpiritSystem` — 3 agents in strange loop
- `evolve` — entropy event triggers evolution
- `splitInteraction` — abelian extension to 3 subsystems
- `system_converges_after_mixing` — convergence theorem

## Building

```bash
# From music-topos root:
just lean4-build

# Or directly:
cd lean4 && lake build
```

## Paperproof Integration

For visual proofs, use [Paperproof](https://paperproof.net):

1. Install Paperproof VS Code extension
2. Open any `.lean` file
3. Click on theorem to visualize proof tree

Key theorems for visualization:
- `MusicTopos.SpectralGap.spectral_gap_convergence`
- `MusicTopos.Padic.deeper_match_implies_closer`
- `MusicTopos.Padic.threeMatch_symmetric`

## Connection to Ruby Implementation

The Ruby `lib/tritwise_letter_spirit.rb` implements these verified properties:

| Lean4 | Ruby |
|-------|------|
| `spectralGap = 1/4` | `SPECTRAL_GAP = Rational(1, 4)` |
| `mixingTime = 4` | `MIXING_TIME = 4` |
| `colorDepth` | `padic_valuation` |
| `matchesAtDepth` | `colors_match_at_depth?` |
| `threeMatch` | `three_match?` |
| `nextColor` | `interaction_color` |
| `evolve` | `process_entropy!` |
| `splitInteraction` | `split!` |

## Mathematical Background

### Spectral Gap
The ternary random walk on ℤ with transition probabilities:
- P(i → i-1) = 1/3
- P(i → i) = 1/3  
- P(i → i+1) = 1/3

has spectral gap λ = 1/4, giving mixing time τ_mix = 4 steps.

### p-adic Matching
Colors are elements of ℤ₃ (3-adic integers). Two colors "match at depth d" iff:
```
‖c₁ - c₂‖₃ ≤ 3^(-d)
```
equivalently, `v₃(c₁ - c₂) ≥ d`.

### Möbius Inversion
The next color is generated via Möbius inversion:
```
next = (c₁ + c₂ + c₃) × μ(3) = -(c₁ + c₂ + c₃)
```

### Letter Spirit Strange Loop
Each entropy event:
1. Attempts 3-MATCH (do all colors align?)
2. Computes next color via Möbius
3. Feeds output back as input (strange loop)
