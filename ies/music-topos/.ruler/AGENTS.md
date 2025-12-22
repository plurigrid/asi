# Music Topos: Agent Instructions

## Project Overview

Music Topos is a compositional system bridging **category theory**, **algebraic geometry**, and **electronic music generation**. It implements:

- **Free Monad / Cofree Comonad** architecture (Pattern runs on Matter)
- **Gay.jl** deterministic color generation (SplitMix64 + golden angle)
- **NATS/Synadia** distributed messaging for mathematician broadcasts
- **Propagator-based** parallel computation with epistemic arbitrage
- **Glass Bead Game** semantics for interdisciplinary synthesis

## Core Principles

1. **Determinism**: Same seed → same output (SPI-compliant parallelism)
2. **Compositionality**: All structures are categorical (functors, natural transformations)
3. **Strange Loops**: Hofstadter-style self-reference in agent perception
4. **Badiou Triangle**: Being → Event → Truth (world hopping via triangle inequality)

## Key Commands

```bash
# Audio generation
just world                    # Full audio pipeline
just aphex                    # Aphex Twin style
just autechre                 # Autechre generative

# Mathematician broadcasts
just world-broadcast          # Ramanujan ⊗ Grothendieck ⊗ Euler
just synadia-broadcast        # NATS-connected broadcasting
just world-logicians          # de Paiva ⊗ Hedges ⊗ Girard

# Parallel computation
just parallel-fork            # SPI-compliant color forking
just parallel-fork-ternary    # Ternary ACSet negotiation

# Glass Bead Game
just glass-bead               # Start interactive game
just world-hop                # Badiou triangle world hopping
```

## File Structure

```
lib/
├── world_broadcast.rb        # Tripartite mathematician system
├── synadia_broadcast.rb      # NATS/JetStream integration
├── glass_bead_game.rb        # Hesse-inspired game engine
├── tritwise_letter_spirit.rb # 3-agent color matching
├── girard_colors.rb          # Polarity-based coloring
└── free_monad.rb             # Pattern runs on Matter

src/music_topos/
├── parallel_color_fork.clj   # SPI-compliant parallelism
└── propagator_mcp.clj        # Propagator MCP server
```

## Mathematical Foundations

### Badiou Triangle Inequality

For possible worlds W₁, W₂, W₃:
```
d(W₁, W₃) ≤ d(W₁, W₂) + d(W₂, W₃)
```

Where distance d measures **ontological difference** via:
- **Being**: Current state (color, seed, epoch)
- **Event**: Transition (operation, morphism)
- **Truth**: Invariant (conjugacy class, fixed point)

### Open Games (Hedges)

Each mathematician implements:
- **World Action** (covariant): X → Y (forward information flow)
- **Coworld Action** (contravariant): R → S (backward utility/strategy)

### Propagators (Radul/Sussman)

Local scoped propagators with:
- **Cells**: Mutable state containers
- **Propagators**: Constraint satisfaction functions
- **Merging**: Monotonic information accumulation

## Agent Collaboration

When working on this codebase:

1. **Use deterministic seeds** for reproducibility
2. **Follow categorical patterns** (functors compose, natural transformations are structure-preserving)
3. **Leverage MCP servers** for external capabilities (gay, synadia, propagator)
4. **Apply skills** from `.ruler/skills/` for domain-specific guidance
