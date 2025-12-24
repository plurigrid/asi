# Theorem Prover Skills Manifest

**Date**: 2025-12-22
**Status**: Saturated from plurigrid/asi
**Total Skills Installed**: 218+

---

## Executive Summary

This manifest documents the theorem prover skills installed from plurigrid/asi into `~/.codex/skills/`. These skills integrate with the music-topos interaction entropy system for:

1. **Deterministic tactic generation** (SplitMix64 seeding)
2. **GF(3) balanced proof search** (generator/coordinator/validator triads)
3. **Self-avoiding walk** (no redundant proof attempts)
4. **LHoTT formalization** (cohesive + linear modalities)

---

## Core Theorem Prover Skills

### Tier 1: Formal Verification

| Skill | GF(3) Trit | Description | Technologies |
|-------|------------|-------------|--------------|
| **proofgeneral-narya** | -1 (Validator) | Higher-dimensional type theory | Proof General + Narya |
| **world-e (infinity-cosmos)** | 0 (Coordinator) | Lean4 ∞-categories | Lean4 + Mathlib |
| **world-r (rzk)** | +1 (Generator) | Simplicial HoTT | Rzk (Haskell) |

### Tier 2: Sheaf & Topological Methods

| Skill | GF(3) Trit | Description | Technologies |
|-------|------------|-------------|--------------|
| **sheaf-uncertainty** | -1 (Validator) | Bayesian sheaf neural networks | PyTorch |
| **koho-sheafnn** | -1 (Validator) | Rust sheaf neural networks | Rust + Candle |
| **topomodelx-hodge** | 0 (Coordinator) | Hodge Laplacian TDL | TopoBenchmarkX |
| **topological-dataloader** | -1 (Validator) | Batched complex loading | TopoModelX |

### Tier 3: Categorical Diagrams

| Skill | GF(3) Trit | Description | Technologies |
|-------|------------|-------------|--------------|
| **discopy-operads** | 0 (Coordinator) | String diagrams + operads | DisCoPy |
| **discopy-functor** | +1 (Generator) | Functorial diagram generation | DisCoPy |
| **acsets** | 0 (Coordinator) | Algebraic databases (C-sets) | AlgebraicJulia |

### Tier 4: MCP Integration

| Skill | GF(3) Trit | Description | Technologies |
|-------|------------|-------------|--------------|
| **mcp-fastpath** | +1 (Generator) | Direct FastMCP tool serving | MCP Protocol |
| **mcp-orchestrator** | 0 (Coordinator) | Multi-tool orchestration | MCP Protocol |

### Tier 5: Specialized Verification

| Skill | GF(3) Trit | Description | Technologies |
|-------|------------|-------------|--------------|
| **spi-parallel-verify** | 0 (Coordinator) | Strong Parallelism Invariance | SplitMix64 |
| **self-validation-loop** | -1 (Validator) | Triadic self-verification | Ruby |
| **hyjax-relational** | +1 (Generator) | Relational thinking + JAX | HyJAX |
| **nerv** | 0 (Coordinator) | Neural verification | TBD |

---

## GF(3) Conservation Triads for Theorem Proving

```
# Core Formal Verification Triad
proofgeneral-narya (-1) ⊗ infinity-cosmos (0) ⊗ rzk (+1) = 0 ✓

# Sheaf Neural Network Triad
sheaf-uncertainty (-1) ⊗ topomodelx-hodge (0) ⊗ mcp-fastpath (+1) = 0 ✓

# Categorical Diagram Triad
topological-dataloader (-1) ⊗ discopy-operads (0) ⊗ discopy-functor (+1) = 0 ✓

# MCP Theorem Proving Triad
koho-sheafnn (-1) ⊗ mcp-orchestrator (0) ⊗ hyjax-relational (+1) = 0 ✓

# Self-Verification Triad
self-validation-loop (-1) ⊗ spi-parallel-verify (0) ⊗ gay-mcp (+1) = 0 ✓
```

---

## Integration with MLX Prover

The installed skills integrate with `scripts/mlx_prover.py`:

```python
# Tactic roles mapped to skill triads
TACTIC_ROLES = {
    "generator": {  # +1 (PLUS)
        "trit": 1,
        "tactics": ["apply", "intro", "refine", "exact", "constructor"],
        "skills": ["discopy-functor", "mcp-fastpath", "hyjax-relational"]
    },
    "coordinator": {  # 0 (ERGODIC)
        "trit": 0,
        "tactics": ["have", "suffices", "calc", "show", "obtain"],
        "skills": ["discopy-operads", "acsets", "spi-parallel-verify"]
    },
    "validator": {  # -1 (MINUS)
        "trit": -1,
        "tactics": ["simp", "decide", "norm_num", "ring", "linarith"],
        "skills": ["proofgeneral-narya", "sheaf-uncertainty", "koho-sheafnn"]
    },
}
```

---

## LHoTT Cohesive Linear Integration

From `lhott-cohesive-linear` skill:

| Modality | Symbol | Action | Theorem Prover Use |
|----------|--------|--------|-------------------|
| Sharp | ♯ | Discretize | Extract trit from goal state |
| Flat | ♭ | Embed continuously | Full proof state embedding |
| Shape | ʃ | Quotient by homotopy | Proof trajectory class |
| Linear | ♮ | Self-adjoint tangent | One-use tactic (no backtracking) |

---

## Proof Tree ACSet Schema

From `lib/proof_tree_acset.jl`:

```julia
@present SchProofTree(FreeSchema) begin
    # Objects
    Goal::Ob
    Tactic::Ob
    ProofState::Ob
    
    # Morphisms
    goal_parent::Hom(Goal, Goal)
    tactic_source::Hom(Tactic, Goal)
    tactic_targets::Hom(Tactic, Goal)
    
    # Interaction Entropy Attributes
    goal_seed::Attr(Goal, Seed)
    goal_trit::Attr(Goal, Trit)
    tactic_trit::Attr(Tactic, Trit)  # +1 gen, 0 coord, -1 val
end
```

---

## World Skills Summary

| World | Path | Contents | Lean4/HoTT |
|-------|------|----------|------------|
| **e** | `~/worlds/e` | InfinityCosmos (∞-categories), Yoneda | Lean4 |
| **r** | `~/worlds/r` | Rzk (simplicial HoTT) | Rzk |
| **a** | `~/worlds/a` | AlgebraicJulia (Catlab, ACSets) | Julia |

---

## Installation Commands

```bash
# Already installed (218+ skills)
ls ~/.codex/skills/ | wc -l
# → 218

# Newly installed theorem prover skills
python3 ~/.claude/skills/skill-installer/scripts/install-skill-from-github.py \
  --repo plurigrid/asi --path skills/discopy-functor
python3 ~/.claude/skills/skill-installer/scripts/install-skill-from-github.py \
  --repo plurigrid/asi --path skills/hyjax-relational
python3 ~/.claude/skills/skill-installer/scripts/install-skill-from-github.py \
  --repo plurigrid/asi --path skills/mcp-orchestrator
python3 ~/.claude/skills/skill-installer/scripts/install-skill-from-github.py \
  --repo plurigrid/asi --path skills/nerv
```

---

## Justfile Integration

Add to `justfile`:

```just
# ═══════════════════════════════════════════════════════════════════════════════
# THEOREM PROVER SKILL TRIADS
# ═══════════════════════════════════════════════════════════════════════════════

# List all theorem prover skills
theorem-prover-skills:
    @echo "=== Theorem Prover Skills (GF(3) Triads) ==="
    @echo ""
    @echo "Formal Verification:"
    @echo "  proofgeneral-narya (-1) ⊗ infinity-cosmos (0) ⊗ rzk (+1) = 0 ✓"
    @echo ""
    @echo "Sheaf Neural Networks:"
    @echo "  sheaf-uncertainty (-1) ⊗ topomodelx-hodge (0) ⊗ mcp-fastpath (+1) = 0 ✓"
    @echo ""
    @echo "Categorical Diagrams:"
    @echo "  topological-dataloader (-1) ⊗ discopy-operads (0) ⊗ discopy-functor (+1) = 0 ✓"

# Run MLX prover demo with theorem prover skills
mlx-prove-demo goal="∀ n : ℕ, n + 0 = n":
    python3 scripts/mlx_prover.py --goal "{{goal}}" --steps 6

# Verify GF(3) conservation in proof attempts
verify-proof-gf3:
    python3 scripts/mlx_prover.py --json | jq '.triplets[] | select(.gf3_conserved == false)'
```

---

## Next Steps

1. [ ] Download MLX model weights (when disk space available)
2. [ ] Integrate with LeanDojo/Pantograph for live Lean4 REPL
3. [ ] Connect to PutnamBench for benchmarking
4. [ ] Build proof tree visualization with DisCoPy

---

## References

- [plurigrid/asi](https://github.com/plurigrid/asi) - ASI Skills Repository
- [Goedel-Prover-V2](https://huggingface.co/Goedel-LM/Goedel-Prover-V2-8B) - MLX-convertible
- [Kimina-Prover](https://huggingface.co/AI-MO/Kimina-Prover-Distill-1.7B) - Lightweight
- [DeepSeek-Prover-V2](https://huggingface.co/deepseek-ai/DeepSeek-Prover-V2-7B) - RL-trained
