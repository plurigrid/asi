---
name: mcp-spec-checker
description: Predicate-level semantic diff for MCP protocol specs. Compares 0618 vs 1125 specs via Narya types, GF(3) evaluators, and Unison-style effects. Use for protocol verification, spec migration, or detecting breaking changes.
model: inherit
tools: read-only
---

# MCP Spec Checker

Semantic diff engine for MCP protocol specifications using three independent verification approaches with mandatory cross-validation.

## Three Verification Approaches

| Approach | File | Trit | Role |
|----------|------|------|------|
| **Narya Types** | `src/mcp_narya_types.py` | -1 (MINUS) | chk/syn/nosyn bidirectional typing |
| **Agent-o-rama Evaluators** | `src/mcp_evaluators.py` | 0 (ERGODIC) | GF(3) predicate evaluation |
| **Unison Effects** | `src/mcp_effects.py` | +1 (PLUS) | Algebraic effect handlers |

GF(3) Conservation: `(-1) + 0 + (+1) = 0 ✓`

## GF(3) Trit Assignments for Predicates

```python
# From src/mcp_spec_predicates.py

PREDICATE_TRITS = {
    # MINUS (-1): Constraint/validation predicates
    "has_required_field": -1,
    "type_matches": -1,
    "schema_valid": -1,
    
    # ERGODIC (0): Coordination predicates
    "version_compatible": 0,
    "capability_negotiated": 0,
    "session_active": 0,
    
    # PLUS (+1): Generation/action predicates
    "tool_invoked": +1,
    "response_emitted": +1,
    "resource_created": +1,
}
```

## Denotation

> **This skill compares MCP protocol specs at the predicate level, detecting semantic differences between versions and generating minimal counterexamples for incompatibilities via cross-validated triadic verification.**

```
SemanticDiff = Inv_0618 △ Inv_1125 (symmetric difference)
Counterexample: min{msg : Inv_0618(msg) ≠ Inv_1125(msg)}
Consensus: ∀ approach ∈ {Narya, Evaluators, Effects}: result_agree
```

## Invariant Set

| Invariant | Definition | Verification |
|-----------|------------|--------------|
| `SpecVersionCompatibility` | Old spec passing → new spec passing OR documented breaking change | Diff analysis |
| `PredicateConsistency` | Same predicate → same trit across versions | Trit comparison |
| `CrossValidationConsensus` | All 3 approaches agree on validity | Bisimulation game |
| `CounterexampleMinimality` | Generated counterexamples are minimal witnesses | Si