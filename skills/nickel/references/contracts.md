# Nickel Contract Library Reference

## Workspace Contracts

### transformation-contracts.ncl

Location: `.topos/nickel/contracts/transformation-contracts.ncl`

| Contract | Purpose | Fields |
|----------|---------|--------|
| `NonEmptyString` | String length > 0 | predicate |
| `ValidIdentifier` | `^[a-zA-Z_][a-zA-Z0-9_]*$` | regex |
| `ValidPath` | `^[a-zA-Z0-9_/.-]+$` | regex |
| `PatternType` | `'identifier \| 'type-identifier \| 'both` | enum |
| `ScopeType` | `'rust-files \| 'cargo-toml \| 'markdown \| 'all` | enum |
| `ValidationGate` | `'cargo-check \| 'cargo-test \| 'cargo-clippy \| 'cargo-fmt` | enum |
| `TransformationPattern` | Rename operation spec | old_name, new_name, pattern_type, scope |
| `TransformationStrategy` | Multi-transform pipeline | name, transforms, validation_level, checkpoint |
| `BalancedTernarySelector` | GF(3) selection | seed (1069), iteration, strategies (array of 3) |
| `TransformationSession` | Complete session state | session_id, variant_path, strategy, operations, status |
| `ValidationResult` | Gate result | gate, passed, output, exit_code, duration_ms |
| `TransformationResult` | Final outcome | session, validation_results, success, rollback_performed |

## Dynamic Sufficiency Levels

From `UnwiringDiagrams.jl/examples/lo_paper/dynamic_sufficiency.jl`:

```
SEMANTICALLY_SUFFICIENT > COMPUTATIONALLY_SUFFICIENT > WEAKLY_SUFFICIENT > NOT_SUFFICIENT
```

### Verification Criteria

1. **NOT_SUFFICIENT**: Different computational behavior
2. **WEAKLY_SUFFICIENT**: Same structure, different labels
3. **COMPUTATIONALLY_SUFFICIENT**: `∀ inputs I: eval(C₁, I) = π(eval(C₂, I))`
4. **SEMANTICALLY_SUFFICIENT**: Same olog types + structure + outputs

## Contract Composition

```nickel
# Intersection (both must pass)
value | Contract1 & Contract2

# Union (one must pass) - via custom contract
let Either = fun c1 c2 =>
  std.contract.from_predicate (fun x =>
    (std.contract.check c1 x) || (std.contract.check c2 x))
```

## Idempotency Property

For dynamically sufficient contracts:
```
∀ c: Contract, ∀ x: (x | c) | c ≡ x | c
```

This ensures transformation chains are stable.
