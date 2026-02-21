---
name: norvidize
description: Extract and audit claims for norvid tracking system
---

# Norvidize Skill

Extract claims from documentation, code, and tests into a claim tracking system
based on multicomputational irreducibility -- claims that cannot be reduced to
simpler forms without losing verification guarantees.

## When to Use

- After completing a significant feature
- When auditing documentation accuracy
- Before releases to ensure claims match reality
- When docs/tests/specs diverge from implementation

## Assurance Levels (lowest to highest)

| Level | Meaning | Evidence Required |
|-------|---------|-------------------|
| Mentioned | Just referenced somewhere | Any doc |
| Designed | Has design doc | Design markdown |
| Specified | Has formal spec | Spec file |
| Implemented | Code exists | Source file + symbol |
| Tested | Has passing tests | Test file + test name |
| Proven | Has formal proof | Proof file + theorem |

## Claim Categories

- **Feature**: User-visible functionality
- **Property**: System guarantee (linearizability, durability)
- **Guarantee**: Promise to users
- **Optimization**: Performance improvement
- **Invariant**: Internal system invariant
- **Decision**: Architectural choice with rationale
- **Omission**: Deliberate non-feature

## Covariant Claim Structure

Claims form a presheaf over the assurance poset: higher assurance levels
pull back evidence from lower levels. A Tested claim covariantly transports
its Designed evidence forward.

```
Mentioned -> Designed -> Specified -> Implemented -> Tested -> Proven
```

Each arrow preserves evidence (covariant functor from assurance levels to evidence sets).

## Extraction Process

### 1. Find Candidate Claims

Scan sources for claim candidates:

```bash
grep -r "CLAIM\|GUARANTEE\|INVARIANT" docs/
grep -r "#\[test\]" -A 2 src/ | grep "fn test_"
grep -r "ops/s\|latency\|throughput" docs/
```

### 2. Categorize by Irreducibility

- **Irreducible claims**: Cannot be verified by simpler means (need full test execution)
- **Reducible claims**: Can be statically verified (type checking, linting)
- **Compositional claims**: Verified by composing sub-claim verifications

### 3. Verify Evidence Paths

Before adding at Tested/Implemented level, verify paths exist.

### 4. Downgrade Strategy

If evidence path is uncertain, downgrade assurance level.
Upgrade later when evidence is confirmed.

## Anti-Patterns

- Don't add Tested claims without verifying paths
- Don't skip Designed level -- even Tested claims should have design evidence
- Don't guess component names
