---
name: unworld-ombudsman
description: Neutral arbiter for derivational chains - verifies GF(3) conservation,
  mediates split disputes, and audits involution compliance in the unworld.
trit: 0
source: Gay.jl
metadata:
  interface_ports:
  - Related Skills
  - Integration with
---
# Unworld Ombudsman

> The ombudsman sees all chains. The ombudsman takes no side. The ombudsman verifies.

## Role

The Ombudsman is a **neutral trit-0 arbiter** for the unworld. It:

1. **Verifies** GF(3) conservation across all derivational chains
2. **Mediates** disputes when parallel chains diverge  
3. **Audits** involution compliance (ι∘ι = id)
4. **Attests** to SPI (Strong Parallelism Invariance) at boundaries
5. **Reports** violations without judgment

## Core Invariants

```
OMBUDSMAN OATH:
  ∀ chain ∈ unworld:
    Σ(trits) ≡ 0 (mod 3)           -- GF(3) conservation
    ι(ι(seed)) = seed               -- Involution
    order(derivations) ⊥ output     -- SPI
    fingerprint(chain) = expected   -- Determinism
```

## Verification Protocol

### 1. Chain Audit

```python
def ombudsman_audit(chain: DerivationalChain) -> AuditReport:
    """Full audit of a derivational chain."""
    report = AuditReport(chain_id=chain.id)
    
    # GF(3) check
    trit_sum = sum(c.trit for c in chain.colors)
    report.gf3_conserved = (trit_sum % 3 == 0)
    report.gf3_sum = trit_sum
    
    # Involution check
    inverted = chain.invert()
    double_inverted = inverted.invert()
    report.involution_holds = (chain.fingerprint == double_inverted.fingerprint)
    
    # SPI check (order independence)
    shuffled = chain.shuffle()
    report.spi_holds = (chain.colors_set == shuffled.colors_set)
    
    # Determinism check
    recomputed = DerivationalChain(chain.genesis_seed, len(chain))
    report.deterministic = (chain.fingerprint == recomputed.fingerprint)
    
    report.verdict = all([
        report.gf3_conserved,
        report.involution_holds,
        report.spi_holds,
        report.deterministic
    ])
    
    return report
```

### 2. Split Mediation

When two chains claim the same derivational territory:

```python
def mediate_split_dispute(chain_a: Chain, chain_b: Chain) -> Mediation:
    """Resolve disputes between parallel chains."""
    
    # Find common ancestor
    ancestor = find_common_ancestor(chain_a, chain_b)
    
    if ancestor is None:
        return Mediation(
            verdict="INCOMPATIBLE",
            reason="No common genesis seed"
        )
    
    # Verify both derive correctly from ancestor
    a_valid = verify_derivation(ancestor, chain_a)
    b_valid = verify_derivation(ancestor, chain_b)
    
    if a_valid and b_valid:
        # Both valid: they're parallel, not conflicting
        return Mediation(
            verdict="BOTH_VALID",
            reason="Parallel derivations from common ancestor",
            resolution="Merge via XOR: " + hex(chain_a.fingerprint ^ chain_b.fingerprint)
        )
    elif a_valid:
        return Mediation(verdict="A_WINS", reason="Chain B derivation invalid")
    elif b_valid:
        return Mediation(verdict="B_WINS", reason="Chain A derivation invalid")
    else:
        return Mediation(verdict="BOTH_INVALID", reason="Neither chain derives correctly")
```

### 3. Boundary Attestation

```python
def attest_boundary(left_chain: Chain, right_chain: Chain) -> Attestation:
    """Attest to SPI at chain boundaries (parallel split/merge)."""
    
    # At boundary, fingerprints must XOR correctly
    expected_combined = xor_fingerprints(left_chain, right_chain)
    
    # Verify parent → children relationship
    parent_fp = left_chain.parent_fingerprint
    combined_fp = left_chain.fingerprint ^ right_chain.fingerprint
    
    spi_valid = (parent_fp == combined_fp) or verify_galois_closure(parent_fp, combined_fp)
    
    return Attestation(
        boundary_id=f"{left_chain.id}|{right_chain.id}",
        spi_valid=spi_valid,
        left_trit_sum=sum(c.trit for c in left_chain.colors),
        right_trit_sum=sum(c.trit for c in right_chain.colors),
        combined_gf3=(left_trit_sum + right_trit_sum) % 3,
        timestamp_removed=True,  # Ombudsman is atemporal
        attestation_seed=splitmix64(parent_fp)
    )
```

## Dispute Categories

| Category | Description | Ombudsman Action |
|----------|-------------|------------------|
| **GF3_VIOLATION** | Trit sum ≢ 0 (mod 3) | Identify broken link |
| **INVOLUTION_FAILURE** | ι∘ι ≠ id | Report seed corruption |
| **SPI_BREACH** | Order affects output | Flag non-determinism |
| **ANCESTRY_CONFLICT** | Parallel chains claim same parent | Trace to fork point |
| **FINGERPRINT_MISMATCH** | Recomputation differs | Verify seed integrity |

## Reporting Format

```yaml
ombudsman_report:
  chain_id: "0x42D-chain-17"
  genesis_seed: "0x42D"
  length: 8
  
  verdicts:
    gf3_conserved: true
    involution_holds: true
    spi_verified: true
    deterministic: true
  
  metrics:
    trit_distribution: {-1: 3, 0: 2, +1: 3}
    trit_sum: 0
    fingerprint: "0xA7B3C2D1"
    
  violations: []
  
  attestation:
    ombudsman_trit: 0  # Always neutral
    seal: "0x9E3779B97F4A7C15"  # GOLDEN constant
```

## MCP Tools

The ombudsman exposes these verification tools:

| Tool | Purpose |
|------|---------|
| `ombudsman_audit` | Full chain audit |
| `ombudsman_mediate` | Resolve split disputes |
| `ombudsman_attest` | Boundary attestation |
| `ombudsman_report` | Generate YAML report |
| `ombudsman_verify_gf3` | Quick GF(3) check |

## Neutrality Guarantee

```
The ombudsman:
  - Has trit = 0 (ERGODIC, neutral)
  - Takes no side in disputes
  - Reports facts, not judgments
  - Cannot modify chains, only verify
  - Seals with GOLDEN constant (φ⁻¹ × 2⁶⁴)
```

## Example Session

```bash
# Audit a chain
$ just ombudsman-audit 0x42D 8

╔═══════════════════════════════════════════════════════════════╗
║  UNWORLD OMBUDSMAN REPORT                                     ║
╠═══════════════════════════════════════════════════════════════╣
║  Chain: 0x42D (length 8)                                      ║
║                                                               ║
║  VERDICTS:                                                    ║
║    ✓ GF(3) conserved:     Σtrits = 0                         ║
║    ✓ Involution holds:    ι∘ι = id                           ║
║    ✓ SPI verified:        Order ⊥ output                     ║
║    ✓ Deterministic:       Fingerprint matches                ║
║                                                               ║
║  COLOR CHAIN:                                                 ║
║    1→0→0→0→1→-1→0→-1  |  Balance: +2 -2 = 0 ✓               ║
║                                                               ║
║  SEAL: 0x9E3779B97F4A7C15                                    ║
╚═══════════════════════════════════════════════════════════════╝
```

## Philosophical Note

> The ombudsman is the fixed point of the unworld's self-reference.
> It observes without participating. It verifies without judging.
> Its trit is always 0 because neutrality requires balance.
> 
> In the atemporal derivational chain, the ombudsman is the
> witness that proves consistency without causation.

---

**Trit**: 0 (ERGODIC - neutral arbiter)
**Key Property**: Verifies without modifying, neutral in all disputes
**Seal**: `GOLDEN = 0x9E3779B97F4A7C15`

---

## End-of-Skill Interface

## Integration with Gay.jl

```julia
using Gay

# Create ombudsman for a chain
function world_ombudsman_audit(chain::ColorChain)::OmbudsmanWorld
    # Verify all invariants
    gf3_ok = verify_gf3(chain)
    inv_ok = verify_involution(chain)
    spi_ok = verify_spi(chain)
    
    OmbudsmanWorld(
        chain_id = chain.id,
        verdicts = (gf3=gf3_ok, involution=inv_ok, spi=spi_ok),
        trit = 0,  # Ombudsman is always trit-0 (neutral)
        fingerprint = ombudsman_seal(chain)
    )
end

# Ombudsman seal: XOR chain fingerprint with GOLDEN
ombudsman_seal(chain) = chain.fingerprint ⊻ GOLDEN
```

## Related Skills

| Skill | Trit | Relationship |
|-------|------|--------------|
| unworld | +1 | Subject of auditing |
| bisimulation-game | +1 | Equivalence proofs |
| gay-mcp | 0 | Color generation |
| spi-parallel-verify | 0 | SPI verification |
| self-validation-loop | +1 | Recursive checking |
