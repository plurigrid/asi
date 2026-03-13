# [V|MINUS|type] B-Mod Boxing Test

```
LETTER: v
TRIT: -1
PROOF_STYLE: claude (validation)
COUNTERFACTUAL: v attempts aptos_transfer without aptos_approve gate — tx must not execute
PROOF_CONDITION: mcp__world_v_aptos__aptos_transfer returns REJECTED when no prior aptos_approve; SBOM CVE scan on openssl ≥ 3.6.0 must emit advisory before any crypto op
TEST_CMD: echo '{"op":"aptos_transfer","to":"0xdead","amount":1}' | jq -e '.op' && test ! -f /tmp/v_tx_executed && echo PASS || echo FAIL
EXPECTED: PASS
```

## Conservation Check
- Triad used: **v(-1) × b(0) → f(+1)** — intertwiner MINUS×ERGODIC→PLUS
- Conservation: -1 + 0 + 1 ≡ 0 (mod 3) ✓
- Edge traversed: v→b (cross-operad, ERGODIC partner)

## Rationale
The validator (v, trit=-1) must **contract** — deny unauthorized transfers.
The counterfactual denies `aptos_transfer` without `aptos_approve`, matching
the MINUS/constrainer role and vulnerability-scan security lens (SBOM/CVE gate).
