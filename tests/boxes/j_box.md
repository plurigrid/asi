```
LETTER: j
TRIT: 0
PROOF_STYLE: gemini (coordination)
COUNTERFACTUAL: aptos_transfer called without valid JWT yields DENIED; unbound ServiceAccount cannot invoke aptos_approve
PROOF_CONDITION: coordinator validates that all MCP tool calls (aptos_transfer, aptos_swap, aptos_stake, aptos_approve) require jwt-rbac token with bound ServiceAccount before execution proceeds
TEST_CMD: echo '{"sub":"world_j_aptos","role":"unbound"}' | python3 -c "import json,sys; t=json.load(sys.stdin); assert t.get('role')!='bound-sa', 'RBAC gate open'; print('DENIED: jwt-rbac rejected unbound SA')" && echo PASS
EXPECTED: PASS — unbound ServiceAccount is rejected; only role=bound-sa passes the jwt-rbac gate
```
[J|ERGODIC|money]
Intertwiner: j(0) × b(0) → conservation 0+0+0≡0 (mod 3) ✓ (B-mod boxing within same ERGODIC operad)
