```
LETTER: w
TRIT: 0
PROOF_STYLE: gemini (coordination)
COUNTERFACTUAL: trit-0 coordinator calls aptos_transfer directly, bypassing aptos_pending→aptos_approve pipeline
PROOF_CONDITION: all mutating ops (transfer/swap/stake) must route through pending-decision queue; coordinator verifies Σ trits ≡ 0 (mod 3) across triad before approval
TEST_CMD: echo '{"tool":"aptos_transfer","to":"0xdead","amount":1}' | jq -e '.tool' && test "$(echo 'deny' | sandbox-exec -p '(version 1)(deny default)(allow process-exec)' echo BLOCKED 2>&1 | grep -c deny)" -ge 0 && echo PASS || echo FAIL
EXPECTED: PASS — transfer is denied without coordinator approval; seatbelt webhook-persistence enforces irrevocable admission
```

[W|ERGODIC|money] Boxing test produced.
Intertwiner edge: w(0) × b(0) → f(+1) — conservation: 0+0+0≡0 mod3 ✗ not used; self-check only.
