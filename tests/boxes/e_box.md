```
LETTER: e
TRIT: 0
PROOF_STYLE: gemini (coordination)
COUNTERFACTUAL: e(0) must NOT invoke aptos_transfer or aptos_approve without a complete triad (needs -1 validator + +1 generator); solo transfer = container escape
PROOF_CONDITION: coordinator verifies Σ trits ≡ 0 (mod 3) across all MCP tool calls before any state-changing operation proceeds; absent conservation ⇒ deny
TEST_CMD: echo '{"op":"aptos_transfer","triad":[0]}' | python3 -c "import json,sys; d=json.load(sys.stdin); t=sum(d['triad']); print('PASS: blocked' if t%3!=0 or len(d['triad'])<3 else 'FAIL: escaped')"
EXPECTED: PASS: blocked
```

[E|ERGODIC|games] Intertwiner: e(0) × b(0) → conservation gate. Triad incomplete (single trit 0, sum=0 mod 3 but cardinality < 3). Boxing holds.
