```
LETTER: r
TRIT: +1
PROOF_STYLE: codex (generation)
COUNTERFACTUAL: world-r MUST NOT execute aptos_transfer or aptos_approve without GF(3) conservation check (Σ trits ≡ 0 mod 3); denied = unaudited financial mutation
PROOF_CONDITION: generator produces a transparency-logged operation; rekor-transparency lens requires every MCP call to aptos_transfer/aptos_swap/aptos_stake to emit a verifiable log entry before execution
TEST_CMD: echo '{"letter":"r","trit":1,"op":"aptos_transfer","partner_trit":-1,"output_trit":0}' | python3 -c "import json,sys; d=json.load(sys.stdin); s=d['trit']+d['partner_trit']+d['output_trit']; print('PASS' if s%3==0 else 'FAIL'); assert s%3==0, f'GF3 violation: {s}'"
EXPECTED: PASS
```

[R|PLUS|money]
