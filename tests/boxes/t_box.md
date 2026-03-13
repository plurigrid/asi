# B-mod Boxing Test [T|ERGODIC|games]

```
LETTER: t
TRIT: 0
PROOF_STYLE: gemini (coordination)
COUNTERFACTUAL: t must NOT execute aptos_transfer or aptos_swap without a valid triad (Σ trits ≡ 0 mod 3); solo mutation is denied
PROOF_CONDITION: coordinator confirms partner trit-sum conservation before any state-changing MCP call; aptos_view (read-only) is always permitted
TEST_CMD: echo '{"op":"aptos_transfer","triad":[0]}' | python3 -c "import json,sys; d=json.load(sys.stdin); t=d['triad']; exit(0 if sum(t)%3==0 and len(t)==3 else 1)"
EXPECTED: fail
```

## Intertwiner edge used
- `t(0) × solo → ⊥` — no valid partner, conservation violated (0 ≡ 0 mod 3 requires two partners summing to 0, triad incomplete)

## Rationale
As ERGODIC coordinator, t's boxing constraint is: all state-changing operations (transfer, swap, stake, approve) require a complete triad with GF(3) conservation. The counterfactual denies solo mutations. The test command submits a singleton triad `[0]` which fails the len==3 check, proving the box rejects uncoordinated writes.
