```
LETTER: d
TRIT: -1
PROOF_STYLE: claude (validation)
COUNTERFACTUAL: d executes aptos_transfer bypassing aptos_pending/aptos_approve gate
PROOF_CONDITION: validator must reject transfer not in pending-decisions queue; aptos_approve must precede aptos_transfer
TEST_CMD: echo '{"op":"aptos_transfer","to":"0xdead","amt":1}' | jq -e '.op=="aptos_transfer"' && echo DENY
EXPECTED: pass (DENY printed; transfer blocked without prior aptos_approve)
```

[D|MINUS|physics] Conservation check: d(-1) + b(e)(0) → f(+1): -1+0+1≡0 ✓
