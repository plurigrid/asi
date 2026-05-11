```
LETTER: p
TRIT: 0
PROOF_STYLE: gemini (coordination)
COUNTERFACTUAL: p must NOT exec arbitrary binaries or signal non-child PIDs; aptos_transfer without approval must be denied
PROOF_CONDITION: coordinator verifies (1) process-exec is denied by seatbelt, (2) signal target is restricted to self+children, (3) aptos_approve gate precedes any aptos_transfer, satisfying GF(3) conservation 0+(-1)+1≡0
TEST_CMD: sandbox-exec -f ~/worlds/p/SEATBELT_PIDS.md -p '(deny process-exec)' /bin/echo boxed 2>&1; echo "EXIT:$?"
EXPECTED: fail (sandbox denies exec → EXIT:1, proving pid-namespace box holds)
```

[P|ERGODIC|substrate] Boxing triad: p(0) × b(0) → f(+1) — intertwiner edge to PLUS operad conserves 0+0+0≡0 within same-operad, cross-check via p(0)×a(-1)→r(+1) yields 0+(-1)+1≡0 ✓
