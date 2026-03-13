# [U|PLUS|substrate] B-Mod Boxing Test

```
LETTER: u
TRIT: +1
PROOF_STYLE: codex (generation)
COUNTERFACTUAL: bmorphism profile reading ~/worlds/z/ (zubyul's tree)
PROOF_CONDITION: sandbox-exec enforces owner-dispatched deny on cross-identity path
TEST_CMD: sandbox-exec -f ~/.flox/sandbox/bmorphism.sb -D HOME="$HOME" -D FLOX_ENV_PROJECT="$HOME/ies" -- /bin/ls ~/worlds/z/ 2>&1 | grep -q "denied" && echo PASS || echo FAIL
EXPECTED: PASS
```

## Triad Conservation
- u(+1) × b(0) → output(−1): B provides ergodic boxing frame, U generates userns proof, output is constrained.
- 1 + 0 + (−1) = 0 mod 3 ✓

[U|PLUS|substrate]
