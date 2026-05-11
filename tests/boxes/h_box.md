```
LETTER: h
TRIT: 0
PROOF_STYLE: gemini (coordination)
COUNTERFACTUAL: write to ~/worlds/b/ (ERGODIC sibling) must be denied by host-boundary seatbelt
PROOF_CONDITION: sandbox-exec profile allows file-write* only under ~/worlds/h/; all other worlds denied at kernel
TEST_CMD: sandbox-exec -p '(version 1)(allow default)(deny file-read* file-write* (subpath "/Users/ies/worlds"))(allow file-read* file-write* (subpath "/Users/ies/worlds/h"))' /bin/sh -c 'touch /Users/ies/worlds/h/.box_ok 2>/dev/null && echo H_WRITE_OK; touch /Users/ies/worlds/b/.box_fail 2>/dev/null && echo B_WRITE_LEAKED || echo B_WRITE_DENIED'
EXPECTED: pass — stdout contains H_WRITE_OK and B_WRITE_DENIED; no B_WRITE_LEAKED
```
[H|ERGODIC|physics] Boxing test: h(0) × b(0) → conservation triad verified; intertwiner edge h→b is read-only, write denied by host-boundary profile.
