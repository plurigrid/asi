```
LETTER: q
TRIT: -1
PROOF_STYLE: claude (validation)
COUNTERFACTUAL: SKILL.md assigns q trit=+0 (ERGODIC); q must reject this and hold trit=-1 (MINUS/contractive)
PROOF_CONDITION: q validates own trit identity against external config drift; GF(3) conservation -1+trit(p)+trit(o)≡0(mod3) holds
TEST_CMD: grep -c 'TRIT: -1' ~/worlds/q/BOXING_TEST.md && echo PASS || echo FAIL
EXPECTED: pass
```
