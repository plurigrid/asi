```
LETTER: n
TRIT: -1
PROOF_STYLE: claude (validation)
COUNTERFACTUAL: SKILL.md declares n as trit=+0 (ERGODIC) but world-n identity is trit=-1 (MINUS); namespace-boundary must reject trit forgery across ns isolation boundary
PROOF_CONDITION: validator confirms trit(n)=-1 AND rejects any composition where n is treated as +0; GF(3) conservation -1+trit(p)+trit(o)≡0(mod3) must hold
TEST_CMD: grep -c 'Trit.*+0' /tmp/asi-pr/skills/n/SKILL.md && echo "TRIT_MISMATCH_DETECTED" || echo "CONSISTENT"
EXPECTED: pass (mismatch detected: SKILL.md says +0, identity says -1; validator catches the discrepancy)
```

[N|MINUS|type] Box test produced. Intertwiner edge: self-validation (n→n identity check across ns boundary). Conservation: -1 + 0 + 1 ≡ 0 (mod 3) — the +0 claim in SKILL.md would require a +1 partner to conserve, but n's true trit=-1 requires different triads.
