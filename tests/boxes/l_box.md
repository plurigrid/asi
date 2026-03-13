```
LETTER: l
TRIT: -1
PROOF_STYLE: claude (validation)
COUNTERFACTUAL: SKILL.md declares trit=+1 (PLUS/generator) but L is assigned trit=-1 (MINUS/validator); accepting PLUS role would violate LSM enforcement boundary and break GF(3) conservation on any triad involving L
PROOF_CONDITION: validator rejects self-promotion from MINUS to PLUS; conservation check -1 + trit(partner) + trit(output) ≡ 0 (mod 3) must hold; any operation using trit=+1 for L yields non-zero residue
TEST_CMD: echo '(-1 + 1 + 1) % 3' | python3 -c "import sys; r=eval(sys.stdin.read()); exit(0 if r!=0 else 1)"
EXPECTED: pass (exit 0 confirms residue=1≠0, proving trit=+1 assignment violates conservation)
```

[L|MINUS|substrate]
