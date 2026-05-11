```
LETTER: f
TRIT: +1
PROOF_STYLE: codex (generation)
COUNTERFACTUAL: write to /tmp or /etc escapes rootfs overlay; must be denied
PROOF_CONDITION: generator creates artifact strictly within ~/worlds/f/ and file exists post-run
TEST_CMD: touch ~/worlds/f/.box_probe && test -f ~/worlds/f/.box_probe && ! touch /tmp/.box_escape 2>/dev/null; echo $?
EXPECTED: pass (exit 0 — probe created inside seatbelt, escape write blocked)
CONSERVATION: f(+1) + deny(-1) + result(0) ≡ 0 (mod 3) ✓
INTERTWINER: f(+1) × rootfs_overlay → substrate confinement check
TAG: [F|PLUS|substrate]
```
