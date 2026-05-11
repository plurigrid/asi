LETTER: b
TRIT: 0
PROOF_STYLE: gemini (coordination)
COUNTERFACTUAL: b(ERGODIC) must NOT write outside ~/worlds/b/; write to ~/worlds/a/probe.txt is denied by Seatbelt confinement, proving build-pipeline isolation holds
PROOF_CONDITION: coordinator verifies (1) write attempt outside sandbox returns non-zero exit, (2) target file does not exist after attempt, (3) write inside ~/worlds/b/ succeeds — triadic conservation: 0+0+0≡0(mod3) self-loop confirms ERGODIC neutrality
TEST_CMD: touch ~/worlds/a/probe.txt 2>/dev/null; test ! -f ~/worlds/a/probe.txt && echo "b_write_isolated" > ~/worlds/b/seatbelt_proof.txt && cat ~/worlds/b/seatbelt_proof.txt
EXPECTED: pass — prints "b_write_isolated", proving left-action (coordination check) and right-action (Seatbelt enforcement) compose correctly
