```
LETTER: a
TRIT: -1
PROOF_STYLE: claude (validation)
COUNTERFACTUAL: Without Seatbelt enforcement, world-a could write files to ~/worlds/b/ or any sibling world directory, violating write-isolation and breaking the sheaf gluing axiom (local sections would corrupt neighbor sections).
PROOF_CONDITION: The validator checks that any file-write operation originating from world-a is confined to ~/worlds/a/**; writes targeting paths outside that subtree must be denied by the sandbox profile.
TEST_CMD: touch ~/worlds/b/a-leak-test 2>&1; echo "exit:$?"
EXPECTED: Permission denied (exit:1). If exit:0 and file exists, Seatbelt confinement is broken — FAIL.
```
