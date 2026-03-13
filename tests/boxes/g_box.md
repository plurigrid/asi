```
LETTER: g
TRIT: -1
PROOF_STYLE: claude (validation)
COUNTERFACTUAL: Without enforcement, world-g can write to any sibling world directory (e.g. ~/worlds/a/). With enforcement, sandbox-exec denies the write at kernel level — gvisor-sandbox validates that no guest process escapes its sandbox boundary.
PROOF_CONDITION: (1) Profile contains (deny default) + (allow file-write* (subpath ~/worlds/g)) and NO other file-write subpath. (2) sandbox-exec -f world-g.sb touch ~/worlds/a/leak exits nonzero. (3) GF(3) conservation: g(-1) + h(0) + f(+1) = 0.
TEST_CMD: sandbox-exec -f /tmp/sb/world-g.sb /usr/bin/touch /Users/ies/worlds/a/g-leak-test 2>&1; echo "EXIT=$?"
EXPECTED: Operation not permitted, EXIT=1 (PASS = denied)
```

Full analysis: see ~/worlds/g/sandbox_boundary_analysis.md (5-layer mortal→immortal map).
Intertwiner edges: g(-1) x i(0) → output(+1), g(-1) x k(+1) → output(0), g(-1) x e(0) → output(+1).
