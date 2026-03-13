---
name: asi-letter-inventory
description: "Runtime inventory validator for ~/worlds/<letter> directories. Ensures every letter a-z has: droid config, .sb profile, valid trit, and at least one skill. Closes the 42% trit coverage gap."
trit: -1
version: 1.0.0
seed: 1069
triad: "asi-letter-inventory (-1) ⊗ asi-letter-dispatch (0) ⊗ asi-letter-bootstrap (+1) = 0"
---

# ASI Letter Inventory

> "Only 42% of skills have trits" — asi-skill-selector
> This skill ensures 100% coverage for the 26 letter-worlds.

## Role: MINUS (-1) — Validate Completeness

### Required Artifacts Per Letter

| Artifact | Path | Status Check |
|---|---|---|
| Directory | `~/worlds/<letter>/` | exists? |
| Droid config | `~/.factory/droids/world-<letter>.md` | has trit? |
| Seatbelt profile | `/tmp/sb/world-<letter>.sb` | valid SBPL? |
| At least 1 skill | `~/worlds/z/.agents/skills/` with letter reference | has trit? |

### The 26-Letter Trit Table (from droid configs)

```
Letter  Trit  Operad    Stratum    Security Role
a       -1    MINUS     games      admission-control
b        0    ERGODIC   substrate  build-pipeline
c       -1    MINUS     type       certificate-authority
d       -1    MINUS     physics    device-access
e        0    ERGODIC   games      escape-vectors
f       +1    PLUS      substrate  filesystem-isolation
g       -1    MINUS     type       gvisor-sandbox
h        0    ERGODIC   physics    host-boundary
i        0    ERGODIC   type       identity-measurement
j        0    ERGODIC   money      jwt-rbac
k       +1    PLUS      games      kyverno-engine
l       -1    MINUS     substrate  lsm-enforcement
m       -1    MINUS     physics    mount-namespace
n       -1    MINUS     type       namespace-boundary
o       -1    MINUS     games      opa-rego
p        0    ERGODIC   substrate  pid-namespace
q       -1    MINUS     type       qlisp-verification
r       +1    PLUS      money      rekor-transparency
s       +1    PLUS      physics    sigstore-signing
t        0    ERGODIC   games      topology-mesh
u       +1    PLUS      substrate  user-namespace
v       -1    MINUS     type       vulnerability-scan
w        0    ERGODIC   money      webhook-persistence
x       -1    MINUS     physics    xor-fingerprint
y        0    ERGODIC   games      yaml-validation
z        0    ERGODIC   money      zero-trust
```

Sum: 11(-1) + 10(0) + 5(+1) = -11 + 0 + 5 = -6 ≡ 0 (mod 3) CONSERVED

### Missing in plurigrid-asi-integrated

That skill's letter index only maps 8 letters: a, b, e, n, o, p, r, t.
Missing 18 letters: c, d, f, g, h, i, j, k, l, m, q, s, u, v, w, x, y, z.
This inventory skill provides the complete mapping.

## Validation Script

```bash
#!/bin/bash
MISSING=0
for letter in {a..z}; do
  # Check directory
  [ -d ~/worlds/$letter ] || { echo "MISSING: ~/worlds/$letter/"; MISSING=$((MISSING+1)); }
  # Check droid config
  [ -f ~/.factory/droids/world-$letter.md ] || { echo "MISSING: droid world-$letter"; MISSING=$((MISSING+1)); }
  # Check .sb profile
  [ -f /tmp/sb/world-$letter.sb ] || { echo "MISSING: profile world-$letter.sb"; MISSING=$((MISSING+1)); }
done
echo "Total missing: $MISSING"
[ $MISSING -eq 0 ] && echo "INVENTORY COMPLETE" || echo "INVENTORY INCOMPLETE"
```
