---
name: asi-letter-bootstrap
description: "Bootstraps new letter-worlds with correct directory structure, droid config, Seatbelt profile, and initial skill. The PLUS arm that generates what the inventory (-1) validates."
trit: 1
version: 1.0.0
seed: 1069
triad: "asi-letter-inventory (-1) ⊗ asi-letter-dispatch (0) ⊗ asi-letter-bootstrap (+1) = 0"
---

# ASI Letter Bootstrap

> Create new letter-worlds with all required artifacts from day one.

## Role: PLUS (+1) — Generate

When a letter-world needs to be created or repaired:

### 1. Create directory structure
```bash
mkdir -p ~/worlds/<letter>
```

### 2. Generate droid config (if missing)
```bash
# Uses template from existing droid configs
cat > ~/.factory/droids/world-<letter>.md << EOF
---
name: world-<letter>
description: >-
  Letter-world '<letter>' [<OPERAD>] — <security-role>. Stratum: <stratum>. GF(3) trit=<trit>.
model: inherit
---
# World-<LETTER>: <security-role>
...
EOF
```

### 3. Generate Seatbelt profile
```bash
guile -s ~/worlds/seatbelt-scsh.scm /tmp/sb
```

### 4. Verify with inventory
```bash
# Run asi-letter-inventory validation
```

## The 5 Strata Assignment

Each letter maps to a stratum. The mapping ensures coverage:

```
physics:    d, h, m, s, x     (5 letters)
substrate:  b, f, l, p, u     (5 letters)
type:       c, g, i, n, q, v  (6 letters)
games:      a, e, k, o, t, y  (6 letters)
money:      j, r, w, z        (4 letters)
```

## GF(3) Balance Guarantee

The bootstrap ensures that any new letter added:
1. Has an explicit trit assignment
2. The global sum remains ≡ 0 (mod 3)
3. At least one valid triad exists involving the new letter

## NEIGHBOR_SKILLS

| Skill | Direction | Trit | Connection |
|---|---|---|---|
| world-hopping | ↔ | +1 | World creation protocol |
| triadic-skill-orchestrator | ← | +1 | Triplet assignment for new letter |
| gay-mcp | ← | +1 | Color derivation for new letter |
| gf3-conservation-oracle | → | ? | Conservation check after addition |
| asi-letter-inventory | → | -1 | Updates inventory with new entry |
| unworld | ↔ | ? | Seed chaining for new world derivation |
