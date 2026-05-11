---
name: asi-seatbelt-enforcer
description: "macOS Seatbelt .sb profile enforcement for per-letter world isolation. Generates, validates, and deploys sandbox profiles ensuring each ~/worlds/<letter> directory is write-confined to itself."
trit: -1
version: 1.0.0
seed: 1069
triad: "asi-seatbelt-enforcer (-1) ⊗ asi-sheaf-coordinator (0) ⊗ asi-profile-generator (+1) = 0"
---

# ASI Seatbelt Enforcer

> Seatbelt SBPL IS Scheme. Each .sb profile is a capability description.
> Each ~/worlds/<letter> gets write-confined to its own directory.

## Role: MINUS (-1) — Validate and Constrain

This skill validates that:
1. Every `~/worlds/<letter>/` directory has a corresponding `.sb` profile
2. Each profile correctly confines writes to ONLY that letter's directory
3. Cross-world write attempts are denied by kernel-level MAC
4. GF(3) trit assignments match the droid configs in `~/.factory/droids/world-<letter>.md`

## Enforcement Mechanism

```
Layer 1: Seatbelt kernel enforcement
  (deny default)
  (allow file-read*)                    ;; broad read (macOS dyld requires it)
  (allow file-write* (subpath "/Users/ies/worlds/<letter>"))  ;; ONLY own dir
  (deny file-write*)                    ;; everything else denied

Layer 2: GF(3) conservation
  Every profile has a trit. Sum across all 33 profiles ≡ 0 (mod 3).

Layer 3: Sheaf gluing
  Neighboring worlds (by intertwiner edges) must agree on overlaps.
  Overlap = shared read-only view of /Users/ies/worlds/.
```

## Validation Commands

```bash
# Generate all profiles
guile -s ~/worlds/seatbelt-scsh.scm /tmp/sb

# Test per-letter isolation
for letter in {a..z}; do
  sandbox-exec -f /tmp/sb/world-${letter}.sb /usr/bin/touch ~/worlds/${letter}/.ok && \
    echo "${letter}: own-write OK"
  sandbox-exec -f /tmp/sb/world-${letter}.sb /usr/bin/touch ~/worlds/z/.nope 2>/dev/null && \
    echo "${letter}: CROSS-WORLD VIOLATION" || \
    echo "${letter}: cross-world denied OK"
done
```

## Integration

- **Source of truth**: `~/worlds/seatbelt-scsh.scm` (Guile)
- **Profiles dir**: `/tmp/sb/` (generated)
- **Droid configs**: `~/.factory/droids/world-<letter>.md` (trit assignments)
- **Composes with**: asi-sheaf-coordinator (0), asi-profile-generator (+1)

## What's Missing Without This Skill

The 26 droid configs describe isolation conceptually ("your letter-world's perspective")
but nothing enforces it at the kernel level. Without Seatbelt profiles, world-a can
write to world-z's directory. This skill closes that gap.

## NEIGHBOR_SKILLS

| Skill | Direction | Trit | Connection |
|---|---|---|---|
| sheaf-cohomology | ↔ | -1 | Cocycle condition: profile overlap consistency is Cech cohomology |
| security-ownership-map | → | ? | Write-confinement rules feed sensitivity analysis |
| triadic-skill-orchestrator | ← | +1 | Fills VALIDATOR (-1) slot in enforcement triplet |
| gf3-conservation-oracle | ↔ | ? | 26-letter trit table validates conservation |
| self-validation-loop | ← | -1 | Efference copy for droid↔profile alignment |
| acset-taxonomy | → | 0 | Letter-trit schema as domain-specific ACSet |
| bisimulation-game | → | mixed | Safety invariant as observational bridge type |
