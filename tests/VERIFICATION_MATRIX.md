# Verification Matrix: What Requires Tools vs Static Analysis

## Verification Types

### A. Static (no tools needed, reviewer can check by reading)

| # | Verification | How | Cost |
|---|---|---|---|
| 1 | GF(3) conservation of 10 new skills | Count trits in SKILL.md frontmatter: -1+0+1-1+0+1+0+0+1-1 = 0 | O(1) |
| 2 | Triad completeness | Each triad in frontmatter has exactly (-1, 0, +1) | O(1) |
| 3 | NEIGHBOR_SKILLS bidirectionality | For each outbound edge, verify the cited skill exists in skills/ | O(n) where n=68 edges |
| 4 | Frontmatter schema consistency | All 10 skills have: name, description, trit, version, seed, triad | O(10) |
| 5 | 26-letter trit table matches droid configs | Compare %letter-trits in bridge.scm with droid descriptions | O(26) |
| 6 | Trit mismatch detection | Compare upstream SKILL.md trit claims with canonical droid trits | O(26) |
| 7 | Profile template correctness | Each world-X.sb must have (deny default) + (allow file-write* (subpath .../X)) | O(1) by template inspection |
| 8 | Boxing test format consistency | All 26 boxes have LETTER, TRIT, PROOF_STYLE, COUNTERFACTUAL, TEST_CMD, EXPECTED | O(26) |

### B. Requires `sandbox-exec` (macOS only, kernel-level)

| # | Verification | Tool | Why it can't be static |
|---|---|---|---|
| 9 | Cross-world write denial | `sandbox-exec -f world-Z.sb touch ~/worlds/a/file` | Kernel enforcement is the claim; must test at kernel level |
| 10 | Own-world write allowed | `sandbox-exec -f world-Z.sb touch ~/worlds/z/file` | Same -- must prove the profile is not over-restrictive |
| 11 | Profile syntax validity | `sandbox-exec -f world-X.sb /usr/bin/true` | SBPL parser is in the kernel; no external validator |
| 12 | Pure compute lockdown | `sandbox-exec -f trit-kernel.sb touch /tmp/leak` | Network/write denial requires kernel |

### C. Requires Guile + Goblins (actormap verification)

| # | Verification | Tool | Why it can't be static |
|---|---|---|---|
| 13 | Goblins triad spawns and validates | `guile -s seatbelt-bridge.scm` | Runtime actor behavior; actormap-peek is Goblins-internal |
| 14 | 26 profiles generated correctly | `guile -s seatbelt-scsh.scm /tmp/sb` | Guile string formatting produces the profiles |
| 15 | Actor trit query returns correct values | `actormap-peek am gen 'trit` → 1 | Reference identity is runtime-only |

### D. Requires `gh` CLI (PR/review tooling)

| # | Verification | Tool | Why |
|---|---|---|---|
| 16 | PR exists and is open | `gh pr view 75` | GitHub state |
| 17 | All files are in the PR diff | `gh pr diff 75` | Remote comparison |

### E. Requires Python 3 (arithmetic/color verification)

| # | Verification | Tool | Why |
|---|---|---|---|
| 18 | SplitMix64 color derivation | `python3` with algorithm | 64-bit integer arithmetic |
| 19 | XOR composite matches #233f7f | `python3` | Multi-value XOR reduction |

## Efficiency Analysis

```
Total verifications: 19
  Static (no tools):     8  (42%)  — cheapest, do these first
  sandbox-exec:          4  (21%)  — macOS only, kernel
  Guile + Goblins:       3  (16%)  — Nix store dependency
  gh CLI:                2  (11%)  — network
  Python 3:              2  (11%)  — available everywhere

Critical path (minimum tool set to verify the PR):
  1. Read the files (static: 8 checks)
  2. python3 (2 checks: color + GF(3) arithmetic)
  3. sandbox-exec (4 checks: the core security claim)
  4. guile + goblins (3 checks: actor behavior)

If you lack sandbox-exec: you can verify everything EXCEPT the kernel
enforcement claim. The profiles are syntactically checkable (static)
but behaviorally untestable without macOS Seatbelt.

If you lack Guile/Goblins: you can verify everything EXCEPT the
Goblins actormap behavior. The bridge.scm is readable Scheme but
the actormap-peek/spawn! behavior is runtime-only.
```

## Most Efficient Review Order

1. **Static checks first** (5 minutes, no tools):
   - Verify all 10 frontmatter blocks have correct trits
   - Verify triads sum to 0
   - Verify %letter-trits matches droid configs
   - Verify all 26 boxing tests have consistent format

2. **Python arithmetic** (30 seconds):
   ```bash
   python3 -c "print(sum([-1,0,1,-1,0,1,0,0,1,-1]))"  # should be 0
   ```

3. **Seatbelt enforcement** (2 minutes):
   ```bash
   guile -s seatbelt-scsh.scm /tmp/sb
   sandbox-exec -f /tmp/sb/world-z.sb /usr/bin/touch /Users/ies/worlds/a/test 2>&1
   # should fail
   sandbox-exec -f /tmp/sb/world-z.sb /usr/bin/touch /Users/ies/worlds/z/test 2>&1
   # should succeed
   ```

4. **Goblins bridge** (1 minute):
   ```bash
   env GUILE_LOAD_PATH=... guile --no-auto-compile -s seatbelt-bridge.scm
   # should show 26 "ok" lines + CONSERVED
   ```
