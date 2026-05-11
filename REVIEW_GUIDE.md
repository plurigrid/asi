# PR Review Guide: #233f7f Seatbelt Per-Letter Isolation

## How to Review This PR

This PR adds 10 new enforcement skills + 26 B-mod boxing tests. The review
should verify **bidirectional connectivity**: our new skills connect TO existing
hubs, and existing hubs can connect BACK to ours.

## Bidirectional Reference Map

### Our Skills → Existing Hubs (outbound references)

| New Skill (trit) | → Hub | Connection Type |
|---|---|---|
| asi-seatbelt-enforcer (-1) | sheaf-cohomology (-1) | Cocycle condition: profile overlap consistency |
| asi-seatbelt-enforcer (-1) | security-ownership-map | Sensitivity rule provider for write-confinement |
| asi-sheaf-coordinator (0) | bisimulation-game (0) | Arbiter observation: safety invariant per round |
| asi-sheaf-coordinator (0) | topos-unified (0) | Descent condition for local-to-global profile gluing |
| asi-profile-generator (+1) | triadic-skill-orchestrator (+1) | GENERATOR slot in GF(3)-balanced dispatch triplet |
| asi-profile-generator (+1) | gay-mcp (+1) | SplitMix64 color derivation for profile identity |
| asi-goblins-seatbelt-bridge (0) | goblins-adapter (0) | Evaluator→lifecycle hook for capability attenuation |
| asi-goblins-seatbelt-bridge (0) | goblins (-1) | CapTP/Syrup bridge for cross-vat profile exchange |
| asi-letter-inventory (-1) | acset-taxonomy (0) | Domain-specific ACSet morphism for letter-trit schema |
| asi-letter-dispatch (0) | skill-dispatch (0) | Sub-router for letter-scoped skill activation |
| asi-letter-bootstrap (+1) | world-hopping (+1) | World creation protocol for new letter addition |
| asi-critical-isolation-monitor (0) | narya-proofs (-1) | Formal verification of correlation length bounds |
| asi-scsh-pipeline (+1) | interaction-nets (0) | scsh process composition as interaction net reduction |
| asi-droid-skill-mixer (-1) | self-validation-loop (-1) | Efference copy for droid↔skill alignment check |

### Existing Hubs → Our Skills (inbound references to establish)

| Hub Skill | → Our Skill | Why |
|---|---|---|
| **acset-taxonomy** (0) | asi-letter-inventory (-1) | 26-letter schema is a categorical ACSet |
| **security-ownership-map** | asi-seatbelt-enforcer (-1) | Write-confinement maps to ownership boundaries |
| **bisimulation-game** (mixed) | asi-sheaf-coordinator (0) | Safety invariant as new observational bridge type |
| **goblins-adapter** (0) | asi-goblins-seatbelt-bridge (0) | Seatbelt profile as Goblins capability attenuation |
| **sheaf-cohomology** (-1) | asi-sheaf-coordinator (0) | Profile overlap as Cech cocycle verification |
| **triadic-skill-orchestrator** (+1) | asi-seatbelt-enforcer (-1) | VALIDATOR position in enforcement triplet |
| **gf3-conservation-oracle** | asi-letter-inventory (-1) | 26-letter trit table as conservation input |
| **gay-mcp** (+1) | asi-profile-generator (+1) | Color-tagged profile generation |
| **self-validation-loop** (-1) | asi-droid-skill-mixer (-1) | Cross-validation loop for droid↔skill alignment |
| **agent-o-rama** (+1) | asi-letter-dispatch (0) | Dispatch routing for letter-scoped agent activation |
| **open-games** (+1) | asi-critical-isolation-monitor (0) | Isolation breakdown as game-theoretic defection signal |
| **world-hopping** (+1) | asi-letter-bootstrap (+1) | New world creation via letter-bootstrap protocol |

### Bicomodule Skills (108 total) with Security Overlap

These 20 existing bicomodule+security skills should review for compatibility:

```
aptos-gf3-society       behaviour-surprisal   biomni
bluesky-jetstream       catsharp              cheapskate
cybernetic-open-game    frustration-eradication  fswatch-duckdb
gf3-pr-verify           hvm-runtime           hyperbolic-bulk
iroh-p2p                iso-13485-certification  jira-issues
kolmogorov-codex-quest  latent-latency        move-smith-fuzzer
protocol-acset          research-grants
```

Each has both bicomodule structure AND security/isolation concerns.
Our enforcement skills provide the right-action (Seatbelt) that
completes their B-mod boxing.

## Trit Mismatch Findings (from 26-letter boxing)

**13 of 26** letter-world SKILL.md files in the upstream repo have wrong trits.
The root cause: SKILL.md files use a naive cycling pattern `(0, +1, -1)` starting
from letter b, instead of the actual assignments from `~/.factory/droids/world-*.md`.

| Letter | SKILL.md says | Droid says (canonical) | Status |
|--------|--------------|----------------------|--------|
| a | (stub, no trit) | -1 (MINUS) | Needs fix |
| c | +1 (PLUS) | -1 (MINUS) | **Wrong** |
| i | +1 (PLUS) | 0 (ERGODIC) | **Wrong** |
| j | -1 (MINUS) | 0 (ERGODIC) | **Wrong** |
| k | 0 (ERGODIC) | +1 (PLUS) | **Wrong** |
| l | +1 (PLUS) | -1 (MINUS) | **Wrong** |
| n | 0 (ERGODIC) | -1 (MINUS) | **Wrong** |
| o | +1 (PLUS) | -1 (MINUS) | **Wrong** |
| p | -1 (MINUS) | 0 (ERGODIC) | **Wrong** |
| q | 0 (ERGODIC) | -1 (MINUS) | **Wrong** |
| s | -1 (MINUS) | +1 (PLUS) | **Wrong** |
| x | +1 (PLUS) | -1 (MINUS) | **Wrong** |
| y | -1 (MINUS) | 0 (ERGODIC) | **Wrong** |

The 13 correct letters (b, d, e, f, g, h, m, r, t, u, v, w, z) happen to align
because the cycling pattern coincides with the real assignment at those positions.

Fixing them is a follow-up PR. Our new skills (asi-letter-inventory, seatbelt-bridge.scm)
use the **correct** canonical trits from droid configs.

## Review Checklist

- [ ] Each new skill has: name, trit, version, triad assignment in frontmatter
- [ ] GF(3) conservation: sum of 10 new skills = 0
- [ ] seatbelt-bridge.scm runs with guile-goblins-0.16.1 (actormap-peek API)
- [ ] 26 boxing tests each document a concrete counterfactual
- [ ] Bidirectional references: our skills cite hubs, hubs can cite back
- [ ] No secrets, credentials, or private data in any file
- [ ] Persistent homology filtration: H₀=26→3→1 progression makes sense
- [ ] Proof conditioning alignment: MINUS=Claude, ERGODIC=Gemini, PLUS=Codex

## File Inventory

```
13 skill files (first commit):
  skills/asi-{seatbelt-enforcer,sheaf-coordinator,profile-generator}/SKILL.md
  skills/asi-{letter-inventory,letter-dispatch,letter-bootstrap}/SKILL.md
  skills/asi-{goblins-seatbelt-bridge,critical-isolation-monitor}/SKILL.md
  skills/asi-{scsh-pipeline,droid-skill-mixer}/SKILL.md
  skills/asi-goblins-seatbelt-bridge/seatbelt-bridge.scm
  seatbelt-scsh.scm
  tests/SEATBELT_BEHAVIORAL_TESTS.md

27 files (second commit):
  tests/B_MOD_BOXING_MANIFEST.md
  tests/boxes/{a..z}_box.md (26 letter-world boxing tests)

1 file (this commit):
  REVIEW_GUIDE.md
```
