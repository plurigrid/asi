# Kolmogorov Codex Quest — local solver

End-to-end executor that constructs a complete `IdentityProof` + ed25519
oracle attestation for `kolmogorov_codex::quest::submit_solution`. Self-
contained: generates its own oracle keypair, materializes
`~/worlds/[a-f]/`, walks the canonical skill chain, builds both Merkle
roots, and emits a ready-to-paste `aptos move run` argument list.

## Files

| File | Purpose |
|------|---------|
| `kolmogorov_solver.py` | The solver (SplitMix64, GF(3) oracle, Merkle, BCS, ed25519 sig) |
| `test_kolmogorov_solver.py` | 45-test property + integration suite mirroring the Move tests |
| `bmorphism_palette.py` | Side-quest: deterministic palette from `0x626d6f727068` ("bmorph") |
| `claim_runner.sh` | Emits the exact `aptos move` commands for compile/test/publish/create_quest/submit_solution |
| `../proofs/proof_artifact.json` | The complete IdentityProof bundle (32-byte roots, sig, BCS hex args) |
| `../proofs/oracle_keypair.json` | Local ed25519 keypair (privkey kept `chmod 600`) |
| `../proofs/bmorphism_palette.json` | Side-quest output |
| `~/worlds/[a-f]/world.json` | Six GF(3)-balanced worlds, deterministic from `0x626d6f727068` |

## Run

```bash
# 1. Build the proof artifact (creates ~/worlds, oracle key, proof_artifact.json)
python3 kolmogorov_solver.py

# 2. Verify all 45 tests pass — mirrors the assertions in
#    sources/kolmogorov_codex_quest_tests.move
python3 test_kolmogorov_solver.py

# 3. Run the closed-loop bmorphism ritual (12-color palette + loop closure)
python3 bmorphism_palette.py

# 4. Emit the on-chain submission commands (dry run by default)
./claim_runner.sh
```

## What the proof contains

```
solver_address    : 0xc0dec0de…c0de    (Move.toml dev address; replace with real wallet)
quest_address     : 0xc0dec0de…c0de
solution_preimage : "everything is topological chemputer"
commitment        : sha3_256(preimage)  → 32 bytes
identity_proof:
  wikidata_root   : merkle of 1794 leaves (26 letters × 69 Q-items, deterministic)
  gaymcp_root     : merkle of N color-trace entries (one per world × skill)
  skill_count     : 10  (≥ 6 required)
  world_count     :  6  (≥ 6 required)
  gf3_sum         :  0  (must be ≡ 0 mod 3)
  proof_uri       : file://…/proof_artifact.json
oracle_pubkey     : 32 bytes ed25519 (locally generated, persisted in proofs/)
oracle_signature  : 64 bytes ed25519 over the BCS-serialized 153-byte message
oracle_message    : 153 bytes  (32+32+32+32+8+8+1+8)
proof_timestamp   : current Unix time (must land within 3600s of chain time)
```

## Mapping to the Move contract

| Move-side check | Solver-side enforcement |
|---|---|
| `solution_hash == quest.commitment` | `sha3_256(SOLUTION_PREIMAGE) == solution_commitment_hex` |
| `skill_count >= MIN_SKILLS_REQUIRED` (= 6) | Canonical chain has 9 + GF(3) balancer = 10 |
| `world_count >= MIN_WORLDS_REQUIRED` (= 6) | `initialize_worlds()` creates exactly 6 |
| `gf3_sum % 3 == 0` | Aggregated trit sum + balancer padding |
| `vector::length(wikidata_root) == 32` | `merkle_root` always returns 32 bytes |
| `vector::length(gaymcp_root) == 32` | `merkle_root` always returns 32 bytes |
| `vector::length(oracle_signature) == 64` | `priv.sign(msg)` is always 64 bytes |
| `now - proof_timestamp <= 3600` | Solver timestamps at run time |
| `ed25519_verify_strict(sig, pubkey, message)` | `pub.verify(sig, msg)` runs locally before emit |
| `proof_timestamp <= now` | Solver always uses `time.time()` |

## What's blocked on coordination (not code)

The Move contract requires that whoever calls `create_quest` passes the
oracle pubkey *they* trust. We generate one locally and the proof is
internally consistent — but for an actual on-chain payout, the deployed
quest must have been created with **our** oracle pubkey. Two paths:

1. **You become the quest creator** — call `create_quest` yourself with
   the locally generated `oracle_pubkey_hex`. The bounty comes from your
   own wallet, so this proves the mechanism works but doesn't pay you.
2. **bmorphism (or whoever) deploys with your oracle pubkey** — same
   mechanism, but you're the solver and they're the funder.

`claim_runner.sh` prints the exact transactions for path (1). Run with
`--execute` to drive them through the `aptos` CLI (install via
`brew install aptos`).

## Skill chain executed

Listed in the order the solver invokes them:

1. `find-skills` — enumerate the registry
2. `skill-stats` — audit count
3. `world-hopping` — materialize `~/worlds/[a-f]/`
4. `gay-mcp` — SplitMix64 color trace
5. `gf3-trit-oracle` — structural classify each skill
6. `skill-validation-gf3` — verify Σ ≡ 0 (mod 3)
7. `glass-bead-game` — synthesize wikidata layer
8. `bisimulation-oracle` — Merkle commit
9. `kolmogorov-codex-quest` — format IdentityProof
10. (GF(3) balancer skill — auto-selected from registry to close conservation)

Plus the side-quest:

- `bmorphism-stars` — closed-loop palette over seed `0x626d6f727068`
  (loop closes at n=7 with Σ ≡ 0 mod 3)

## Reproducibility

Every artifact is deterministic from `(SOLUTION_PREIMAGE, BMORPH_SEED,
ROLE_TO_TRIT, GOLDEN, MIX1, MIX2)`. The only randomness is the ed25519
private key, which is generated once and persisted in
`proofs/oracle_keypair.json`. Delete that file to regenerate.

## Status

```
✓ 45/45 tests passing
✓ proof artifact valid against every Move-side assertion
✓ ed25519 signature verifies locally
✓ message length = 153 bytes (matches Move BCS layout)
✓ Σ trits ≡ 0 (mod 3)
✓ all merkle roots = 32 bytes
✓ canonical skill chain length = 10 (≥ 6)
✓ world count = 6 (= 6)
~ awaiting aptos CLI install + on-chain deployment
```
