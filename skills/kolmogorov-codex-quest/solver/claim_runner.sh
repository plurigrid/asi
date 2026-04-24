#!/usr/bin/env bash
#
# claim_runner.sh
# ===============
#
# One-shot deployment + claim runner for the Kolmogorov Codex Quest.
#
# Reads `proofs/proof_artifact.json` (produced by `kolmogorov_solver.py`) and
# emits the exact `aptos move` commands needed to:
#
#   1. Compile the contract
#   2. Run the local Move test suite
#   3. Publish the contract to a fresh devnet account
#   4. Call `create_quest` (creator-side) with the locally-generated oracle key
#   5. Call `submit_solution` (solver-side) with the proof artifact
#
# Designed to be safe-by-default: it does NOT execute any aptos commands
# itself. It prints them, ready to paste, so you can review every transaction
# before broadcasting.
#
# USAGE:
#   ./claim_runner.sh                    # print all commands
#   ./claim_runner.sh --execute          # also execute (requires aptos CLI + funded profile)

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ARTIFACT="${ROOT}/proofs/proof_artifact.json"
KEYFILE="${ROOT}/proofs/oracle_keypair.json"

if [[ ! -f "$ARTIFACT" ]]; then
  echo "missing $ARTIFACT — run python3 kolmogorov_solver.py first" >&2
  exit 1
fi

EXECUTE=0
if [[ "${1:-}" == "--execute" ]]; then
  EXECUTE=1
fi

require_jq() {
  if ! command -v jq >/dev/null 2>&1; then
    echo "jq is required" >&2
    exit 2
  fi
}
require_jq

# ── Read every field straight out of the artifact ─────────────────────────────
SOLVER_ADDRESS=$(jq -r '.solver_address' "$ARTIFACT")
QUEST_ADDRESS=$(jq -r '.quest_address' "$ARTIFACT")
COMMITMENT_HEX=$(jq -r '.solution_commitment_hex' "$ARTIFACT")
ORACLE_PUBKEY_HEX=$(jq -r '.oracle_pubkey_hex' "$ARTIFACT")
WIKIDATA_ROOT=$(jq -r '.identity_proof.wikidata_root' "$ARTIFACT")
GAYMCP_ROOT=$(jq -r '.identity_proof.gaymcp_root' "$ARTIFACT")
SKILL_COUNT=$(jq -r '.identity_proof.skill_count' "$ARTIFACT")
WORLD_COUNT=$(jq -r '.identity_proof.world_count' "$ARTIFACT")
GF3_SUM=$(jq -r '.identity_proof.gf3_sum' "$ARTIFACT")
PROOF_URI=$(jq -r '.identity_proof.proof_uri' "$ARTIFACT")
SOLUTION_HEX=$(jq -r '.solution_preimage_hex' "$ARTIFACT")
SIGNATURE_HEX=$(jq -r '.oracle_signature_hex' "$ARTIFACT")
PROOF_TIMESTAMP=$(jq -r '.proof_timestamp' "$ARTIFACT")

PROOF_URI_HEX=$(printf '%s' "$PROOF_URI" | xxd -p -c 4096 | tr -d '\n')
SOLUTION_HEX_NO0X="$SOLUTION_HEX"

bar() { printf '─%.0s' {1..72}; printf '\n'; }

bar
echo "Kolmogorov Codex Quest — claim runner"
bar

echo
echo "[1/5] Compile contract"
echo
cat <<EOF
cd ${ROOT}
aptos move compile \\
  --named-addresses kolmogorov_codex=default \\
  --skip-fetch-latest-git-deps
EOF

echo
echo "[2/5] Run local Move test suite (no chain interaction)"
echo
cat <<EOF
aptos move test \\
  --named-addresses kolmogorov_codex=default \\
  --skip-fetch-latest-git-deps
EOF

echo
echo "[3/5] Publish to devnet"
echo
cat <<EOF
aptos init --network devnet --profile kolmogorov_dev   # one-time
aptos account fund-with-faucet --profile kolmogorov_dev
aptos move publish \\
  --profile kolmogorov_dev \\
  --named-addresses kolmogorov_codex=kolmogorov_dev \\
  --skip-fetch-latest-git-deps \\
  --included-artifacts none
EOF

echo
echo "[4/5] Create the quest (creator side) — uses the oracle pubkey we generated"
echo
echo "  oracle pubkey: 0x${ORACLE_PUBKEY_HEX}"
echo "  commitment   : 0x${COMMITMENT_HEX}  (sha3_256 of solution preimage)"
echo "  bounty       : 200000000 octas (= 2 APT)"
echo
cat <<EOF
aptos move run \\
  --profile kolmogorov_dev \\
  --function-id default::quest::create_quest \\
  --args u64:200000000 hex:0x${COMMITMENT_HEX} hex:0x${ORACLE_PUBKEY_HEX}
EOF

echo
echo "[5/5] Submit the solution (solver side) — pastes the full IdentityProof + signed attestation"
echo
echo "  skill_count    : ${SKILL_COUNT}"
echo "  world_count    : ${WORLD_COUNT}"
echo "  gf3_sum        : ${GF3_SUM}  (must be 0)"
echo "  proof_timestamp: ${PROOF_TIMESTAMP}  (must be within 3600s of chain time)"
echo
cat <<EOF
aptos move run \\
  --profile kolmogorov_dev \\
  --function-id default::quest::submit_solution \\
  --args \\
    address:${QUEST_ADDRESS} \\
    hex:0x${SOLUTION_HEX_NO0X} \\
    hex:0x${WIKIDATA_ROOT} \\
    hex:0x${GAYMCP_ROOT} \\
    u64:${SKILL_COUNT} \\
    u64:${WORLD_COUNT} \\
    u8:${GF3_SUM} \\
    hex:0x${PROOF_URI_HEX} \\
    hex:0x${SIGNATURE_HEX} \\
    u64:${PROOF_TIMESTAMP}
EOF

echo
bar
if [[ $EXECUTE -eq 1 ]]; then
  if ! command -v aptos >/dev/null 2>&1; then
    echo "✗ aptos CLI not installed. Install with:" >&2
    echo "    brew install aptos" >&2
    exit 3
  fi
  echo "→ EXECUTE mode: running the commands above for real"
  bar
  cd "$ROOT"
  aptos move compile --named-addresses kolmogorov_codex=default --skip-fetch-latest-git-deps
  aptos move test    --named-addresses kolmogorov_codex=default --skip-fetch-latest-git-deps
  echo
  echo "▲ stop. publish + create_quest + submit_solution require interactive setup."
  echo "  Re-run the printed commands above one at a time once you have a profile."
else
  echo "→ DRY RUN. Re-invoke with --execute to run compile + test locally."
fi
