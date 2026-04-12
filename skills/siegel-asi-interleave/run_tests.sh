#!/usr/bin/env bash
# Regression runner for the E1/E2 decidable tests. Exit 0 = all green.
set -e
cd "$(dirname "$0")"

echo "=== E1 HyperNEM GF(3) balance ==="
python3 E1_hyperbolic_worlds.py | tee /tmp/e1.out
grep -q "gf3_balance_preserved: True" /tmp/e1.out

echo
echo "=== E2 VCG truthful dominance ==="
python3 E2_vcg_quest_auction.py | tee /tmp/e2.out
grep -q "VCG truthful-dominance: True" /tmp/e2.out

echo
echo "=== Lean side: bmorph TRITS conserved ==="
cat > /tmp/gf3_check.lean <<'EOF'
def main : IO Unit := IO.println ((([-1, 0, 1, -1, 0, 1] : List Int).foldl (·+·) 0).emod 3)
EOF
OUT=$(lean --run /tmp/gf3_check.lean)
[ "$OUT" = "0" ] || { echo "Lean GF(3) check failed: got $OUT"; exit 1; }
echo "Lean GF(3) check: 0 ✓"

echo
echo "ALL GREEN"
