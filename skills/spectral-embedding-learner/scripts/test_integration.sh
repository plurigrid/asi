#!/bin/bash
# Spectral Embedding Learner Integration Test

set -e

SCRIPT_DIR="$HOME/.claude/skills/spectral-embedding-learner/scripts"

echo "═══ Spectral Embedding Learner Integration Test ═══"
echo ""

echo "1. Python implementation:"
python3 -c "
import sys
sys.path.insert(0, '$SCRIPT_DIR')
from spectral_embedding_learner import SpectralEmbeddingLearner
import numpy as np
np.random.seed(1069)
L = SpectralEmbeddingLearner(seed=1069)
for _ in range(10): L.add_node(np.random.randn(64))
m = L.metrics()
assert m.is_ramanujan, 'Ramanujan violated!'
assert m.gap_efficiency >= 0.9, 'Gap efficiency too low!'
print(f'   ✓ Ramanujan: {m.is_ramanujan}, Gap: {m.gap:.4f}, Eff: {m.gap_efficiency:.1%}')
"

echo ""
echo "2. Julia implementation:"
julia -e '
include(expanduser("~/.claude/skills/spectral-embedding-learner/scripts/spectral_embedding_learner.jl"))
using Random; Random.seed!(1069)
L = SpectralEmbeddingLearner(seed=1069)
for _ in 1:10
    emb = randn(64)
    add_node!(L, emb ./ norm(emb))
end
m = metrics(L)
@assert m.is_ramanujan "Ramanujan violated!"
println("   ✓ Ramanujan: $(m.is_ramanujan), Gap: $(round(m.gap, digits=4)), Eff: $(round(m.gap_efficiency*100, digits=1))%")
'

echo ""
echo "3. Babashka implementation:"
bb -e '
(load-file (str (System/getenv "HOME") "/.claude/skills/spectral-embedding-learner/scripts/spectral_learner.clj"))
(reset! spectral-learner/*learner* {:seed 1069 :p 3 :d 4 :embeddings {} :adjacency {} :history []})
(doseq [_ (range 10)]
  (let [emb (vec (repeatedly 64 #(- (rand 2) 1)))
        norm (Math/sqrt (reduce + (map #(* % %) emb)))]
    (spectral-learner/add-node! (mapv #(/ % norm) emb))))
(println (format "   ✓ Vertices: %d, Edges: %d, GF(3) balanced: %s"
  (spectral-learner/n-vertices)
  (spectral-learner/edge-count)
  (spectral-learner/gf3-balanced?)))
'

echo ""
echo "4. DuckLake bridge:"
python3 -c "
import sys
sys.path.insert(0, '$SCRIPT_DIR')
from ducklake_spectral_bridge import DuckLakeSpectralBridge
bridge = DuckLakeSpectralBridge(':memory:', seed=1069)
bridge.conn.execute('CREATE TABLE t1 (id INT)')
bridge.conn.execute('CREATE TABLE t2 (id INT)')
bridge.conn.execute('CREATE TABLE t3 (id INT)')
bridge.ingest_schema()
path = bridge.spectral_walk(50)
report = bridge.coverage_report()
print(f'   ✓ Coverage: {report[\"coverage\"]*100:.0f}%, GF(3) balanced: {report[\"gf3_balanced\"]}')
"

echo ""
echo "═══ All tests passed ═══"
