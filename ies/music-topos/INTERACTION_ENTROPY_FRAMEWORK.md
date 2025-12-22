# Interaction Entropy & Mode Collapse Prevention Framework

**Status**: Phase 1-3 Integration Framework
**Date**: 2025-12-21
**Purpose**: Prevent mode collapse in cognitive surrogate training

---

## 1. Interaction Entropy Metrics

### 1.1 Topic Entropy (Shannon Entropy)
Measures diversity of topics discussed.

```
H_topic = -Σ(p_i * log(p_i))
where p_i = proportion of posts about topic i
```

**Calculation from Phase 1 data:**
```clojure
(defn calculate-topic-entropy [posts]
  "Posts must have :content field"
  (let [topics (extract-topics posts)  ; NLP: tech, music, philosophy, etc.
        topic-counts (frequencies topics)
        total (count topics)
        proportions (map #(/ % total) (vals topic-counts))
        entropy (- (sum (map #(* % (log %)) proportions)))]
    entropy))

; Example results:
; High entropy (diverse): 4.2 bits (many topics)
; Low entropy (focused):  1.5 bits (few topics)
; Complete collapse:      0.0 bits (single topic)
```

**Target for @barton**: ~3.5-4.0 bits (indicates 12-16 distinct topic areas)

### 1.2 Interaction Mode Entropy
Measures diversity of interaction types.

```
H_modes = -Σ(p_i * log(p_i))
where p_i = proportion of posts of interaction type i
```

**Interaction modes:**
- Original posts (thought/content creation)
- Replies (engagement/discussion)
- Quote posts (commentary/remixing)
- Thread continuations (extended thoughts)
- Mentions/Tags (network connection)
- Collaboration posts (joint work)

**Calculation:**
```clojure
(defn calculate-mode-entropy [interactions]
  "interactions have :mode field"
  (let [mode-counts (frequencies (map :mode interactions))
        total (count interactions)
        proportions (vals (update-vals mode-counts #(/ % total)))
        entropy (- (sum (map #(* % (log %)) proportions)))]
    entropy))

; Expected distribution for @barton:
; Original:        25-30%
; Replies:         35-45%
; Quotes:          10-15%
; Threads:         5-10%
; Mentions:        5-10%
; Collaboration:   5-10%
```

**Target entropy**: ~2.4-2.6 bits (indicates balanced mode distribution)

### 1.3 Temporal Entropy
Measures unpredictability of posting patterns.

```
H_temporal = entropy(inter-post time intervals)
```

**Calculation:**
```clojure
(defn calculate-temporal-entropy [posts]
  "posts sorted by :timestamp"
  (let [timestamps (map :timestamp posts)
        intervals (map #(- %2 %1) timestamps (rest timestamps))
        bucketed (bucket-into-time-bins intervals)  ; 5min, 1hr, 1day, 1week
        entropy (shannon-entropy bucketed)]
    entropy))

; High entropy: Posts at random times (hard to predict next post)
; Low entropy: Posts at exact same time every day (very predictable)
```

**Target**: ~2.0-2.5 bits (indicates natural variation in posting rhythm)

### 1.4 Network Entropy
Measures diversity of connections.

```
H_network = entropy(degree distribution in follower/mention graph)
```

**Calculation:**
```clojure
(defn calculate-network-entropy [network-relationships]
  "relationships with :source :target :type (follow/mention/collab)"
  (let [out-degrees (map count (group-by :source network-relationships))
        entropy (shannon-entropy out-degrees)]
    entropy))

; High entropy: Interacts with many different people
; Low entropy: Only interacts with same small group
```

**Target**: ~3.5-4.0 bits (indicates broad network engagement)

### 1.5 Content Length Entropy
Measures diversity in expression length.

```clojure
(defn calculate-length-entropy [posts]
  (let [lengths (map #(count (:content %)) posts)
        bucketed (bucket-by-quantiles lengths 10)  ; 10 buckets
        entropy (shannon-entropy bucketed)]
    entropy))

; High entropy: Mix of short quips and long essays
; Low entropy: All posts same length
```

**Target**: ~1.8-2.2 bits (indicates varied expression styles)

---

## 2. Mode Collapse Detection

### 2.1 Entropy Collapse Signature

**Red flags during training:**

```
Training Phase 4: Epoch 1
  Topic entropy:     4.1 bits ✅
  Mode entropy:      2.5 bits ✅
  Temporal entropy:  2.2 bits ✅
  Network entropy:   3.8 bits ✅
  ──────────────────────────────

Training Phase 4: Epoch 50
  Topic entropy:     3.8 bits ✅
  Mode entropy:      2.3 bits ✅
  Temporal entropy:  1.9 bits ✅
  Network entropy:   3.6 bits ✅
  ──────────────────────────────

Training Phase 4: Epoch 100
  Topic entropy:     2.1 bits ❌ COLLAPSE ALERT
  Mode entropy:      1.4 bits ❌ COLLAPSE ALERT
  Temporal entropy:  0.8 bits ❌ COLLAPSE ALERT
  Network entropy:   2.2 bits ❌ COLLAPSE ALERT
```

**Collapse symptoms:**
- Entropy drops >50% from epoch 1
- All metrics decline together (not noise)
- Generator repeats same patterns
- Loss plateaus despite training

### 2.2 Early Warning System

Track entropy **slope**, not just values:

```clojure
(defn entropy-collapse-risk [entropy-history]
  "entropy-history = [{:epoch n :entropies {...}}]"
  (let [recent-10 (take-last 10 entropy-history)
        early-10 (take-first 10 entropy-history)

        early-avg (mean (map :topic-entropy early-10))
        recent-avg (mean (map :topic-entropy recent-10))

        slope (/ (- recent-avg early-avg) (count early-10))

        is-collapsing? (< slope -0.1)]  ; Loss >10% per epoch = danger

    {:is-collapsing is-collapsing?
     :slope slope
     :early-avg early-avg
     :recent-avg recent-avg
     :risk-level (cond
                   (< slope -0.2) :critical
                   (< slope -0.1) :high
                   (< slope -0.05) :medium
                   :else :low)}))
```

---

## 3. Mode Collapse Prevention Strategies

### 3.1 Diversity Loss Function

Add to agent-o-rama training loss:

```
Total Loss = Reconstruction Loss + λ * Diversity Loss

Diversity Loss = -Σ(entropy_metrics)
  = -(topic_entropy + mode_entropy + temporal_entropy + network_entropy)
```

**Why**: Penalizes low entropy, encourages high diversity.

```clojure
(defn diversity-loss [generated-posts real-posts]
  (let [real-entropies (calc-all-entropies real-posts)
        gen-entropies (calc-all-entropies generated-posts)

        entropy-mismatch (- (mean (vals real-entropies))
                           (mean (vals gen-entropies)))

        penalty (* 0.1 entropy-mismatch)]  ; λ = 0.1
    penalty))

(defn total-training-loss [reconstructed real generated]
  (+ (reconstruction-loss reconstructed real)
     (diversity-loss generated real)))
```

### 3.2 Stratified Sampling

During training, ensure all modes/topics represented:

```clojure
(defn stratified-training-batch [all-posts batch-size]
  "Ensures each batch has all interaction modes"
  (let [modes (distinct (map :mode all-posts))
        per-mode (int (/ batch-size (count modes)))

        batch (flatten
          (for [mode modes]
            (let [mode-posts (filter #(= (:mode %) mode) all-posts)]
              (take per-mode (shuffle mode-posts)))))]
    (take batch-size (shuffle batch))))
```

### 3.3 Checkpoint-Based Recovery

If collapse detected, restart from earlier checkpoint:

```clojure
(defn train-with-collapse-detection [data initial-model checkpoints]
  (loop [epoch 0
         model initial-model
         entropy-history []]

    (if (>= epoch max-epochs)
      model

      (let [new-model (train-one-epoch model data)
            new-entropies (calc-all-entropies (generate new-model 1000))
            new-history (conj entropy-history new-entropies)

            collapse-risk (entropy-collapse-risk new-history)]

        (if (:is-collapsing? collapse-risk)
          ;; COLLAPSE DETECTED - restore and adjust learning rate
          (let [last-good-checkpoint (last (filter #(>= (:epoch %) (- epoch 10))
                                                   checkpoints))
                recovered-model (:model last-good-checkpoint)
                new-lr (* (:lr last-good-checkpoint) 0.5)]
            (println "⚠️  Mode collapse detected at epoch" epoch)
            (println "💾 Recovering from epoch" (:epoch last-good-checkpoint))
            (println "📉 Reducing learning rate to" new-lr)
            (recur (inc epoch)
                   recovered-model
                   (conj new-history new-entropies)))

          ;; NO COLLAPSE - continue normally
          (recur (inc epoch)
                 new-model
                 new-history))))))
```

### 3.4 Ensemble Methods

Train multiple agents, prevent groupthink:

```clojure
(defn train-diverse-ensemble [data num-agents]
  "Train multiple independent agents with different initializations"
  (let [agents (map #(initialize-agent (random-seed %))
                    (range num-agents))]
    (map #(train-to-convergence % data) agents)))

(defn diversity-across-ensemble [agents test-data]
  "Measure how different the agents' outputs are"
  (let [outputs (map #(generate % test-data) agents)
        pairwise-distances (for [i (range (count agents))
                                j (range (inc i) (count agents))]
                              (kl-divergence (nth outputs i)
                                           (nth outputs j)))]
    {:mean-distance (mean pairwise-distances)
     :min-distance (apply min pairwise-distances)
     :is-diverse? (> (mean pairwise-distances) 0.5)}))
```

---

## 4. Entropy-Based Validation (Phase 3→4 Transition)

### 4.1 Pre-Training Checklist

Before starting Phase 4 agent-o-rama training:

```
Phase 1 Data Quality Checks:
✓ Topic entropy > 3.5 bits
✓ Mode entropy > 2.3 bits
✓ Temporal entropy > 1.8 bits
✓ Network entropy > 3.2 bits
✓ Content length entropy > 1.5 bits
✓ No single topic > 40% of posts
✓ No single mode > 50% of interactions
✓ Temporal gaps < 2 weeks (no dead zones)
✓ Network has > 100 unique connections
```

### 4.2 Training Checkpoints

Save entropy metrics at every epoch:

```clojure
(defn checkpoint-with-entropy [epoch model data]
  {:epoch epoch
   :model model
   :timestamp (now)
   :entropy-metrics {:topic (calculate-topic-entropy data)
                     :mode (calculate-mode-entropy data)
                     :temporal (calculate-temporal-entropy data)
                     :network (calculate-network-entropy data)
                     :length (calculate-length-entropy data)}
   :loss (calculate-loss model data)})

(defn save-checkpoint-if-good [epoch model data history]
  (let [current (checkpoint-with-entropy epoch model data)
        previous (last history)]

    (if (> (mean (vals (:entropy-metrics current)))
           (mean (vals (:entropy-metrics previous))))
      (do (println "💾 Checkpoint saved (entropy improving)")
          (conj history current))
      history)))
```

### 4.3 Entropy Timeline

Expected progression:

```
Phase 1 (Data Acquisition):
  Entropy measured in raw data
  High: 4.0-4.5 bits (diverse real world)

Phase 3 (Pattern Extraction):
  5D patterns capture high-entropy interactions
  Expected: ~3.8 bits in pattern space

Phase 4 (Training):
  Epoch 0:  ~3.5 bits (initial patterns)
  Epoch 25: ~3.4 bits (learning stabilizes)
  Epoch 50: ~3.3 bits (minor overfitting ok)
  Epoch 75: ~3.2 bits (acceptable range)
  Epoch 100: ~3.1 bits (edge of collapse)

  ⚠️ If drops below 2.8 bits → mode collapse

Phase 5 (Surrogate Engine):
  Target: ≥ 3.0 bits (maintains diversity)
  Validation: Surrogate entropy ≥ 90% of training data
```

---

## 5. Implementation in Phase 4

### 5.1 Add to agent-o-rama Training Loop

```clojure
(ns agents.phase-4-training
  (:require [agents.phase-3-patterns :as p3]
            [agents.entropy-metrics :as entropy]))

(defn train-agent-o-rama-with-entropy-monitoring [phase-3-data]
  "Train with real-time entropy monitoring"

  (let [initial-model (initialize-agent-model)
        initial-entropy (entropy/calc-all-entropies phase-3-data)

        checkpoints (atom [])]

    (println "📊 Initial entropy profile:")
    (println "  Topic entropy:    " (:topic initial-entropy) "bits")
    (println "  Mode entropy:     " (:mode initial-entropy) "bits")
    (println "  Temporal entropy: " (:temporal initial-entropy) "bits")
    (println "  Network entropy:  " (:network initial-entropy) "bits")
    (println "")

    (loop [epoch 0
           model initial-model
           history []]

      (if (>= epoch max-epochs)
        (do (println "✅ Training complete - no mode collapse!")
            {:model model :checkpoints @checkpoints})

        (let [trained-model (train-one-epoch model phase-3-data)
              generated (generate trained-model 1000)
              current-entropy (entropy/calc-all-entropies generated)

              collapse-risk (entropy/entropy-collapse-risk history)
              checkpoint (entropy/checkpoint-with-entropy epoch trained-model generated)]

          ;; Log every 10 epochs
          (when (zero? (mod epoch 10))
            (println (format "Epoch %3d | Topic: %.2f | Mode: %.2f | Temporal: %.2f | Network: %.2f"
                           epoch
                           (:topic current-entropy)
                           (:mode current-entropy)
                           (:temporal current-entropy)
                           (:network current-entropy))))

          ;; Check for collapse
          (if (:is-collapsing? collapse-risk)
            (do (println "⚠️  MODE COLLAPSE DETECTED at epoch" epoch)
                (println "💔 Risk level:" (:risk-level collapse-risk))
                (println "📍 Slope:" (format "%.4f" (:slope collapse-risk)))
                (println "💾 Recovering from checkpoint...")
                ;; Recovery logic here
                {:model model :checkpoint-epoch epoch :status :collapsed})

            ;; No collapse, continue
            (recur (inc epoch)
                   trained-model
                   (conj history current-entropy)))))))
```

### 5.2 Entropy Dashboard

Real-time monitoring during training:

```
╔════════════════════════════════════════════════════════════════╗
║             Phase 4: Mode Collapse Prevention Monitor          ║
╚════════════════════════════════════════════════════════════════╝

Epoch 45 / 100
─────────────────────────────────────────────────────────────────
Topic Entropy:       3.42 bits ████████████████░░░░ 86%
Mode Entropy:        2.35 bits ███████████░░░░░░░░░ 94%
Temporal Entropy:    2.11 bits ██████████░░░░░░░░░░ 84%
Network Entropy:     3.65 bits ██████████████████░░ 92%
Length Entropy:      1.87 bits ███████████░░░░░░░░░ 75%

Average Entropy:     2.68 bits ✅ HEALTHY (target: 2.7+)
─────────────────────────────────────────────────────────────────

Collapse Risk:       LOW ✅
  Entropy slope:     -0.012 (stable)
  Variance:          0.14 (natural variation)
  Recovery capability: FULL ✅

Learning Rate:       0.0001
Batch Size:          64
Samples Seen:        2,880

Estimated Time to Complete: 27 minutes
```

---

## 6. Interaction Entropy Table Schema

In DuckDB (Phase 1):

```sql
CREATE TABLE interaction_entropy (
  id INTEGER PRIMARY KEY,
  epoch INTEGER,

  -- Calculated metrics
  topic_entropy FLOAT,
  mode_entropy FLOAT,
  temporal_entropy FLOAT,
  network_entropy FLOAT,
  content_length_entropy FLOAT,

  -- Distribution info
  topic_distribution JSON,      -- {topic: proportion}
  mode_distribution JSON,        -- {mode: count}
  temporal_buckets JSON,         -- {time_range: count}
  network_degree_distribution JSON,

  -- Quality flags
  is_diverse BOOLEAN,
  collapse_risk_level VARCHAR,   -- low/medium/high/critical

  -- Metadata
  data_source VARCHAR,           -- 'training' / 'generated'
  timestamp TIMESTAMP,
  phase VARCHAR                  -- '1' / '3' / '4' / '5'
);

CREATE INDEX idx_entropy_epoch ON interaction_entropy(epoch);
CREATE INDEX idx_entropy_phase ON interaction_entropy(phase);
CREATE INDEX idx_entropy_timestamp ON interaction_entropy(timestamp);
```

---

## 7. Success Criteria

### Phase 4 Training ✅ Complete When:

```
✅ Topic entropy remains > 3.0 bits throughout training
✅ Mode entropy stable > 2.2 bits
✅ Temporal entropy doesn't collapse below 1.5 bits
✅ Network entropy stays > 3.0 bits
✅ No single mode dominates > 60% of outputs
✅ Generated samples have diverse topics/lengths/temporal patterns
✅ Human evaluation: Generated text feels like real @barton (>80% accuracy)
✅ No entropy collapse detected in training history
```

### Phase 5 Validation ✅ Pass When:

```
✅ Surrogate entropy >= 90% of original @barton entropy
✅ Mode distribution of surrogate matches original within 5%
✅ Network interactions diverse, not repetitive
✅ Cognitive fidelity test passes (>85% behavioral match)
```

---

## Summary

**Interaction Entropy** = measure of diversity in @barton's behavior patterns
**Mode Collapse** = risk that agent-o-rama learns only stereotypical patterns

**Prevention**:
1. Measure entropy across 5 dimensions
2. Monitor for collapse during training
3. Apply diversity loss + stratified sampling
4. Recover from checkpoints if needed
5. Use ensemble methods for robustness

**Target**: Keep trained surrogate entropy ≥ 3.0 bits (90%+ of real data diversity)
