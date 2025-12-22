# Entropy Metrics Quick Reference

**For Phase 3→4 Transition: Prevent Mode Collapse in Agent-o-rama Training**

---

## TL;DR - The Problem

**Mode Collapse** = Your learned model only generates stereotypical @barton outputs (boring, repetitive, generic) instead of capturing the full diversity of real @barton behavior.

**Interaction Entropy** = How diverse @barton's interactions actually are (good target for preventing collapse).

---

## Quick Usage

### Before Training (Phase 3 Complete)

```clojure
(require '[agents.entropy-metrics :as entropy])

;; Measure diversity of Phase 3 extracted patterns
(let [patterns (load-phase-3-patterns)
      entropies (entropy/calculate-all-entropies
                 (:posts patterns)
                 (:interactions patterns)
                 (:network patterns))]

  ;; Check if data is diverse enough to train on
  (println "Topic entropy:    " (get-in entropies [:topic :topic-entropy]))
  (println "Mode entropy:     " (get-in entropies [:mode :mode-entropy]))
  (println "Temporal entropy: " (get-in entropies [:temporal :temporal-entropy]))
  (println "Network entropy:  " (get-in entropies [:network :network-entropy]))

  ;; Should be > 3.0 bits for healthy training data
  (let [mean-entropy (get-in entropies [:composite :mean-entropy])]
    (if (>= mean-entropy 2.7)
      (println "✅ Data is sufficiently diverse - safe to train")
      (println "⚠️  Data lacks diversity - risk of mode collapse"))))
```

### During Training (Phase 4)

```clojure
;; In your training loop:
(let [generated-data (generate-samples model 1000)
      current-entropies (entropy/calculate-all-entropies
                        generated-data
                        (:interactions generated-data)
                        (:network generated-data))

      entropy-history (conj history current-entropies)
      collapse-risk (entropy/detect-collapse-risk entropy-history)]

  ;; Display metrics every epoch
  (entropy/display-entropy-report current-entropies epoch)

  ;; Check for collapse
  (if (:is-collapsing? collapse-risk)
    (do (entropy/display-collapse-warning collapse-risk)
        ;; RECOVER: restore from earlier checkpoint
        (recur-from-checkpoint ...))

    ;; Continue training
    (recur (inc epoch) ...)))
```

---

## Entropy Targets

| Metric | Target | Healthy | At Risk | Collapse |
|--------|--------|---------|---------|----------|
| **Topic** | >3.5 bits | 3.0-3.8 | 2.0-3.0 | <2.0 |
| **Mode** | >2.4 bits | 2.2-2.6 | 1.5-2.2 | <1.5 |
| **Temporal** | >2.0 bits | 1.8-2.4 | 1.2-1.8 | <1.2 |
| **Network** | >3.2 bits | 3.0-3.8 | 2.0-3.0 | <2.0 |
| **Length** | >1.5 bits | 1.4-2.0 | 1.0-1.4 | <1.0 |
| **Average** | >2.7 bits | 2.5-3.0 | 2.0-2.5 | <2.0 |

---

## Red Flags During Training

### ❌ Mode Collapse Happening

```
Epoch  0: Topic=4.1 Mode=2.5 Temporal=2.2 Network=3.8 → Average=3.32 ✅
Epoch 25: Topic=3.9 Mode=2.4 Temporal=2.1 Network=3.7 → Average=3.22 ✅
Epoch 50: Topic=3.5 Mode=2.2 Temporal=1.9 Network=3.5 → Average=3.02 ✅
Epoch 75: Topic=2.8 Mode=1.6 Temporal=1.2 Network=2.5 → Average=2.03 ❌ COLLAPSE!
```

**Slope**: -0.053 bits/epoch (declining too fast)
**Risk**: CRITICAL - restore checkpoint immediately

### ✅ Healthy Training

```
Epoch  0: Average=3.32 ✅
Epoch 25: Average=3.28 ✅  (slight decline ok)
Epoch 50: Average=3.25 ✅  (stabilizing)
Epoch 75: Average=3.23 ✅  (minor variation expected)
Epoch 100: Average=3.21 ✅ (final model still diverse)
```

**Slope**: -0.011 bits/epoch (slow, stable decline)
**Risk**: LOW - training proceeding normally

---

## Recovery Actions

### If Collapse Detected

1. **Immediate**: Restore from last good checkpoint
   ```clojure
   (load-checkpoint epoch-45)  ; When entropy was still high
   ```

2. **Reduce Learning Rate**:
   ```clojure
   (update-hyperparams {:learning-rate (* current-lr 0.5)})
   ```

3. **Increase Diversity Loss Weight**:
   ```clojure
   (update-hyperparams {:diversity-loss-lambda 0.2})  ; was 0.1
   ```

4. **Use Stratified Sampling**:
   ```clojure
   (defn next-training-batch []
     (stratified-sample-by-mode all-data batch-size))
   ```

---

## Entropy Calculation (What Each Means)

### Topic Entropy (Shannon)
- Measures: How many different topics does @barton discuss?
- High (>3.5): Tech, music, philosophy, math, AI, network, personal, community
- Low (<2.0): Only talks about one thing (e.g., just code)
- **Why**: Different topics → different generation patterns → diversity

### Mode Entropy
- Measures: How varied are interaction types?
- High (>2.4): Mix of posts, replies, quotes, threads, mentions, collaborations
- Low (<1.5): Mostly just posts or mostly just replies
- **Why**: Different modes → different linguistic patterns

### Temporal Entropy
- Measures: How predictable is posting timing?
- High (>2.0): Posts at random times throughout day
- Low (<0.8): Posts every day at exact same time
- **Why**: Predictable timing → repetitive generation patterns

### Network Entropy
- Measures: How diverse are network connections?
- High (>3.2): Mentions/collaborates with many different people
- Low (<1.5): Always same small group
- **Why**: Network diversity → different interaction partners in generation

### Content Length Entropy
- Measures: How varied are post lengths?
- High (>1.8): Mix of short tweets and long essays
- Low (<0.6): All posts same length
- **Why**: Varied length → richer generation patterns

---

## Full Integration with Phase 4

```clojure
(ns agents.phase-4-training-with-entropy)

(defn train-with-entropy-monitoring [phase-3-data max-epochs]
  "Complete training loop with mode collapse prevention"

  ;; 1. Calculate baseline entropy from training data
  (let [baseline-entropy (entropy/calculate-all-entropies
                         (:posts phase-3-data)
                         (:interactions phase-3-data)
                         (:network phase-3-data))

        target-entropy (get-in baseline-entropy [:composite :mean-entropy])]

    (println "📊 Baseline entropy:" target-entropy "bits")
    (println "   Target during training: ≥" (* 0.9 target-entropy) "bits")
    (println "")

    ;; 2. Training loop with monitoring
    (loop [epoch 0
           model (init-agent-model)
           history []
           best-model model
           best-entropy target-entropy]

      (if (>= epoch max-epochs)
        {:model best-model :history history :status :complete}

        (let [;; 3. Train one epoch
              trained-model (train-epoch model phase-3-data)
              generated (generate trained-model 1000)

              ;; 4. Calculate current entropy
              current-entropy (entropy/calculate-all-entropies
                              generated
                              (:interactions generated)
                              (:network generated))

              ;; 5. Calculate loss with diversity penalty
              recon-loss (calculate-reconstruction-loss generated phase-3-data)
              div-loss (entropy/diversity-loss
                       current-entropy baseline-entropy 0.1)
              total-loss (entropy/combined-loss recon-loss div-loss)

              ;; 6. Update history
              new-history (conj history current-entropy)

              ;; 7. Check for collapse
              collapse-risk (if (>= (count new-history) 10)
                             (entropy/detect-collapse-risk new-history)
                             {:is-collapsing? false :risk-level :low})

              ;; 8. Update best checkpoint if improving
              current-mean (get-in current-entropy [:composite :mean-entropy])
              is-best? (> current-mean best-entropy)
              new-best-model (if is-best? trained-model best-model)
              new-best-entropy (if is-best? current-mean best-entropy)]

          ;; 9. Display progress every 10 epochs
          (when (zero? (mod epoch 10))
            (entropy/display-entropy-report current-entropy epoch)
            (println (str "  Loss (recon+div): " (format "%.4f" total-loss)))
            (println ""))

          ;; 10. Collapse detection & recovery
          (if (:is-collapsing? collapse-risk)
            (do (println "⚠️  MODE COLLAPSE DETECTED!")
                (entropy/display-collapse-warning collapse-risk)
                (println "💾 Recovering from best checkpoint (epoch"
                        (- epoch 10) ")")
                {:model new-best-model
                 :history new-history
                 :status :collapsed-at-epoch epoch
                 :recovery-epoch (- epoch 10)})

            ;; 11. Continue training
            (recur (inc epoch)
                   new-best-model
                   new-history
                   new-best-model
                   new-best-entropy)))))))
```

---

## Validation Before Going to Phase 5

```clojure
;; After training completes, validate surrogate entropy
(let [trained-model (load-final-model)
      surrogate-samples (generate trained-model 5000)

      real-entropy (load-stored-baseline-entropy)
      surrogate-entropy (entropy/calculate-all-entropies
                        surrogate-samples
                        (:interactions surrogate-samples)
                        (:network surrogate-samples))]

  ;; Acceptance criteria
  (let [real-mean (get-in real-entropy [:composite :mean-entropy])
        surrogate-mean (get-in surrogate-entropy [:composite :mean-entropy])
        similarity (/ surrogate-mean real-mean)]

    (if (>= similarity 0.9)
      (println "✅ PHASE 4 PASS: Surrogate entropy ≥90% of real data")
      (println "❌ PHASE 4 FAIL: Surrogate entropy only"
              (format "%.1f%%" (* 100 similarity))
              "of real data - insufficient diversity"))))
```

---

## Files

- **Framework**: `INTERACTION_ENTROPY_FRAMEWORK.md` (detailed theory & implementation)
- **Code**: `src/agents/entropy_metrics.clj` (Clojure implementation)
- **Quick Ref**: This file

---

## Next Steps

1. ✅ Phase 1: Data acquisition complete
2. ✅ Phase 2: MCP saturation (ready)
3. ✅ Phase 3: 5D pattern extraction (ready)
4. **→ Phase 4**: Train with entropy monitoring using this framework
5. Phase 5: Validate surrogate has ≥90% entropy of real @barton

Ready to integrate into agent-o-rama training!
