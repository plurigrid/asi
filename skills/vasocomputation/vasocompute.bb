#!/usr/bin/env bb
;; vasocompute.bb — interactive REPL core for the vasocomputation skill grid.
;;
;; Two ways to use it:
;;   1. Self-test:   bb skills/vasocomputation/vasocompute.bb
;;   2. Live REPL:   load into forj / gorj_bb, then call the forms below, e.g.
;;        (require '[vasocompute :as v] :reload)
;;        (v/verify-balanced)                  ;=> true   (both triads Sigma trit = 0)
;;        (v/skill :latched-hyperprior)        ;=> hypothesis card
;;        (v/latch {:hold 250})                ;=> residual latch after a held contraction
;;        (v/kyle-lambda (v/latch {:hold 250})); price-impact analogue 1/lambda_min(H)
;;
;; Model: Hai & Murphy (1988) four-state latch-bridge. A LATCH is not "high Ca2+";
;; it is the attached + DEphosphorylated state (AM) that holds force at low Ca2+/low
;; ATP. It forms via a PROTOCOL: contract at high Ca2+, then release -> cross-bridges
;; dephosphorylate while still attached -> tension persists. "Held long enough ->
;; latches" (LHH): residual latch rises monotonically with hold duration.
(ns vasocompute (:require [clojure.math :as m]))

;; ── the grid ────────────────────────────────────────────────────────────────
(def triads
  {:timescale {:cvh +1 :vch 0 :lhh -1}        ; CVH compress / VCH clamp / LHH latch
   :substrate {:vascular +1 :immune 0 :synaptic -1}})

(def skills
  {:compressive-vasomotion {:trit +1 :triad :timescale :hypothesis "CVH" :band :fast
                            :gloss "vasomotion = compression sweep collapsing Bayesian-blur SOHMs"}
   :vascular-clamp         {:trit 0  :triad :timescale :hypothesis "VCH" :band :medium
                            :gloss "contraction freezes pattern = prediction-as-tension = medium-term memory"}
   :latched-hyperprior     {:trit -1 :triad :timescale :hypothesis "LHH" :band :slow
                            :gloss "latch-bridge cements a committed hyperprior; a kinetic exit barrier"}
   :vasocomputation        {:trit +1 :triad :substrate :substrate "vascular" :band :medium
                            :gloss "VSMC tension = inference landscape (umbrella)"}
   :neuroimmune-pruning    {:trit 0  :triad :substrate :substrate "immune" :band :slow
                            :gloss "microglia + complement = TMS justifier / garbage collector"}
   :neural-potentiation    {:trit -1 :triad :substrate :substrate "synaptic" :band :slowest
                            :gloss "LTP writes neuron priors = learning landscape"}})

(defn gf3-sum [t] (mod (reduce + (vals (triads t))) 3))   ; 0 ⇒ balanced
(defn verify-balanced [] (every? zero? (map gf3-sum (keys triads))))
(defn skill [k] (get skills k))

;; ── Hai–Murphy (1988) four-state latch-bridge ───────────────────────────────
;; states: M (detached, dephospho) · Mp (detached, phospho)
;;         · AMp (attached, cycling) · AM (attached, latched/dephospho)
;; k1 = k6 = MLCK phosphorylation rate ∝ [Ca2+]; k2 = k5 = MLCP dephosphorylation;
;; k7 = AM→M latch detachment ≪ everything else ⇒ force held cheaply.
(def k0 {:k2 0.5 :k3 0.4 :k4 0.1 :k5 0.5 :k7 0.01})
(defn deriv [{:keys [k1 k2 k3 k4 k5 k6 k7]} [M Mp AMp AM]]
  [(+ (* (- k1) M)  (* k2 Mp)            (* k7 AM))
   (+ (* k1 M)      (* k4 AMp)           (* (- (+ k2 k3)) Mp))
   (+ (* k3 Mp)     (* k6 AM)            (* (- (+ k4 k5)) AMp))
   (+ (* k5 AMp)                         (* (- (+ k6 k7)) AM))])
(defn tension [[_ _ AMp AM]] (+ AMp AM))
(defn step-run [ca dt steps s0]
  (let [ks (assoc k0 :k1 ca :k6 ca)]
    (loop [n steps s s0]
      (if (zero? n) s (recur (dec n) (mapv (fn [x dx] (+ x (* dt dx))) s (deriv ks s)))))))

(defn simulate-latch-bridge
  "Fixed-Ca2+ integration from rest. Returns end state + tension/phospho/latch."
  [{:keys [ca dt steps] :or {ca 0.55 dt 0.1 steps 400}}]
  (let [[M Mp AMp AM :as s] (step-run ca dt steps [1.0 0.0 0.0 0.0])]
    {:state (zipmap [:M :Mp :AMp :AM] s) :tension (+ AMp AM) :phospho (+ AMp Mp) :latch AM}))

(def baseline-latch
  "Residual tension with NO contraction (resting equilibrium) — the latch floor."
  (tension (step-run 0.02 0.1 600 [1.0 0.0 0.0 0.0])))

(defn latch
  "The LHH protocol: contract at ca-hi for `hold` steps, release to ca-lo for
   `release` steps. Residual tension above baseline = the latched hyperprior."
  [{:keys [ca-hi ca-lo hold release dt] :or {ca-hi 0.9 ca-lo 0.02 hold 200 release 300 dt 0.1}}]
  (let [peaked (step-run ca-hi dt hold [1.0 0.0 0.0 0.0])
        relaxed (step-run ca-lo dt release peaked)]
    {:peak (tension peaked)
     :residual (tension relaxed)
     :latch-above-baseline (max 0.0 (- (tension relaxed) baseline-latch))
     :AM (nth relaxed 3)}))

;; ── empirical hooks (oldies / premise welds) ────────────────────────────────
;; A held latch shrinks the spectral gap of the justification/Fisher Hessian H:
;; belief-updating becomes illiquid. spread ∝ 1/λ_min(H); Kyle's λ ≈ 1/λ_min(H).
(defn spectral-gap [r] (max 1e-6 (- 1.0 (:latch-above-baseline r))))  ; λ_min(H)
(defn kyle-lambda  [r] (/ 1.0 (spectral-gap r)))
(def band-tau {:fast 5 :medium 25 :slow 100 :slowest 1000})           ; CVH→VCH→LHH→synaptic
(defn latch-tau [k] (get band-tau (:band (skill k))))

;; ── self-test ───────────────────────────────────────────────────────────────
(defn -main [& _]
  (println "GF(3) triads:" triads)
  (println "balanced? " (verify-balanced) " sums:" (zipmap (keys triads) (map gf3-sum (keys triads))))
  (println (format "baseline (no contraction) latch floor = %.3f" baseline-latch))
  (println "LHH: residual latch rises with hold duration (held long enough -> latches):")
  (doseq [h [10 40 100 250]]
    (let [r (latch {:hold h})]
      (println (format "  hold=%-4d peak=%.3f residual=%.3f latch+=%.3f  λmin=%.3f  kyleλ=%.2f"
                       h (:peak r) (:residual r) (:latch-above-baseline r)
                       (spectral-gap r) (kyle-lambda r)))))
  (println "τ ladder (CVH/VCH/LHH/synaptic):"
           (mapv latch-tau [:compressive-vasomotion :vascular-clamp :latched-hyperprior :neural-potentiation])))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
