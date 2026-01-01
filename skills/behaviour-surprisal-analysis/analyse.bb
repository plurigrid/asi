#!/usr/bin/env bb
;; Behaviour Surprisal Analysis v3.0 - Tri-Channel with AGM Revision + Cat# Integration
;; Usage: bb analyse.bb --predictions <file> --observed <file> [--alpha 0.3 --beta 0.5 --gamma 0.2]
;;
;; Channels (Cat# Bicomodule Structure):
;;   Direct (α)  - Exact artifact matching | Trit: -1 | Home: Span    | Kan: Ran_K
;;   Diffuse (β) - Thematic/structural     | Trit: 0  | Home: Prof    | Kan: Adj
;;   Meta (γ)    - Capability tracking     | Trit: +1 | Home: Presheaves | Kan: Lan_K
;;
;; Cat# Integration:
;;   - Galois adjunction α ⊣ γ between attention channels
;;   - Bicomodule coherence checking
;;   - Pitch-class sonification via CatSharp scale
;;
;; AGM Revision: Levi Identity K * φ = (K − ¬φ) + φ

(require '[clojure.string :as str]
         '[clojure.set :as set]
         '[babashka.cli :as cli]
         '[babashka.fs :as fs]
         '[babashka.process :as p])

;; ═══════════════════════════════════════════════════════════════
;; CatSharp Scale Constants (Mazzola)
;; ═══════════════════════════════════════════════════════════════

(def catsharp-scale
  "Pitch classes grouped by GF(3) trit assignment"
  {:plus     #{0 4 8}      ;; Augmented triad
   :ergodic  #{3 6 9}      ;; Diminished 7th  
   :minus    #{1 2 5 7 10 11}}) ;; Fifths cycle + passing tones

(def cat#-homes
  "Cat# Three Homes mapping"
  {:minus   {:home :Span :poly-op :× :kan-role :Ran_K :description "Cofree/coalgebra"}
   :ergodic {:home :Prof :poly-op :⊗ :kan-role :Adj   :description "Bicomodule/bridge"}
   :plus    {:home :Presheaves :poly-op :◁ :kan-role :Lan_K :description "Free/algebra"}})

(def base-freq 261.63) ;; C4 = middle C

;; ═══════════════════════════════════════════════════════════════
;; CatSharp Galois Adjunction α ⊣ γ
;; ═══════════════════════════════════════════════════════════════

(defn hue->pitch-class
  "Convert hue (0-360) to pitch class (0-11)"
  [h]
  (mod (Math/round (/ h 30.0)) 12))

(defn pitch-class->hue
  "Convert pitch class to hue"
  [pc]
  (+ (* (mod pc 12) 30.0) 15.0))

(defn pitch-class->trit
  "Map pitch class to GF(3) trit via CatSharp scale"
  [pc]
  (let [pc (mod pc 12)]
    (cond
      (contains? (:plus catsharp-scale) pc) 1
      (contains? (:ergodic catsharp-scale) pc) 0
      :else -1)))

(defn trit->trit-key [t]
  (case t 1 :plus 0 :ergodic -1 :minus :ergodic))

(defn surprisal->pitch-class
  "Map surprisal (0-10+ bits) to pitch class"
  [surp]
  (mod (Math/round (* (min surp 10.0) 1.2)) 12))

(defn pitch-class->freq
  "Convert pitch class to frequency (Hz)"
  [pc]
  (* base-freq (Math/pow 2 (/ pc 12.0))))

(defn α-abstract
  "Abstraction functor: Direct attention → Diffuse pattern
   Part of Galois adjunction α ⊣ γ"
  [direct-result]
  (let [trit (:trit direct-result)
        home-info (get cat#-homes (trit->trit-key trit))]
    (merge direct-result
           {:abstract-type :diffuse
            :hyperedge (case trit 1 :generation 0 :verification -1 :transformation)
            :home (:home home-info)
            :kan-role (:kan-role home-info)})))

(defn γ-concretize
  "Concretization functor: Diffuse pattern → Direct prediction
   Part of Galois adjunction α ⊣ γ"
  [diffuse-result]
  (let [trit (:trit diffuse-result)
        home-info (get cat#-homes (trit->trit-key trit))]
    (merge diffuse-result
           {:concrete-type :direct
            :home (:home home-info)
            :kan-role (:kan-role home-info)})))

(defn verify-galois-unit
  "Verify η: id → γ∘α (unit of adjunction)"
  [direct-result]
  (let [abstracted (α-abstract direct-result)
        concretized (γ-concretize abstracted)]
    {:original-trit (:trit direct-result)
     :round-trip-trit (:trit concretized)
     :coherent? (= (:trit direct-result) (:trit concretized))}))

(defn bicomodule-coherent?
  "Check if prediction-observation pair satisfies Cat# coherence"
  [pred-trit obs-trit]
  ;; Coherent if they're in compatible homes or same trit
  (or (= pred-trit obs-trit)
      (zero? pred-trit)  ;; Ergodic bridges anything
      (zero? obs-trit)))

;; ═══════════════════════════════════════════════════════════════
;; Core Functions (from v2.0)
;; ═══════════════════════════════════════════════════════════════

(defn tokenize [s]
  (->> (str/split (str/lower-case s) #"[\s\-_/]+")
       (filter #(> (count %) 2))
       (remove #{"the" "and" "for" "with" "from" "into" "that" "this"})))

(defn jaccard [s1 s2]
  (let [t1 (set (tokenize s1))
        t2 (set (tokenize s2))
        inter (count (set/intersection t1 t2))
        union (count (set/union t1 t2))]
    (if (zero? union) 0.0 (double (/ inter union)))))

(defn levenshtein [s1 s2]
  (let [n (count s1) m (count s2)]
    (cond
      (zero? n) m
      (zero? m) n
      :else
      (let [d (make-array Integer/TYPE (inc n) (inc m))]
        (doseq [i (range (inc n))] (aset d i 0 i))
        (doseq [j (range (inc m))] (aset d 0 j j))
        (doseq [i (range 1 (inc n))
                j (range 1 (inc m))]
          (aset d i j
                (min (inc (aget d (dec i) j))
                     (inc (aget d i (dec j)))
                     (+ (aget d (dec i) (dec j))
                        (if (= (nth s1 (dec i)) (nth s2 (dec j))) 0 1)))))
        (aget d n m)))))

(defn normalized-lev [s1 s2]
  (let [maxlen (max (count s1) (count s2))]
    (if (zero? maxlen) 1.0
        (- 1.0 (/ (levenshtein s1 s2) maxlen)))))

(defn surprisal [p]
  (cond
    (<= p 0.01) 10.0
    (>= p 0.99) 0.0
    :else (- (/ (Math/log p) (Math/log 2)))))

;; ═══════════════════════════════════════════════════════════════
;; Direct Attention: Exact Matching (Home: Span, Kan: Ran_K)
;; ═══════════════════════════════════════════════════════════════

(defn direct-match [pred observed]
  (apply max 0.0
         (for [obs observed]
           (let [j (jaccard pred obs)
                 l (normalized-lev (str/lower-case pred) (str/lower-case obs))]
             (* 0.5 (+ j l))))))

(defn direct-analysis [predictions observed]
  (for [pred predictions]
    (let [match (direct-match pred observed)
          surp (surprisal match)
          trit (cond (< surp 2) 1 (< surp 5) 0 :else -1)
          home-info (get cat#-homes (trit->trit-key trit))
          pc (surprisal->pitch-class surp)]
      {:prediction pred
       :match match
       :surprisal surp
       :trit trit
       :home (:home home-info)
       :kan-role (:kan-role home-info)
       :pitch-class pc
       :freq (pitch-class->freq pc)})))

;; ═══════════════════════════════════════════════════════════════
;; Diffuse Attention: Thematic Matching (Home: Prof, Kan: Adj)
;; ═══════════════════════════════════════════════════════════════

(defn extract-themes [texts n-themes]
  (let [all-tokens (mapcat tokenize texts)
        freq (frequencies all-tokens)
        top-tokens (->> freq (sort-by val >) (take 50) (map key) set)]
    (let [text-vecs (for [t texts]
                      (let [toks (set (tokenize t))]
                        {:text t :tokens (set/intersection toks top-tokens)}))]
      (->> text-vecs
           (group-by #(first (sort-by (fn [tok] (- (get freq tok 0))) (:tokens %))))
           (take n-themes)
           (map (fn [[k v]]
                  {:theme k
                   :keywords (apply set/union (map :tokens v))
                   :texts (map :text v)}))))))

(defn theme-overlap [theme-keywords observed-tokens]
  (let [inter (count (set/intersection theme-keywords observed-tokens))
        union (count theme-keywords)]
    (if (zero? union) 0.0 (double (/ inter union)))))

(defn diffuse-analysis [predictions observed]
  (let [pred-themes (extract-themes predictions 5)
        obs-tokens (set (mapcat tokenize observed))]
    (for [theme pred-themes]
      (let [overlap (theme-overlap (:keywords theme) obs-tokens)
            surp (surprisal overlap)
            trit (cond (< surp 2) 1 (< surp 5) 0 :else -1)
            home-info (get cat#-homes (trit->trit-key trit))
            pc (surprisal->pitch-class surp)]
        {:theme (:theme theme)
         :keywords (take 5 (:keywords theme))
         :overlap overlap
         :surprisal surp
         :trit trit
         :home (:home home-info)
         :kan-role (:kan-role home-info)
         :pitch-class pc
         :freq (pitch-class->freq pc)}))))

;; ═══════════════════════════════════════════════════════════════
;; Meta Attention: Capability Tracking (Home: Presheaves, Kan: Lan_K)
;; ═══════════════════════════════════════════════════════════════

(defn count-skills [dir]
  (if (and dir (fs/exists? dir))
    (count (fs/list-dir dir))
    0))

(defn capability-delta [before-state after-state]
  {:skills-added (- (get after-state :skills 0) (get before-state :skills 0))
   :mcp-added (- (get after-state :mcp-servers 0) (get before-state :mcp-servers 0))
   :config-changed (not= (get before-state :config-hash) (get after-state :config-hash))})

(defn meta-analysis [before-state after-state capability-events]
  (let [delta (capability-delta before-state after-state)
        events (or capability-events [])
        total-changes (+ (Math/abs (:skills-added delta))
                         (Math/abs (:mcp-added delta))
                         (if (:config-changed delta) 1 0)
                         (count events))
        p-change (if (zero? total-changes) 0.9 (/ 1.0 (+ 1 total-changes)))
        surp (surprisal (- 1 p-change))
        trit (cond (< surp 2) 1 (< surp 5) 0 :else -1)
        home-info (get cat#-homes (trit->trit-key trit))
        pc (surprisal->pitch-class surp)]
    {:delta delta
     :events events
     :total-changes total-changes
     :surprisal surp
     :trit trit
     :home (:home home-info)
     :kan-role (:kan-role home-info)
     :pitch-class pc
     :freq (pitch-class->freq pc)}))

;; ═══════════════════════════════════════════════════════════════
;; AGM Belief Revision (Levi Identity)
;; ═══════════════════════════════════════════════════════════════

(defn kappa-rank [belief]
  "Spohn κ-ranking: lower = more entrenched"
  (let [conf (or (:confidence belief) 0.5)]
    (- (Math/log (/ 1 (max 0.01 conf))))))

(defn entrenchment-order [beliefs]
  "Sort beliefs by entrenchment (most entrenched first)"
  (sort-by kappa-rank beliefs))

(defn contract [beliefs contradicted]
  "Remove contradicted beliefs (AGM contraction)"
  (remove #(contains? contradicted (:content %)) beliefs))

(defn expand [beliefs new-beliefs]
  "Add new beliefs (AGM expansion)"
  (concat beliefs new-beliefs))

(defn levi-revise [beliefs observed]
  "Levi identity: K * φ = (K − ¬φ) + φ"
  (let [contradicted (->> beliefs
                          (filter #(zero? (direct-match (:content %) observed)))
                          (map :content)
                          set)
        contracted (contract beliefs contradicted)
        new-beliefs (for [obs observed]
                      {:content obs :confidence 1.0 :source :observed})]
    (expand contracted new-beliefs)))

;; ═══════════════════════════════════════════════════════════════
;; Sonification via sox
;; ═══════════════════════════════════════════════════════════════

(defn sox-available? []
  (try
    (-> (p/process ["which" "sox"] {:out :string})
        deref
        :exit
        zero?)
    (catch Exception _ false)))

(defn play-tone [freq duration]
  "Play a sine tone via sox"
  (when (sox-available?)
    (try
      @(p/process ["play" "-q" "-n" "synth" (str duration) "sine" (str freq)]
                  {:out :inherit :err :inherit})
      (catch Exception e
        (println "  [sox unavailable]")))))

(defn sonify-channel [results channel-name duration]
  "Sonify a channel's surprisal as a chord"
  (when (sox-available?)
    (let [freqs (if (map? results)
                  [(:freq results)]
                  (map :freq results))
          avg-freq (/ (reduce + freqs) (max 1 (count freqs)))]
      (println (format "  ♪ %s: %.1f Hz" channel-name avg-freq))
      (play-tone avg-freq duration))))

(defn sonify-all [direct diffuse meta-result]
  "Sonify all three channels as sequential tones"
  (println "\n  CATSHARP SONIFICATION")
  (println "  ───────────────────────────────────────────────────────────────")
  (sonify-channel direct "Direct (Ran_K)" 0.3)
  (Thread/sleep 100)
  (sonify-channel diffuse "Diffuse (Adj)" 0.3)
  (Thread/sleep 100)
  (sonify-channel meta-result "Meta (Lan_K)" 0.3))

;; ═══════════════════════════════════════════════════════════════
;; Combined Tri-Channel Analysis with Cat# Structure
;; ═══════════════════════════════════════════════════════════════

(defn check-bicomodule-coherence [direct diffuse meta-result]
  "Verify Cat# bicomodule coherence across channels"
  (let [direct-trits (map :trit direct)
        diffuse-trits (map :trit diffuse)
        meta-trit (:trit meta-result)
        
        ;; Check Galois unit η: id → γ∘α
        galois-checks (map verify-galois-unit direct)
        galois-coherent? (every? :coherent? galois-checks)
        
        ;; Check bicomodule compatibility
        all-pairs (for [d direct-trits
                        df diffuse-trits]
                    (bicomodule-coherent? d df))
        bicomodule-coherent? (> (/ (count (filter identity all-pairs))
                                   (max 1 (count all-pairs)))
                                0.5)]
    {:galois-coherent? galois-coherent?
     :bicomodule-coherent? bicomodule-coherent?
     :coherence-ratio (/ (count (filter identity all-pairs))
                         (max 1 (count all-pairs)))}))

(defn combined-analysis 
  ([predictions observed alpha] 
   (combined-analysis predictions observed alpha 0.5 0.0 {} {} [] false))
  ([predictions observed alpha beta gamma before-state after-state cap-events sonify?]
   (let [;; Normalize weights
         total-weight (+ alpha beta gamma)
         alpha-n (/ alpha total-weight)
         beta-n (/ beta total-weight)
         gamma-n (/ gamma total-weight)
         
         ;; Channel analyses with Cat# structure
         direct (direct-analysis predictions observed)
         diffuse (diffuse-analysis predictions observed)
         meta-result (meta-analysis before-state after-state cap-events)
         
         ;; Cat# coherence check
         coherence (check-bicomodule-coherence direct diffuse meta-result)
         
         ;; Totals
         direct-total (reduce + (map :surprisal direct))
         diffuse-total (reduce + (map :surprisal diffuse))
         meta-total (:surprisal meta-result)
         
         ;; Averages
         direct-avg (/ direct-total (max 1 (count direct)))
         diffuse-avg (/ diffuse-total (max 1 (count diffuse)))
         
         ;; Weighted total
         weighted (+ (* alpha-n direct-total) 
                     (* beta-n diffuse-total) 
                     (* gamma-n meta-total))]
     {:direct direct
      :diffuse diffuse
      :meta meta-result
      :coherence coherence
      :direct-total direct-total
      :diffuse-total diffuse-total
      :meta-total meta-total
      :direct-avg direct-avg
      :diffuse-avg diffuse-avg
      :weighted-total weighted
      :alpha alpha-n
      :beta beta-n
      :gamma gamma-n
      :sonify? sonify?
      :recommended-weights 
      (cond
        (> meta-total 5) {:alpha 0.2 :beta 0.3 :gamma 0.5}
        (> direct-avg (* 2 diffuse-avg)) {:alpha 0.2 :beta 0.6 :gamma 0.2}
        (> diffuse-avg (* 2 direct-avg)) {:alpha 0.6 :beta 0.2 :gamma 0.2}
        :else {:alpha 0.3 :beta 0.5 :gamma 0.2})})))

;; ═══════════════════════════════════════════════════════════════
;; Output Formatting
;; ═══════════════════════════════════════════════════════════════

(defn format-trit [t]
  (case t 1 "+" 0 "○" -1 "−" "?"))

(defn format-home [home]
  (case home :Span "Span" :Prof "Prof" :Presheaves "Presh" "?"))

(defn format-kan [kan]
  (case kan :Ran_K "Ran" :Adj "Adj" :Lan_K "Lan" "?"))

(defn print-results [results]
  (println "╔══════════════════════════════════════════════════════════════════╗")
  (printf  "║  BEHAVIOUR SURPRISAL ANALYSIS v3.0 (Cat# + AGM)                  ║%n")
  (printf  "║  α=%.2f (Span/Ran) β=%.2f (Prof/Adj) γ=%.2f (Presh/Lan)          ║%n"
           (double (:alpha results))
           (double (:beta results))
           (double (:gamma results)))
  (println "╚══════════════════════════════════════════════════════════════════╝")
  (println)

  (println "  DIRECT ATTENTION (Home: Span, Kan: Ran_K)")
  (println "  ───────────────────────────────────────────────────────────────")
  (println "  Prediction                      │ Match │ S_dir │ Trit │ PC │ Home")
  (println "  ────────────────────────────────┼───────┼───────┼──────┼────┼─────")
  (doseq [d (:direct results)]
    (printf "  %-33s │ %5.1f%% │ %5.2f │  %s   │ %2d │ %s%n"
            (subs (:prediction d) 0 (min 33 (count (:prediction d))))
            (double (* 100 (:match d)))
            (double (:surprisal d))
            (format-trit (:trit d))
            (:pitch-class d)
            (format-home (:home d))))
  (println)

  (println "  DIFFUSE ATTENTION (Home: Prof, Kan: Adj)")
  (println "  ───────────────────────────────────────────────────────────────")
  (println "  Theme Cluster                   │ Overlap │ S_diff │ Trit │ PC │ Home")
  (println "  ────────────────────────────────┼─────────┼────────┼──────┼────┼─────")
  (doseq [d (:diffuse results)]
    (printf "  %-33s │  %5.1f%% │  %5.2f │  %s   │ %2d │ %s%n"
            (str (:theme d) " [" (str/join "," (take 2 (:keywords d))) "]")
            (double (* 100 (:overlap d)))
            (double (:surprisal d))
            (format-trit (:trit d))
            (:pitch-class d)
            (format-home (:home d))))
  (println)

  (println "  META ATTENTION (Home: Presheaves, Kan: Lan_K)")
  (println "  ───────────────────────────────────────────────────────────────")
  (let [m (:meta results)]
    (printf  "  Skills Δ: %+d  MCP Δ: %+d  Config Changed: %s%n"
             (get-in m [:delta :skills-added] 0)
             (get-in m [:delta :mcp-added] 0)
             (if (get-in m [:delta :config-changed]) "yes" "no"))
    (printf  "  Events: %d │ S_meta: %5.2f │ Trit: %s │ PC: %2d │ Home: %s%n"
             (:total-changes m)
             (double (:surprisal m))
             (format-trit (:trit m))
             (:pitch-class m)
             (format-home (:home m))))
  (println)

  (println "  CAT# COHERENCE")
  (println "  ───────────────────────────────────────────────────────────────")
  (let [c (:coherence results)]
    (printf  "  Galois adjunction α ⊣ γ:    %s%n"
             (if (:galois-coherent? c) "✓ coherent" "✗ defect"))
    (printf  "  Bicomodule compatibility:   %.1f%% (%s)%n"
             (double (* 100 (:coherence-ratio c)))
             (if (:bicomodule-coherent? c) "✓" "✗")))
  (println)

  (println "  COMBINED METRICS")
  (println "  ═══════════════════════════════════════════════════════════════")
  (printf  "  Direct Surprisal:    %6.2f bits (avg %.2f bits/pred)%n"
           (double (:direct-total results)) (double (:direct-avg results)))
  (printf  "  Diffuse Surprisal:   %6.2f bits (avg %.2f bits/theme)%n"
           (double (:diffuse-total results)) (double (:diffuse-avg results)))
  (printf  "  Meta Surprisal:      %6.2f bits%n"
           (double (:meta-total results)))
  (printf  "  Weighted Total:      %6.2f bits%n%n"
           (double (:weighted-total results)))

  (println "  ATTENTION DIAGNOSIS (AGM + Cat#)")
  (println "  ───────────────────────────────────────────────────────────────")
  (let [da (:direct-avg results)
        dfa (:diffuse-avg results)
        meta-s (:meta-total results)
        rec (:recommended-weights results)]
    (cond
      (> meta-s 5)
      (do (println "  → HIGH META SURPRISAL: Capability blind spot (Lan_K expansion needed)")
          (println "  → Skill installs or infrastructure changes were unpredicted")
          (printf  "  → Recommend: (α=%.1f, β=%.1f, γ=%.1f)%n"
                   (:alpha rec) (:beta rec) (:gamma rec)))
      (> da (* 2 dfa))
      (do (println "  → Direct (Ran_K) too specific - shift to Prof bicomodules")
          (println "  → Diffuse themes well-calibrated")
          (printf  "  → Recommend: (α=%.1f, β=%.1f, γ=%.1f)%n"
                   (:alpha rec) (:beta rec) (:gamma rec)))
      (> dfa (* 2 da))
      (do (println "  → Direct (Ran_K) well-calibrated")
          (println "  → Diffuse (Adj) too vague - needs Span grounding")
          (printf  "  → Recommend: (α=%.1f, β=%.1f, γ=%.1f)%n"
                   (:alpha rec) (:beta rec) (:gamma rec)))
      :else
      (do (println "  → Balanced tri-channel Cat# profile")
          (println "  → All three homes (Span/Prof/Presheaves) contributing")
          (printf  "  → Current weights optimal%n"))))

  (println)
  (let [all-trits (concat (map :trit (:direct results)) 
                          (map :trit (:diffuse results))
                          [(:trit (:meta results))])
        trit-sum (reduce + all-trits)]
    (printf  "  GF(3) Conservation: Σtrits = %d ≡ %d (mod 3) %s%n"
             trit-sum (mod trit-sum 3)
             (if (zero? (mod trit-sum 3)) "✓" "✗"))
    (println "  Channel Trits: Direct(Span) + Diffuse(Prof) + Meta(Presh) → Cat# coherent"))
  
  ;; Sonification
  (when (:sonify? results)
    (sonify-all (:direct results) (:diffuse results) (:meta results))))

;; ═══════════════════════════════════════════════════════════════
;; CLI Interface
;; ═══════════════════════════════════════════════════════════════

(def cli-opts
  {:predictions {:alias :p :desc "Predictions (JSON file or comma-separated)"}
   :observed {:alias :o :desc "Observed outcomes (JSON file or comma-separated)"}
   :alpha {:alias :a :desc "Direct attention weight (Span/Ran_K)" :default 0.3 :coerce :double}
   :beta {:alias :b :desc "Diffuse attention weight (Prof/Adj)" :default 0.5 :coerce :double}
   :gamma {:alias :g :desc "Meta attention weight (Presheaves/Lan_K)" :default 0.2 :coerce :double}
   :skills-before {:desc "Skills directory state before (for meta channel)"}
   :skills-after {:desc "Skills directory state after (for meta channel)"}
   :sonify {:alias :s :desc "Enable CatSharp sonification" :default true :coerce :boolean}
   :mode {:alias :m :desc "Analysis mode: standard, agm, catsharp" :default "catsharp"}})

(defn parse-input [s]
  (if (str/ends-with? s ".json")
    (-> s slurp clojure.edn/read-string)
    (str/split s #",")))

(defn -main [& args]
  (let [opts (cli/parse-opts args {:spec cli-opts})
        predictions (if (:predictions opts)
                      (parse-input (:predictions opts))
                      ;; Default demo predictions (from thread paste t₀)
                      ["VirtualizationBridge sandbox test"
                       "Derangement permutation group"
                       "GF(3) lattice diagram"
                       "Wavelet compression thread"
                       "Ruby MCP endpoint test"])
        observed (if (:observed opts)
                   (parse-input (:observed opts))
                   ;; Default demo observed (from thread paste t₁)
                   ["GF(3) skill composition and Galois connection verification"
                    "Integrate VirtualizationBridge into parallel vi exit demo"
                    "Wolfram Modelica documentation integration analysis"
                    "Archive files with wavelet decomposition schemes"
                    "Derangement operators and GF(3) entropy management"])
        alpha (or (:alpha opts) 0.3)
        beta (or (:beta opts) 0.5)
        gamma (or (:gamma opts) 0.2)
        sonify? (or (:sonify opts) false)
        ;; Meta channel state (from paste context)
        before-state {:skills (if (:skills-before opts)
                                (count-skills (:skills-before opts))
                                45)
                      :mcp-servers 12
                      :config-hash "a3f2c1"}
        after-state {:skills (if (:skills-after opts)
                               (count-skills (:skills-after opts))
                               418)  ;; 45 + 373 from plurigrid/asi
                     :mcp-servers 28  ;; world_a through world_z + alice + bob
                     :config-hash "b7d3e2"}
        cap-events [{:type "skill_install" :count 373 :source "plurigrid/asi"}
                    {:type "mcp_addition" :server "world_a_aptos"}]
        results (combined-analysis predictions observed alpha beta gamma 
                                   before-state after-state cap-events sonify?)]
    (print-results results)))

(apply -main *command-line-args*)
