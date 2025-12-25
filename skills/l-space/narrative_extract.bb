#!/usr/bin/env bb
;; L-Space Narrative Extractor - P0 Implementation
;; Extracts narrative structure from text: arcs, causality, novelty
;; 
;; Usage: bb narrative_extract.bb <file.txt>
;; Output: JSON with {arcs, causality_graph, novelty_curve}

(require '[babashka.fs :as fs]
         '[clojure.string :as str]
         '[cheshire.core :as json])

;; --- Narrative Arc Detection ---
;; Identify beginning/middle/end structure via heuristics

(def arc-markers
  {:beginning #{#"(?i)^once" #"(?i)^in the beginning" #"(?i)^there was" 
                #"(?i)^long ago" #"(?i)chapter 1" #"(?i)^first"}
   :climax    #{#"(?i)suddenly" #"(?i)but then" #"(?i)however" 
                #"(?i)at last" #"(?i)finally" #"(?i)the moment"}
   :ending    #{#"(?i)and so" #"(?i)the end" #"(?i)ever after"
                #"(?i)in conclusion" #"(?i)thus" #"(?i)finally$"}})

(defn classify-sentence [sentence]
  "Classify sentence as :beginning, :middle, :climax, or :ending"
  (let [s (str/trim sentence)]
    (cond
      (some #(re-find % s) (:beginning arc-markers)) :beginning
      (some #(re-find % s) (:climax arc-markers))    :climax
      (some #(re-find % s) (:ending arc-markers))    :ending
      :else                                           :middle)))

(defn extract-arcs [sentences]
  "Partition sentences into narrative arcs"
  (let [classified (map-indexed (fn [i s] {:idx i :text s :phase (classify-sentence s)}) 
                                sentences)]
    {:arc-markers (remove #(= :middle (:phase %)) classified)
     :phase-distribution (frequencies (map :phase classified))}))

;; --- Causality Graph ---
;; Extract causal relationships via connective patterns

(def causal-patterns
  [#"(?i)(\w+)\s+(?:caused|leads? to|results? in)\s+(\w+)"
   #"(?i)(?:because|since|as)\s+(\w+).*?,\s*(\w+)"
   #"(?i)(\w+)\s+(?:therefore|thus|hence|so)\s+(\w+)"
   #"(?i)if\s+(\w+).*?then\s+(\w+)"])

(defn extract-causal-edges [text]
  "Extract cause->effect pairs from text"
  (->> causal-patterns
       (mapcat #(re-seq % text))
       (map (fn [[_ cause effect]] {:from cause :to effect}))
       (remove #(nil? (:from %)))
       vec))

(defn build-causality-graph [sentences]
  "Build adjacency list from causal relationships"
  (let [edges (mapcat extract-causal-edges sentences)]
    {:nodes (distinct (concat (map :from edges) (map :to edges)))
     :edges edges
     :edge-count (count edges)}))

;; --- Token Novelty Curve ---
;; Compute surprise based on unigram frequency

(defn tokenize [text]
  "Simple whitespace + punctuation tokenizer"
  (->> (str/lower-case text)
       (re-seq #"\b\w+\b")))

(defn compute-novelty [tokens]
  "Compute novelty = -log2(freq/total) for each token"
  (let [freqs (frequencies tokens)
        total (count tokens)
        log2 #(/ (Math/log %) (Math/log 2))]
    (map-indexed 
     (fn [i tok]
       {:idx i
        :token tok
        :freq (get freqs tok)
        :novelty (- (log2 (/ (get freqs tok) total)))})
     tokens)))

(defn novelty-curve [tokens]
  "Return novelty statistics and high-surprise tokens"
  (let [novelties (compute-novelty tokens)
        values (map :novelty novelties)
        mean-nov (/ (reduce + values) (count values))
        max-nov (apply max values)]
    {:mean-novelty mean-nov
     :max-novelty max-nov
     :high-surprise (filter #(> (:novelty %) (* 2 mean-nov)) novelties)
     :total-tokens (count tokens)}))

;; --- GF(3) Balance Check ---

(defn gf3-balance [arcs]
  "Verify narrative phases balance: beginning(-1) + middle(0) + ending(+1) ≡ 0"
  (let [trit-map {:beginning -1 :middle 0 :climax 0 :ending 1}
        trits (map #(get trit-map (:phase %) 0) (:arc-markers arcs))
        sum (reduce + trits)]
    {:trits trits
     :sum sum
     :balanced? (zero? (mod sum 3))}))

;; --- Main ---

(defn analyze-narrative [text]
  "Full narrative analysis: arcs + causality + novelty"
  (let [sentences (str/split text #"[.!?]+\s*")
        tokens (tokenize text)
        arcs (extract-arcs sentences)
        causality (build-causality-graph sentences)
        novelty (novelty-curve tokens)]
    {:arcs arcs
     :gf3 (gf3-balance arcs)
     :causality causality
     :novelty novelty}))

(defn -main [& args]
  (if (empty? args)
    (do
      (println "Usage: bb narrative_extract.bb <file.txt>")
      (println "       echo 'text' | bb narrative_extract.bb -")
      (System/exit 1))
    (let [input (if (= "-" (first args))
                  (slurp *in*)
                  (slurp (first args)))
          result (analyze-narrative input)]
      (println (json/generate-string result {:pretty true})))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
