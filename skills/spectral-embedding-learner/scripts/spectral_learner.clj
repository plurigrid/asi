#!/usr/bin/env bb
;; Spectral Embedding Learner - Babashka CLI
;; Self-learning topological embedding with configurable gamut

(ns spectral-learner
  (:require [babashka.pods :as pods]
            [clojure.java.shell :refer [sh]]
            [clojure.string :as str]
            [cheshire.core :as json]))

;; Try to load DuckDB pod
(try
  (pods/load-pod 'org.babashka/go-sqlite3 "0.2.3")
  (catch Exception _ nil))

;; === Gay.jl-compatible color generation ===

(def ^:const PHI (/ (+ 1 (Math/sqrt 5)) 2))
(def ^:const GOLDEN-ANGLE (/ 360.0 (* PHI PHI)))

(defn splitmix64-next [state]
  ;; Simplified hash for Babashka compatibility
  (let [h (hash [state 0x9e3779b97f4a7c15])]
    [(Math/abs h) (inc state)]))

(defn hue-at [seed idx]
  (loop [state (long seed) i 0]
    (if (>= i idx)
      (let [[next-val _] (splitmix64-next state)]
        (mod (+ (* (/ (double next-val) Long/MAX_VALUE) 180) 
                (* idx GOLDEN-ANGLE)) 
             360))
      (let [[_ new-state] (splitmix64-next state)]
        (recur new-state (inc i))))))

(defn trit-at [seed idx]
  (loop [state (long seed) i 0]
    (if (>= i idx)
      (let [[next-val _] (splitmix64-next state)]
        (- (mod (Math/abs next-val) 3) 1))
      (let [[_ new-state] (splitmix64-next state)]
        (recur new-state (inc i))))))

(defn hsl->rgb [h s l]
  (let [c (* (- 1 (Math/abs (- (* 2 l) 1))) s)
        x (* c (- 1 (Math/abs (- (mod (/ h 60) 2) 1))))
        m (- l (/ c 2))
        [r g b] (cond
                  (< h 60)  [c x 0]
                  (< h 120) [x c 0]
                  (< h 180) [0 c x]
                  (< h 240) [0 x c]
                  (< h 300) [x 0 c]
                  :else     [c 0 x])]
    [(int (* 255 (+ r m)))
     (int (* 255 (+ g m)))
     (int (* 255 (+ b m)))]))

(defn hex-at [seed idx]
  (let [h (hue-at seed idx)
        [r g b] (hsl->rgb h 0.7 0.55)]
    (format "#%02X%02X%02X" r g b)))

;; === Spectral Learner State ===

(def ^:dynamic *learner* 
  (atom {:seed 1069
         :p 3  ; gamut prime
         :d 4  ; target degree
         :embeddings {}
         :adjacency {}
         :history []}))

(defn n-vertices [] (count (:embeddings @*learner*)))

(defn ramanujan-bound []
  (* 2 (Math/sqrt (- (:d @*learner*) 1))))

(defn optimal-gap []
  (- (:d @*learner*) (ramanujan-bound)))

(defn gamut-depth 
  ([] (gamut-depth (n-vertices)))
  ([n] (if (> n 0) 
         (int (Math/ceil (/ (Math/log n) (Math/log (:p @*learner*)))))
         0)))

;; === P-adic Distance ===

(defn p-adic-valuation [n p]
  (if (zero? n)
    Integer/MAX_VALUE
    (loop [n n k 0]
      (if (zero? (mod n p))
        (recur (quot n p) (inc k))
        k))))

(defn p-adic-norm [n p]
  (let [v (p-adic-valuation n p)]
    (if (= v Integer/MAX_VALUE) 
      0.0 
      (Math/pow p (- v)))))

(defn p-adic-distance [a b]
  (let [p (:p @*learner*)
        scale (Math/pow 2 20)
        diff-int (mapv #(int (* (- %1 %2) scale)) a b)
        norms (map #(if (not= % 0) (p-adic-norm (Math/abs %) p) 0.0) diff-int)]
    (apply max 0.0 norms)))

;; === Graph Operations ===

(defn add-edge! [u v]
  (swap! *learner* update-in [:adjacency u] (fnil conj #{}) v)
  (swap! *learner* update-in [:adjacency v] (fnil conj #{}) u))

(defn remove-edge! [u v]
  (swap! *learner* update-in [:adjacency u] disj v)
  (swap! *learner* update-in [:adjacency v] disj u))

(defn neighbors [u]
  (get-in @*learner* [:adjacency u] #{}))

;; === Metrics (simplified - full spectral analysis requires numpy/julia) ===

(defn edge-count []
  (/ (reduce + (map count (vals (:adjacency @*learner*)))) 2))

(defn avg-degree []
  (let [n (n-vertices)]
    (if (zero? n) 0 (/ (* 2 (edge-count)) n))))

(defn is-connected? []
  (let [n (n-vertices)]
    (if (<= n 1) 
      true
      (let [visited (atom #{0})
            queue (atom [0])]
        (while (seq @queue)
          (let [u (first @queue)]
            (swap! queue rest)
            (doseq [v (neighbors u)]
              (when-not (@visited v)
                (swap! visited conj v)
                (swap! queue conj v)))))
        (= (count @visited) n)))))

;; === Random Walk ===

(defn random-walk [steps & {:keys [start teleport-prob] 
                            :or {teleport-prob 0.15}}]
  (let [n (n-vertices)]
    (if (zero? n)
      []
      (loop [current (or start (rand-int n))
             path [current]
             remaining steps]
        (if (zero? remaining)
          path
          (let [next-node (if (< (rand) teleport-prob)
                            (rand-int n)
                            (let [nbrs (vec (neighbors current))]
                              (if (empty? nbrs) current (rand-nth nbrs))))]
            (recur next-node (conj path next-node) (dec remaining))))))))

(defn walk-coverage [steps & {:keys [runs] :or {runs 10}}]
  (let [n (n-vertices)]
    (if (zero? n)
      0.0
      (/ (reduce + (for [_ (range runs)]
                     (/ (count (set (random-walk steps))) n)))
         runs))))

;; === Add Node with Learning ===

(defn add-node! [embedding]
  (let [node-id (n-vertices)]
    (swap! *learner* assoc-in [:embeddings node-id] embedding)
    (swap! *learner* assoc-in [:adjacency node-id] #{})
    
    (when (> node-id 0)
      ;; Find candidates by p-adic distance
      (let [candidates (->> (keys (:embeddings @*learner*))
                            (filter #(not= % node-id))
                            (map (fn [other]
                                   [other (p-adic-distance embedding 
                                                          (get-in @*learner* [:embeddings other]))]))
                            (sort-by second)
                            (take (* 2 (:d @*learner*))))]
        ;; Add edges (simplified - no full spectral check in bb)
        (doseq [[other _] (take (:d @*learner*) candidates)]
          (add-edge! node-id other))))
    
    (swap! *learner* update :history conj
           {:node node-id
            :edges (count (neighbors node-id))
            :color (hex-at (:seed @*learner*) node-id)
            :trit (trit-at (:seed @*learner*) node-id)})
    
    node-id))

;; === GF(3) Conservation ===

(defn gf3-total []
  (reduce + (map :trit (:history @*learner*))))

(defn gf3-balanced? []
  (zero? (mod (gf3-total) 3)))

;; === DuckDB Persistence ===

(defn save-to-duckdb! [db-path]
  (let [state @*learner*
        json-data (json/generate-string state)]
    (sh "duckdb" db-path "-c"
        (format "CREATE TABLE IF NOT EXISTS spectral_learner (
                   id INTEGER PRIMARY KEY,
                   seed BIGINT,
                   gamut_prime INT,
                   target_degree INT,
                   n_vertices INT,
                   edge_count INT,
                   gf3_total INT,
                   gf3_balanced BOOLEAN,
                   state_json TEXT,
                   created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                 );
                 INSERT INTO spectral_learner 
                 (id, seed, gamut_prime, target_degree, n_vertices, edge_count, gf3_total, gf3_balanced, state_json)
                 VALUES (
                   (SELECT COALESCE(MAX(id), 0) + 1 FROM spectral_learner),
                   %d, %d, %d, %d, %d, %d, %s, '%s'
                 );"
                (:seed state)
                (:p state)
                (:d state)
                (n-vertices)
                (edge-count)
                (gf3-total)
                (if (gf3-balanced?) "true" "false")
                (str/replace json-data "'" "''")))))

;; === CLI ===

(defn demo []
  (println "=== Spectral Embedding Learner (Babashka) ===\n")
  
  (reset! *learner* {:seed 1069 :p 3 :d 4 :embeddings {} :adjacency {} :history []})
  
  (println (format "Seed: %d" (:seed @*learner*)))
  (println (format "Gamut prime: %d (depth = log_%d(n))" (:p @*learner*) (:p @*learner*)))
  (println (format "Target degree: %d" (:d @*learner*)))
  (println (format "Ramanujan bound: λ₂ ≤ %.4f" (ramanujan-bound)))
  (println)
  
  (let [n-nodes 20 dim 64]
    (println (format "Adding %d nodes with %d-dim embeddings...\n" n-nodes dim))
    
    (doseq [i (range n-nodes)]
      (let [emb (vec (repeatedly dim #(- (rand 2) 1)))
            norm (Math/sqrt (reduce + (map #(* % %) emb)))
            emb-normalized (mapv #(/ % norm) emb)]
        (add-node! emb-normalized)
        
        (when (zero? (mod (inc i) 5))
          (let [last-hist (last (:history @*learner*))]
            (println (format "  n=%2d: edges=%d, color=%s, trit=%d"
                           (inc i)
                           (edge-count)
                           (:color last-hist)
                           (:trit last-hist))))))))
  
  (println "\n=== Final Metrics ===")
  (println (format "Vertices: %d" (n-vertices)))
  (println (format "Edges: %d" (edge-count)))
  (println (format "Avg degree: %.2f" (double (avg-degree))))
  (println (format "Connected: %s" (is-connected?)))
  (println (format "GF(3) total: %d" (gf3-total)))
  (println (format "GF(3) balanced: %s" (gf3-balanced?)))
  
  (println "\n=== Random Walk Coverage ===")
  (doseq [steps [10 50 100]]
    (println (format "  %3d steps: %.1f%% coverage" 
                    steps (double (* 100 (walk-coverage steps :runs 20))))))
  
  (println "\n=== Color Trail ===")
  (doseq [h (take 5 (:history @*learner*))]
    (println (format "  Node %d: %s (trit=%d)" (:node h) (:color h) (:trit h)))))

(defn -main [& args]
  (cond
    (= (first args) "demo") (demo)
    (= (first args) "save") (do (demo) 
                                (save-to-duckdb! (or (second args) "spectral_learner.duckdb"))
                                (println "\nSaved to DuckDB."))
    :else (demo)))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
