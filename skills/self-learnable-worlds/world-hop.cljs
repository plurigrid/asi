#!/usr/bin/env nbb
;; world-hop.cljs - Transfer learning via world-hopping
;; Usage: npx nbb world-hop.cljs <from-seed> <to-seed>
;;
;; Implements Badiou-inspired world navigation:
;; - Triangle inequality constrains valid hops
;; - Patterns transfer between accessible worlds
;; - GF(3) conservation maintained

(ns self-learnable-worlds.hop
  (:require ["child_process" :as cp]
            [clojure.string :as str]))

;;; ============================================================
;;; Configuration
;;; ============================================================

(def HOME (.-HOME (.-env js/process)))
(def DB-PATH (str HOME "/.autopoiesis/worlds.duckdb"))

;;; ============================================================
;;; World Representation
;;; ============================================================

(defn splitmix64-step [z]
  (let [z1 (bit-xor z (unsigned-bit-shift-right z 30))
        z2 (bit-xor z1 (* z1 0xBF584))
        z3 (bit-xor z2 (unsigned-bit-shift-right z2 27))
        z4 (bit-xor z3 (* z3 0x94D04))]
    (Math/abs (bit-xor z4 (unsigned-bit-shift-right z4 31)))))

(defn create-world [seed epoch]
  (let [derived (splitmix64-step (bit-xor seed epoch))
        trit-raw (mod derived 3)
        trit (if (= trit-raw 2) -1 trit-raw)]
    {:seed seed
     :epoch epoch
     :trit trit
     :derived derived
     :patterns []
     :hue (* (/ (mod derived 65536) 65536) 360)}))

;;; ============================================================
;;; Distance Metrics
;;; ============================================================

(defn hamming-distance [a b]
  "Count differing bits between two numbers."
  (let [xor (bit-xor a b)]
    ;; Count set bits
    (loop [n xor count 0]
      (if (zero? n)
        count
        (recur (bit-and n (dec n)) (inc count))))))

(defn world-distance [w1 w2]
  "Calculate distance between two worlds.
   Components: seed divergence, epoch separation, trit difference."
  (let [;; Seed component: Hamming distance
        seed-dist (hamming-distance (:seed w1) (:seed w2))
        
        ;; Epoch component: absolute difference
        epoch-dist (Math/abs (- (:epoch w1) (:epoch w2)))
        
        ;; Trit component: weighted difference
        trit-dist (* 10 (Math/abs (- (:trit w1) (:trit w2))))]
    
    (Math/sqrt (+ (* seed-dist seed-dist)
                  (* epoch-dist epoch-dist)
                  (* trit-dist trit-dist)))))

(defn max-hop-distance [world]
  "Maximum single hop distance for a world."
  (case (:trit world)
    1  3.0   ; PLUS can hop further (exploratory)
    0  2.5   ; ERGODIC medium range
    -1 2.0   ; MINUS conservative hops
    2.5))

;;; ============================================================
;;; Triangle Inequality
;;; ============================================================

(defn triangle-valid? [w1 w2 w3]
  "Check if path w1→w2→w3 satisfies triangle inequality."
  (let [d12 (world-distance w1 w2)
        d23 (world-distance w2 w3)
        d13 (world-distance w1 w3)]
    {:valid? (<= d13 (+ d12 d23))
     :d12 d12
     :d23 d23
     :d13 d13
     :excess (- d13 (+ d12 d23))}))

;;; ============================================================
;;; Pattern Transfer
;;; ============================================================

(defn pattern-compatible? [pattern target-world]
  "Check if pattern trit is GF(3)-compatible with target."
  (let [combined (+ (:trit pattern) (:trit target-world))]
    (zero? (mod combined 3))))

(defn transfer-patterns [from-world to-world]
  "Transfer compatible patterns from source to target."
  (let [compatible (filter #(pattern-compatible? % to-world)
                          (:patterns from-world))
        transferred (vec compatible)]
    {:to-world (update to-world :patterns concat transferred)
     :transferred-count (count transferred)
     :transferred transferred}))

;;; ============================================================
;;; Path Finding
;;; ============================================================

(defn accessible? [from to]
  "Can we hop directly from 'from' to 'to'?"
  (<= (world-distance from to) (max-hop-distance from)))

(defn find-intermediate [from to]
  "Find an intermediate world for indirect hop."
  ;; Generate candidate intermediate world by averaging seeds
  (let [mid-seed (bit-and (+ (:seed from) (:seed to)) 0xFFFFFFFF)
        mid-epoch (int (/ (+ (:epoch from) (:epoch to)) 2))]
    (create-world mid-seed mid-epoch)))

(defn find-path [from to]
  "Find a path from 'from' to 'to' respecting triangle inequality."
  (if (accessible? from to)
    ;; Direct hop
    {:path [from to]
     :direct? true
     :total-distance (world-distance from to)}
    
    ;; Find intermediate
    (let [mid (find-intermediate from to)]
      (if (and (accessible? from mid) (accessible? mid to))
        (let [tri (triangle-valid? from mid to)]
          (if (:valid? tri)
            {:path [from mid to]
             :direct? false
             :intermediate mid
             :distances tri
             :total-distance (+ (:d12 tri) (:d23 tri))}
            {:error "Triangle inequality violated"
             :details tri}))
        {:error "No valid intermediate found"}))))

;;; ============================================================
;;; Hop Execution
;;; ============================================================

(defn execute-hop [from to]
  "Execute world-hop with pattern transfer."
  (println)
  (println "╔═══════════════════════════════════════════════════════════════╗")
  (println "║  WORLD-HOP                                                     ║")
  (println "╚═══════════════════════════════════════════════════════════════╝")
  (println (str "  From: seed=0x" (.toString (:seed from) 16)
               " epoch=" (:epoch from)
               " trit=" (case (:trit from) -1 "−" 0 "○" 1 "+")))
  (println (str "  To:   seed=0x" (.toString (:seed to) 16)
               " epoch=" (:epoch to)
               " trit=" (case (:trit to) -1 "−" 0 "○" 1 "+")))
  (println)
  
  (let [path-result (find-path from to)]
    (if (:error path-result)
      (do
        (println (str "  ❌ " (:error path-result)))
        (when (:details path-result)
          (println (str "     Excess: " (:excess (:details path-result))))))
      
      (do
        (println (str "  Path: " (if (:direct? path-result) "DIRECT" "VIA INTERMEDIATE")))
        (println (str "  Distance: " (.toFixed (:total-distance path-result) 3)))
        
        (when (:intermediate path-result)
          (let [mid (:intermediate path-result)]
            (println (str "  Intermediate: seed=0x" (.toString (:seed mid) 16)
                         " epoch=" (:epoch mid)))))
        
        ;; Transfer patterns along path
        (println)
        (println "  Pattern Transfer:")
        (loop [worlds (:path path-result)
               total-transferred 0]
          (if (< (count worlds) 2)
            (println (str "  Total patterns transferred: " total-transferred))
            (let [[w1 w2] (take 2 worlds)
                  result (transfer-patterns w1 w2)]
              (println (str "    " (:seed w1) " → " (:seed w2)
                           ": " (:transferred-count result) " patterns"))
              (recur (rest worlds) (+ total-transferred (:transferred-count result))))))
        
        ;; GF(3) check
        (let [path-trits (map :trit (:path path-result))
              trit-sum (reduce + path-trits)
              gf3 (mod trit-sum 3)]
          (println)
          (println (str "  GF(3) path sum: " trit-sum " ≡ " gf3 " (mod 3) "
                       (if (zero? gf3) "✓" "⚠"))))))
    
    (println)
    (println "═══════════════════════════════════════════════════════════════")
    path-result))

;;; ============================================================
;;; CLI
;;; ============================================================

(defn print-help []
  (println "
world-hop.cljs - Transfer learning via world-hopping

Usage:
  npx nbb world-hop.cljs <from-seed> <to-seed>
  npx nbb world-hop.cljs <from-seed>:<epoch> <to-seed>:<epoch>

Arguments:
  from-seed   Hex seed of source world (e.g., 0x42D)
  to-seed     Hex seed of target world
  epoch       Optional epoch number (default: 0)

Examples:
  npx nbb world-hop.cljs 0x42D 0x1069
  npx nbb world-hop.cljs 0x42D:5 0x1069:10
"))

(defn parse-world-spec [spec]
  "Parse 'seed' or 'seed:epoch' format."
  (let [parts (str/split spec #":")]
    (if (= (count parts) 2)
      {:seed (js/parseInt (first parts) 16)
       :epoch (js/parseInt (second parts))}
      {:seed (js/parseInt spec 16)
       :epoch 0})))

(defn -main [& args]
  (let [[from-spec to-spec] args]
    (cond
      (or (nil? from-spec) (= from-spec "--help") (= from-spec "-h"))
      (print-help)
      
      (nil? to-spec)
      (println "Error: Both from and to seeds required")
      
      :else
      (let [from-parsed (parse-world-spec from-spec)
            to-parsed (parse-world-spec to-spec)
            from-world (create-world (:seed from-parsed) (:epoch from-parsed))
            to-world (create-world (:seed to-parsed) (:epoch to-parsed))]
        (if (or (js/isNaN (:seed from-world)) (js/isNaN (:seed to-world)))
          (println "Error: Invalid seed format. Use hex like 0x42D")
          (execute-hop from-world to-world))))))

(apply -main *command-line-args*)
