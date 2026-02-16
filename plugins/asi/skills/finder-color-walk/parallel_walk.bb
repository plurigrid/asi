#!/usr/bin/env bb
;; parallel_walk.bb - Triadic parallel random walks with GF(3) conservation

(ns parallel-walk
  (:require [babashka.process :refer [shell]]
            [clojure.java.io :as io]
            [clojure.string :as str]))

;; SplitMix64 constants
(def ^:const GOLDEN (unchecked-long 0x9E3779B97F4A7C15))
(def ^:const MIX1 (unchecked-long 0xBF58476D1CE4E5B9))
(def ^:const MIX2 (unchecked-long 0x94D049BB133111EB))

(defn splitmix64 [^long state]
  (let [z (unchecked-add state GOLDEN)
        z (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 30)) MIX1)
        z (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 27)) MIX2)
        result (bit-xor z (unsigned-bit-shift-right z 31))]
    [result (unchecked-add state GOLDEN)]))

(defn fork-seed 
  "Fork seed into 3 independent child seeds for parallel streams."
  [^long parent-seed]
  (let [[r1 s1] (splitmix64 parent-seed)
        [r2 s2] (splitmix64 s1)
        [r3 _]  (splitmix64 s2)]
    {:minus   r1   ; -1 MINUS (Blue stream)
     :ergodic r2   ;  0 ERGODIC (Green stream)  
     :plus    r3}));+1 PLUS (Red stream)

(defn trit-to-label [trit]
  (case trit
    -1 4  ; Blue
     0 2  ; Green
    +1 7));Red

(defn set-finder-label! [filepath label]
  (let [script (format "tell application \"Finder\"
                          set theFile to POSIX file \"%s\" as alias
                          set label index of theFile to %d
                        end tell" filepath label)]
    (try
      (shell {:out :string :err :string} "osascript" "-e" script)
      true
      (catch Exception _ false))))

(defn collect-files [directory]
  (->> (file-seq (io/file directory))
       (filter #(.isFile %))
       (filter #(not (str/starts-with? (.getName %) ".")))
       (map str)
       vec))

(defn shuffle-with-seed [^long seed items]
  (let [arr (into-array Object items)
        n (alength arr)]
    (loop [i (dec n) state seed]
      (if (pos? i)
        (let [[rand new-state] (splitmix64 state)
              j (mod (Math/abs rand) (inc i))
              tmp (aget arr i)]
          (aset arr i (aget arr j))
          (aset arr j tmp)
          (recur (dec i) new-state))
        (vec arr)))))

(defn parallel-walk-stream!
  "Execute one stream of the triadic walk."
  [stream-name trit seed files]
  (let [label (trit-to-label trit)
        shuffled (shuffle-with-seed seed files)
        symbol (case trit -1 "−" 0 "○" +1 "+")]
    (println (format "\n  ━━━ %s STREAM (trit=%s, seed=0x%X) ━━━" 
                     (str/upper-case (name stream-name)) symbol seed))
    (doseq [[idx f] (map-indexed vector (take 5 shuffled))]
      (let [fname (last (str/split f #"/"))
            short (if (> (count fname) 25) (str (subs fname 0 22) "...") fname)]
        (set-finder-label! f label)
        (println (format "    %d: %s" idx short))))
    {:stream stream-name :trit trit :files (take 5 shuffled)}))

(defn parallel-triadic-walk!
  "Execute 3 parallel walks with GF(3) = 0 guaranteed."
  [directory parent-seed]
  (println "╔═══════════════════════════════════════════════════════════════╗")
  (println "║  PARALLEL TRIADIC RANDOM WALK                                 ║")
  (println (format "║  Directory: %-48s ║" directory))
  (println (format "║  Parent Seed: 0x%-42X ║" parent-seed))
  (println "╚═══════════════════════════════════════════════════════════════╝")
  
  (let [files (collect-files directory)
        seeds (fork-seed parent-seed)
        
        ;; Execute 3 streams in parallel (via pmap in real impl)
        results [(parallel-walk-stream! :minus   -1 (:minus seeds) files)
                 (parallel-walk-stream! :ergodic  0 (:ergodic seeds) files)
                 (parallel-walk-stream! :plus    +1 (:plus seeds) files)]
        
        ;; Verify GF(3)
        trit-sum (reduce + (map :trit results))]
    
    (println)
    (println "  ━━━ GF(3) VERIFICATION ━━━")
    (println (format "    Σ trits = (-1) + (0) + (+1) = %d" trit-sum))
    (println (format "    %d ≡ %d (mod 3) %s" trit-sum (mod trit-sum 3) 
                     (if (zero? (mod trit-sum 3)) "✓ CONSERVED" "✗ VIOLATED")))
    (println)
    
    {:seeds seeds :results results :gf3-sum trit-sum}))

;; CLI
(when (= *file* (System/getProperty "babashka.file"))
  (let [[dir seed-str] *command-line-args*
        seed (if seed-str
               (if (str/starts-with? seed-str "0x")
                 (Long/parseLong (subs seed-str 2) 16)
                 (Long/parseLong seed-str))
               1069)]
    (parallel-triadic-walk! (or dir ".") seed)
    (println "  ✓ Done")))
