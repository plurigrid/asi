#!/usr/bin/env bb
;; finder_color_walk.bb - Deterministic Finder coloring via Gay.jl algorithm

(ns finder-color-walk
  (:require [babashka.process :refer [shell]]
            [clojure.java.io :as io]
            [clojure.string :as str]))

;; SplitMix64 constants as signed longs
(def ^:const GOLDEN (unchecked-long 0x9E3779B97F4A7C15))
(def ^:const MIX1 (unchecked-long 0xBF58476D1CE4E5B9))
(def ^:const MIX2 (unchecked-long 0x94D049BB133111EB))

(defn splitmix64 
  "SplitMix64 PRNG step. Returns [random-value new-state]."
  [^long state]
  (let [z (unchecked-add state GOLDEN)
        z (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 30)) MIX1)
        z (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 27)) MIX2)
        result (bit-xor z (unsigned-bit-shift-right z 31))]
    [result (unchecked-add state GOLDEN)]))

(defn color-at 
  "Generate color at index using Gay.jl algorithm."
  [seed index]
  (loop [state seed i 0]
    (let [[rand new-state] (splitmix64 state)]
      (if (= i index)
        (let [hue (* 360.0 (/ (double (bit-and rand 0x7FFFFFFFFFFFFFFF)) 
                              (double 0x7FFFFFFFFFFFFFFF)))
              trit (cond
                     (or (< hue 60) (>= hue 300)) 1   ; PLUS (warm)
                     (< hue 180) 0                     ; ERGODIC (neutral)
                     :else -1)]                        ; MINUS (cold)
          {:hue hue :trit trit :index index})
        (recur new-state (inc i))))))

(defn hue->finder-label 
  "Map hue (0-360) to Finder label index (1-7)."
  [hue]
  (cond
    (< hue 30) 7    ; Red
    (< hue 60) 6    ; Orange
    (< hue 90) 5    ; Yellow
    (< hue 150) 2   ; Green
    (< hue 270) 4   ; Blue
    (< hue 330) 3   ; Purple
    :else 7))       ; Red (wrap)

(def label-names
  {1 "Gray" 2 "Green" 3 "Purple" 4 "Blue" 5 "Yellow" 6 "Orange" 7 "Red"})

(def trit-symbols {-1 "−" 0 "○" 1 "+"})

(defn set-finder-label! 
  "Set macOS Finder label via AppleScript."
  [filepath label]
  (let [abs-path (.getAbsolutePath (io/file filepath))
        script (format "tell application \"Finder\"
                          set theFile to POSIX file \"%s\" as alias
                          set label index of theFile to %d
                        end tell" abs-path label)]
    (try
      (shell {:out :string :err :string} "osascript" "-e" script)
      true
      (catch Exception e
        (println (format "  ⚠ Failed to set label for %s: %s" filepath (.getMessage e)))
        false))))

(defn collect-files 
  "Recursively collect files from directory."
  [directory]
  (->> (file-seq (io/file directory))
       (filter #(.isFile %))
       (filter #(not (str/starts-with? (.getName %) ".")))  ; Skip hidden
       (map str)
       vec))

(defn shuffle-with-seed
  "Fisher-Yates shuffle using SplitMix64 seed for determinism."
  [^long seed items]
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

(defn walk-and-color! 
  "Random walk through directory, coloring files."
  [directory seed max-files]
  (let [all-files (collect-files directory)
        shuffled (shuffle-with-seed seed all-files)
        files (take max-files shuffled)
        results (atom [])
        trit-sum (atom 0)]
    
    (println)
    (println "  ┌────┬────────────────────────────────┬────────┬──────┐")
    (println "  │ ## │ File                           │ Label  │ Trit │")
    (println "  ├────┼────────────────────────────────┼────────┼──────┤")
    
    (doseq [[idx filepath] (map-indexed vector files)]
      (let [{:keys [hue trit]} (color-at seed idx)
            label (hue->finder-label hue)
            filename (last (str/split filepath #"/"))
            short-name (if (> (count filename) 28)
                         (str (subs filename 0 25) "...")
                         filename)]
        
        (swap! trit-sum + trit)
        (swap! results conj {:file filepath :label label :trit trit})
        
        (set-finder-label! filepath label)
        
        (println (format "  │ %2d │ %-30s │ %-6s │  %s   │"
                         idx short-name (label-names label) (trit-symbols trit)))))
    
    (println "  └────┴────────────────────────────────┴────────┴──────┘")
    (println)
    
    (let [gf3-ok? (zero? (mod @trit-sum 3))]
      (println (format "  GF(3) Sum: %d ≡ %d (mod 3) %s"
                       @trit-sum (mod @trit-sum 3) (if gf3-ok? "✓" "✗")))
      {:results @results :gf3-conserved gf3-ok? :trit-sum @trit-sum})))

(defn clear-labels! 
  "Clear all Finder labels in directory."
  [directory]
  (doseq [f (collect-files directory 1000)]
    (set-finder-label! f 0))
  (println "  ✓ Labels cleared"))

;; CLI entrypoint
(when (= *file* (System/getProperty "babashka.file"))
  (let [[cmd-or-dir arg1 arg2] *command-line-args*]
    (cond
      (= cmd-or-dir "clear")
      (do
        (println (format "🧹 CLEARING LABELS: %s" arg1))
        (clear-labels! arg1))
      
      (= cmd-or-dir "help")
      (do
        (println "Usage:")
        (println "  finder_color_walk.bb <directory> [seed] [max-files]")
        (println "  finder_color_walk.bb clear <directory>")
        (println)
        (println "Examples:")
        (println "  finder_color_walk.bb ~/Documents 0x42D 20")
        (println "  finder_color_walk.bb . 1069")
        (println "  finder_color_walk.bb clear ~/Downloads"))
      
      :else
      (let [dir cmd-or-dir
            seed (if arg1 
                   (if (str/starts-with? arg1 "0x")
                     (Long/parseLong (subs arg1 2) 16)
                     (Long/parseLong arg1))
                   1069)
            max-files (if arg2 (Integer/parseInt arg2) 20)]
        (println (format "🎨 FINDER COLOR WALK"))
        (println (format "   Directory: %s" dir))
        (println (format "   Seed: 0x%X (%d)" seed seed))
        (println (format "   Max files: %d" max-files))
        (walk-and-color! dir seed max-files)
        (println)
        (println "  ✓ Done")))))
