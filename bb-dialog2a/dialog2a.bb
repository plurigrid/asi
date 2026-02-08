#!/usr/bin/env bb
;; bb-dialog2a: Babashka dialog library for Plurigrid ASI
;; 3-at-a-time cobordism scale display with GF(3) parallel bifurcation
;; 
;; Scale is reducible. Cobordism is differentiable.
;; Three parallel streams, indicating more exist beyond the horizon.

(ns dialog2a.core
  (:require [babashka.process :refer [shell]]
            [clojure.string :as str]))

;; GF(3) trit values for parallel bifurcation
(def MINUS -1)
(def ERGODIC 0)
(def PLUS 1)

;; SplitMix64 for deterministic coloring (Gay.bb compatible)
(defn splitmix64-next [state]
  (let [z (unchecked-long (+ state 0x9e3779b97f4a7c15))]
    [(bit-xor (bit-shift-right z 30) z)
     z]))

(defn trit-from-hue [hue]
  (let [sector (mod (int (/ hue 120)) 3)]
    (case sector
      0 MINUS
      1 ERGODIC
      2 PLUS)))

(defn hex-color [seed idx]
  (let [[h _] (splitmix64-next (+ seed (* idx 137508)))]
    (format "#%06X" (bit-and h 0xFFFFFF))))

;; Cobordism structure: scale as reducible manifold with boundary
(defrecord Cobordism [source target morphism trit])

(defn make-cobordism [name-a name-b trit]
  (->Cobordism name-a name-b (str name-a " → " name-b) trit))

;; 3-at-a-time display with horizon indicator
(defn display-3-slice [items start-idx total seed]
  (let [slice (vec (take 3 (drop start-idx items)))
        remaining (- total (+ start-idx 3))
        colors (mapv #(hex-color seed (+ start-idx %)) (range (count slice)))]
    {:items (zipmap slice colors)
     :showing [(inc start-idx) (min (+ start-idx 3) total)]
     :total total
     :more? (pos? remaining)
     :remaining remaining}))

;; Scale types for display
(def musical-scales
  ["Ionian" "Dorian" "Phrygian" "Lydian" "Mixolydian" "Aeolian" "Locrian"
   "Harmonic Minor" "Melodic Minor" "Whole Tone" "Diminished" "Augmented"
   "Pentatonic Major" "Pentatonic Minor" "Blues" "Bebop Dominant"
   "Chromatic" "Enigmatic" "Hungarian Minor" "Neapolitan Major"
   "Persian" "Double Harmonic" "Prometheus" "Tritone" "Iwato" "Hirajoshi"])

(def cat#-scales
  ["C#" "D♭" "E♯" "F♭" "G#" "A♭" "B#" "C♭"
   "Enharmonic-1" "Enharmonic-2" "Enharmonic-3"])

(def gf3-structures
  ["MINUS (-1)" "ERGODIC (0)" "PLUS (+1)"
   "Cocycle" "Coboundary" "Cohomology"
   "Bifurcation-A" "Bifurcation-B" "Merge"
   "Split" "Resolve" "Withdraw"])

;; Parallel bifurcation: 3 simultaneous streams
(defn parallel-bifurcation [seed]
  (let [stream-minus (display-3-slice musical-scales 0 (count musical-scales) seed)
        stream-ergodic (display-3-slice cat#-scales 0 (count cat#-scales) (+ seed 1))
        stream-plus (display-3-slice gf3-structures 0 (count gf3-structures) (+ seed 2))]
    {:minus stream-minus
     :ergodic stream-ergodic  
     :plus stream-plus
     :conservation (+ MINUS ERGODIC PLUS)})) ;; = 0, conserved

;; Terminal rendering with ANSI colors
(defn ansi-color [hex]
  (let [r (Integer/parseInt (subs hex 1 3) 16)
        g (Integer/parseInt (subs hex 3 5) 16)
        b (Integer/parseInt (subs hex 5 7) 16)]
    (format "\033[38;2;%d;%d;%dm" r g b)))

(def RESET "\033[0m")

(defn render-stream [label stream trit-val]
  (let [trit-sym (case trit-val -1 "−" 0 "○" 1 "+")]
    (println (format "\n╭─── %s [%s] ───────────────────────" label trit-sym))
    (doseq [[item color] (:items stream)]
      (println (format "│ %s●%s %s" (ansi-color color) RESET item)))
    (when (:more? stream)
      (println (format "│ ⋮ (%d more...)" (:remaining stream))))
    (println "╰────────────────────────────────────")))

(defn render-bifurcation-display [bif]
  (println "\n╔═══════════════════════════════════════════╗")
  (println "║   BB-DIALOG2A: PARALLEL BIFURCATION SCALES ║")
  (println "║   GF(3) Conservation: Σ = 0 ✓             ║")
  (println "╚═══════════════════════════════════════════╝")
  
  (render-stream "MINUS: Musical Scales" (:minus bif) MINUS)
  (render-stream "ERGODIC: Cat# Scales" (:ergodic bif) ERGODIC)
  (render-stream "PLUS: GF(3) Structures" (:plus bif) PLUS)
  
  (println "\n─── Cobordism Differentiability ───")
  (println "Scale is reducible → parallel streams share morphism")
  (println "Bifurcation is covariant → streams evolve together"))

;; Navigation state
(def state (atom {:seed 69
                  :offsets {:minus 0 :ergodic 0 :plus 0}}))

(defn advance-stream [stream-key]
  (let [max-items (case stream-key
                    :minus (count musical-scales)
                    :ergodic (count cat#-scales)
                    :plus (count gf3-structures))]
    (swap! state update-in [:offsets stream-key] 
           #(min (+ % 3) (- max-items 3)))))

(defn current-display []
  (let [{:keys [seed offsets]} @state]
    {:minus (display-3-slice musical-scales (:minus offsets) (count musical-scales) seed)
     :ergodic (display-3-slice cat#-scales (:ergodic offsets) (count cat#-scales) (+ seed 1))
     :plus (display-3-slice gf3-structures (:plus offsets) (count gf3-structures) (+ seed 2))
     :conservation 0}))

;; Main entry point
(defn -main [& args]
  (let [seed (if (seq args) (parse-long (first args)) 69)]
    (reset! state {:seed seed :offsets {:minus 0 :ergodic 0 :plus 0}})
    (render-bifurcation-display (parallel-bifurcation seed))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
