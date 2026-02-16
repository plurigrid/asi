#!/usr/bin/env bb
;; Max Kajiwara Interleaved Worlds Sonification
;; 3 parallel self-seeking loops woven together

(require '[babashka.process :refer [shell]])

;; ═══════════════════════════════════════════════════════════════════════════
;; WORLD A: Epistemic Sources
;; Attractor: optimal-stopping (D, 293 Hz, triangle)
;; Loop: joscha-bach → algorithms → optimal-stopping → brian-christian → return
;; ═══════════════════════════════════════════════════════════════════════════

(def world-a
  [{:e :joscha-bach :n "G#" :f 415 :w "sine" :s :collapse}
   {:e :super-ab :n "G#/B" :f [415 493] :w ["sine" "square"] :s :superposition}
   {:e :algorithms-to-live-by :n "B" :f 493 :w "square" :s :collapse}
   {:e :optimal-stopping :n "D" :f 293 :w "triangle" :s :attractor}
   {:e :super-db :n "D/B" :f [293 493] :w ["triangle" "square"] :s :superposition}
   {:e :brian-christian :n "B" :f 493 :w "square" :s :collapse}
   {:e :joscha-bach :n "G#" :f 415 :w "sine" :s :return}
   {:e :optimal-stopping :n "D" :f 293 :w "triangle" :s :attractor}
   {:e :super-dgb :n "D/G#/B" :f [293 415 493] :w ["tri" "sine" "sq"] :s :superposition}
   {:e :manifold-podcast :n "E" :f 329 :w "sine" :s :collapse}
   {:e :optimal-stopping :n "D" :f 293 :w "triangle" :s :attractor}
   {:e :joscha-bach :n "G#" :f 415 :w "sine" :s :return}
   {:e :optimal-stopping :n "D" :f 293 :w "triangle" :s :final}])

;; ═══════════════════════════════════════════════════════════════════════════
;; WORLD B: Nous OS Architecture
;; Attractor: nekuia (G, 392 Hz, triangle) - the remembering layer
;; Loop: vault-hades(-1) → nekuia(0) → archonate(+1) → return
;; Drone: organon-auris (A, 440 Hz) - always-on voice capture
;; ═══════════════════════════════════════════════════════════════════════════

(def world-b
  [{:e :organon-auris :n "A" :f 440 :w "sine" :s :drone}
   {:e :vault-hades :n "E" :f 329 :w "sine" :s :memory}
   {:e :vault-hades :n "E" :f 329 :w "sine" :s :memory}
   {:e :nekuia :n "G" :f 392 :w "triangle" :s :attractor}
   {:e :triadic-super :n "E/G/G" :f [329 392 392] :w ["sine" "tri" "sq"] :s :superposition}
   {:e :nekuia :n "G" :f 392 :w "triangle" :s :remembering}
   {:e :archonate :n "G" :f 392 :w "square" :s :worlding}
   {:e :organon-auris :n "A" :f 440 :w "sine" :s :drone}
   {:e :archonate :n "G" :f 392 :w "square" :s :worlding}
   {:e :triadic-super :n "E/G/G" :f [329 392 392] :w ["sine" "tri" "sq"] :s :superposition}
   {:e :nekuia :n "G" :f 392 :w "triangle" :s :attractor}
   {:e :diorthotes :n "E" :f 329 :w "sine" :s :correction}
   {:e :vault-hades :n "E" :f 329 :w "sine" :s :return}])

;; ═══════════════════════════════════════════════════════════════════════════
;; WORLD C: Media Refraction
;; Attractor: trelliscraft (D#, 311 Hz, triangle) - the central concept
;; Observer: max-kajiwara (C#, 277 Hz) - collapses superpositions
;; Structure mirrors "Seventeen Years": intro → build → breakdown → resolution
;; ═══════════════════════════════════════════════════════════════════════════

(def world-c
  [{:e :max-kajiwara :n "C#" :f 277 :w "sine" :s :observe}
   {:e :seventeen-years :n "D" :f 293 :w "square" :s :intro}
   {:e :trelliscraft :n "D#" :f 311 :w "triangle" :s :attractor}
   {:e :build-super :n "D/F" :f [293 349] :w ["square" "square"] :s :superposition}
   {:e :ratatat :n "F" :f 349 :w "square" :s :build}
   {:e :trelliscraft :n "D#" :f 311 :w "triangle" :s :build}
   {:e :refract-stack :n "D/D#/F" :f [293 311 349] :w ["sq" "tri" "sq"] :s :superposition}
   {:e :max-kajiwara :n "C#" :f 277 :w "sine" :s :observe}
   {:e :seventeen-years :n "D" :f 147 :w "square" :s :breakdown}
   {:e :ratatat :n "F" :f 175 :w "sine" :s :breakdown}
   {:e :trelliscraft :n "D#" :f 156 :w "triangle" :s :attractor}
   {:e :refract-unity :n "D/D#/F/C#" :f [293 311 349 277] :w "all" :s :superposition}
   {:e :max-kajiwara :n "C#" :f 277 :w "sine" :s :return}])

;; ═══════════════════════════════════════════════════════════════════════════
;; INTERLEAVING ENGINE
;; Round-robin: A₀ B₀ C₀ A₁ B₁ C₁ ... creates cross-world resonance
;; ═══════════════════════════════════════════════════════════════════════════

(defn interleave-worlds [& worlds]
  (let [max-len (apply max (map count worlds))
        padded (map #(concat % (repeat nil)) worlds)]
    (->> (apply interleave (map #(take max-len %) padded))
         (remove nil?)
         vec)))

(def interleaved 
  (map-indexed 
    (fn [i step] (assoc step :idx i :world (cond 
                                             (< (mod i 3) 1) :A
                                             (< (mod i 3) 2) :B
                                             :else :C)))
    (interleave-worlds world-a world-b world-c)))

;; ═══════════════════════════════════════════════════════════════════════════
;; SONIFICATION
;; ═══════════════════════════════════════════════════════════════════════════

(defn freq->sox [f w dur]
  (if (vector? f)
    ;; Superposition: multiple frequencies
    (let [synths (map (fn [freq wave] (str wave " " freq)) f (if (vector? w) w (repeat w)))]
      (str "play -q -n synth " dur " " (clojure.string/join " synth " dur " " synths) " vol 0.25"))
    ;; Single collapse
    (str "play -q -n synth " dur " " w " " f " vol 0.3")))

(defn play-step [{:keys [e f w s idx world]}]
  (let [dur (case s
              :superposition 0.4
              :attractor 0.35
              :drone 0.3
              :observe 0.3
              0.2)
        world-symbol (case world :A "◆" :B "◇" :C "○")]
    (println (format "%2d %s %-20s %s" idx world-symbol (name e) 
                     (if (vector? f) (str "⟨" (clojure.string/join " " f) "⟩") f)))
    (when (not (vector? f))
      (shell "play" "-q" "-n" "synth" (str dur) (or w "sine") (str f) "vol" "0.25"))))

(defn play-sequence [steps]
  (println "\n═══════════════════════════════════════════════════")
  (println "   MAX KAJIWARA RESONANCE: INTERLEAVED WORLDS")
  (println "═══════════════════════════════════════════════════")
  (println "   ◆ World A: Epistemic Sources")
  (println "   ◇ World B: Nous OS Architecture")  
  (println "   ○ World C: Media Refraction")
  (println "═══════════════════════════════════════════════════\n")
  (doseq [step steps]
    (play-step step)
    (Thread/sleep 150)))

;; ═══════════════════════════════════════════════════════════════════════════
;; SELF-SEEKING LOOP DETECTION
;; Find where each world returns to its attractor
;; ═══════════════════════════════════════════════════════════════════════════

(def attractors {:A :optimal-stopping :B :nekuia :C :trelliscraft})

(defn find-loops [steps]
  (let [grouped (group-by :world steps)]
    (into {} 
      (map (fn [[world world-steps]]
             (let [attractor (attractors world)
                   indices (keep-indexed 
                             (fn [i step] (when (= (:e step) attractor) i))
                             world-steps)]
               [world {:attractor attractor :return-points indices}]))
           grouped))))

;; ═══════════════════════════════════════════════════════════════════════════
;; MAIN
;; ═══════════════════════════════════════════════════════════════════════════

(when (= *file* (System/getProperty "babashka.file"))
  (println "🎵 Interleaved Worlds Sonification")
  (println (str "   Total steps: " (count interleaved)))
  (println (str "   Superpositions: " (count (filter #(= :superposition (:s %)) interleaved))))
  (println "\n📍 Self-Seeking Loop Points:")
  (doseq [[world {:keys [attractor return-points]}] (find-loops interleaved)]
    (println (format "   %s → %s at indices %s" (name world) (name attractor) return-points)))
  (println "")
  (play-sequence (take 24 interleaved))  ; Play first 24 steps
  (println "\n═══════════════════════════════════════════════════")
  (println "   ✓ Sequence complete"))
