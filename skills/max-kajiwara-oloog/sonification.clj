#!/usr/bin/env bb
;; Max Kajiwara Resonance Sonification
;; Maps interaction entities to CatSharp scale

(def entity-tones
  {:max-kajiwara     {:note "C#" :freq 277 :wave "sine"    :trit 1}
   :seventeen-years  {:note "D"  :freq 293 :wave "square"  :trit -1}
   :trelliscraft     {:note "D#" :freq 311 :wave "triangle" :trit 0}
   :nous-os          {:note "D"  :freq 293 :wave "sine"    :trit 1}
   :optimal-stopping {:note "D"  :freq 293 :wave "triangle" :trit 0}
   :vault-hades      {:note "E"  :freq 329 :wave "sine"    :trit 1}
   :constructor      {:note "F"  :freq 349 :wave "square"  :trit -1}
   :ratatat          {:note "F"  :freq 349 :wave "square"  :trit -1}
   :nekuia           {:note "G"  :freq 392 :wave "triangle" :trit 0}
   :archonate        {:note "G"  :freq 392 :wave "square"  :trit -1}
   :joscha-bach      {:note "G#" :freq 415 :wave "sine"    :trit 1}
   :organon-auris    {:note "A"  :freq 440 :wave "sine"    :trit 1}
   :algorithms-to-live-by {:note "B" :freq 493 :wave "square" :trit -1}})

;; Interaction sequence (order of discovery)
(def discovery-sequence
  [:seventeen-years :trelliscraft :nous-os :vault-hades 
   :nekuia :archonate :organon-auris :joscha-bach
   :algorithms-to-live-by :optimal-stopping :constructor])

;; Max's time-of-day pattern (PST)
;; Peak: 5-6 PM (afternoon/evening transition)
;; Deep content: evening hours
(def temporal-envelope
  {:morning   {:amp 0.2 :tempo 1.5}   ; quiet, fast
   :afternoon {:amp 0.4 :tempo 1.0}   ; building
   :evening   {:amp 0.6 :tempo 0.7}   ; peak engagement, slower
   :night     {:amp 0.3 :tempo 0.5}}) ; reflective, slowest

(defn play-tone [{:keys [freq wave]} duration amp]
  (let [cmd ["play" "-q" "-n" "synth" (str duration) 
             wave (str freq) "vol" (str amp)]]
    (apply shell cmd)))

(defn play-sequence [entities duration amp]
  (doseq [e entities]
    (when-let [tone (entity-tones e)]
      (println (str "♪ " (name e) " → " (:note tone) " (" (:wave tone) ")"))
      (play-tone tone duration amp))))

;; Triadic phrases (GF(3) balanced)
(def balanced-triads
  [[:vault-hades :nekuia :archonate]           ; Nous OS core
   [:joscha-bach :optimal-stopping :algorithms-to-live-by] ; Epistemic sources
   [:nous-os :trelliscraft :seventeen-years]]) ; Media refraction

(defn play-triad [triad]
  (println (str "\n▲ Triad: " (mapv name triad)))
  (let [trit-sum (reduce + (map #(:trit (entity-tones %)) triad))]
    (println (str "  Σ trit = " trit-sum " ≡ " (mod trit-sum 3) " (mod 3)"))
    (play-sequence triad 0.25 0.4)
    (Thread/sleep 300)))

;; Main
(when (= *file* (System/getProperty "babashka.file"))
  (println "🎵 Max Kajiwara Resonance Sonification\n")
  
  (println "━━━ Discovery Sequence ━━━")
  (play-sequence discovery-sequence 0.2 0.3)
  
  (println "\n━━━ Balanced Triads ━━━")
  (doseq [triad balanced-triads]
    (play-triad triad))
  
  (println "\n━━━ Subject Signature ━━━")
  (play-tone (entity-tones :max-kajiwara) 1.0 0.5)
  (println "♪ max-kajiwara → C# (sine) — sustained"))
