#!/usr/bin/env bb
;; CatSharp Sonification - Babashka implementation
;; Play GF(3) color streams as audio via sox
;; 
;; Usage: bb sonify.bb [seed] [steps]
;;        bb sonify.bb 0x42D 12
;;        bb sonify.bb --champions

(require '[babashka.process :refer [shell]]
         '[clojure.string :as str])

;; ═══════════════════════════════════════════════════════════════════════════
;; SplitMix64 (Gay.jl compatible)
;; ═══════════════════════════════════════════════════════════════════════════

(defn splitmix64 [^long seed]
  (let [z (bit-and (unchecked-add seed 0x9E3779B97F4A7C15) 0xFFFFFFFFFFFFFFFF)
        z (bit-and (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 30)) 
                                        0xBF58476D1CE4E5B9) 0xFFFFFFFFFFFFFFFF)
        z (bit-and (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 27)) 
                                        0x94D049BB133111EB) 0xFFFFFFFFFFFFFFFF)]
    (bit-xor z (unsigned-bit-shift-right z 31))))

(defn to-rgb [h]
  [(bit-and (unsigned-bit-shift-right h 16) 0xFF)
   (bit-and (unsigned-bit-shift-right h 8) 0xFF)
   (bit-and h 0xFF)])

(defn rgb->hue [[r g b]]
  (let [r (/ r 255.0) g (/ g 255.0) b (/ b 255.0)
        mx (max r g b) mn (min r g b)]
    (if (= mx mn)
      0.0
      (let [d (- mx mn)
            h (cond
                (= mx r) (+ (/ (- g b) d) (if (< g b) 6 0))
                (= mx g) (+ (/ (- b r) d) 2)
                :else    (+ (/ (- r g) d) 4))]
        (* h 60.0)))))

;; ═══════════════════════════════════════════════════════════════════════════
;; CatSharp Mappings
;; ═══════════════════════════════════════════════════════════════════════════

(defn hue->trit [h]
  (let [h (mod h 360)]
    (cond
      (or (< h 60) (>= h 300)) 1   ; PLUS (warm)
      (< h 180) 0                   ; ERGODIC (neutral)
      :else -1)))                   ; MINUS (cold)

(defn hue->pitch-class [h]
  (int (mod (/ h 30.0) 12)))

(defn pitch-class->freq [pc & {:keys [octave] :or {octave 4}}]
  (let [midi (+ (* 12 (inc octave)) pc)]
    (* 440.0 (Math/pow 2.0 (/ (- midi 69) 12.0)))))

(def note-names ["C" "C#" "D" "Eb" "E" "F" "F#" "G" "G#" "A" "Bb" "B"])
(def waveforms {1 "sine" 0 "triangle" -1 "square"})
(def symbols {1 "🔴" 0 "🟢" -1 "🔵"})

;; ═══════════════════════════════════════════════════════════════════════════
;; Terminal Colors
;; ═══════════════════════════════════════════════════════════════════════════

(defn fg [r g b] (str "\033[38;2;" r ";" g ";" b "m"))
(defn bg [r g b] (str "\033[48;2;" r ";" g ";" b "m"))
(def rst "\033[0m")
(def bold "\033[1m")

;; ═══════════════════════════════════════════════════════════════════════════
;; Playback
;; ═══════════════════════════════════════════════════════════════════════════

(defn play-tone [freq trit & {:keys [duration volume] :or {duration 0.15 volume 0.3}}]
  (let [wave (waveforms trit)]
    (shell {:out :string :err :string}
           "play" "-q" "-n" "synth" (str duration) wave (str freq) "vol" (str volume))))

(defn play-chord [freqs & {:keys [duration volume] :or {duration 0.5 volume 0.25}}]
  (let [args (concat ["play" "-q" "-n" "synth" (str duration)]
                     (mapcat #(vector "sine" (str %)) freqs)
                     ["vol" (str volume)])]
    (apply shell {:out :string :err :string} args)))

(defn sonify-stream [seed steps]
  (println (str "\n" bold (fg 255 100 255) "▶ Sonifying seed 0x" 
                (Long/toHexString seed) " (" steps " steps)" rst "\n"))
  (loop [h seed step 0 trit-sum 0]
    (if (>= step steps)
      (let [gf3 (mod trit-sum 3)]
        (println (str "\n  " (fg 100 255 150) "GF(3) Σ = " trit-sum 
                      (if (zero? gf3) " ✓" (str " ≡ " gf3)) " (mod 3)" rst "\n"))
        {:trit-sum trit-sum :gf3 gf3})
      (let [[r g b] (to-rgb h)
            hue (rgb->hue [r g b])
            trit (hue->trit hue)
            pc (hue->pitch-class hue)
            freq (pitch-class->freq pc)
            note (nth note-names pc)
            hex-c (format "#%02X%02X%02X" r g b)
            ts (case trit 1 "+1" 0 " 0" -1 "-1")]
        (println (str "  " (format "%2d" step) ": " (bg r g b) "████" rst " " 
                      (fg r g b) hex-c rst " " (format "%-2s" note) " [" ts "] ♪" (int freq) "Hz"))
        (play-tone freq trit)
        (recur (splitmix64 h) (inc step) (+ trit-sum trit))))))

(defn play-champions []
  (let [champions [[0xF39ECB83 "Alpha" 99]
                   [0x515E1C62 "Beta" 81]
                   [0xC729546E "Gamma" 76]]]
    (println (str "\n" bold (fg 255 215 0)
                  "╔════════════════════════════════════════════════════════════╗" rst))
    (println (str bold (fg 255 215 0)
                  "║  GF(3) CHAMPIONS • CATSHARP SONIFICATION                  ║" rst))
    (println (str bold (fg 255 215 0)
                  "╚════════════════════════════════════════════════════════════╝" rst "\n"))
    
    (play-chord [261.63 329.63 392.00] :duration 0.4)
    
    (doseq [[seed name full-steps] champions]
      (println (str bold (fg 255 100 200) "▶ " name ": 0x" 
                    (format "%08X" seed) " (full: " full-steps " steps)" rst))
      (let [path (loop [h seed step 0 path ""]
                   (if (>= step 9)
                     path
                     (let [[r g b] (to-rgb h)
                           hue (rgb->hue [r g b])
                           trit (hue->trit hue)
                           pc (hue->pitch-class hue)
                           freq (pitch-class->freq pc)]
                       (play-tone freq trit :duration 0.12)
                       (recur (splitmix64 h) (inc step) (str path (symbols trit))))))]
        (println (str "  " path "\n"))))
    
    (println (str "  " (fg 100 255 150) "Resolution..." rst))
    (play-chord [523.25 659.26 783.99] :duration 0.8 :volume 0.3)
    (println (str "\n" bold (fg 100 200 255) 
                  "═══ GALOIS: seed ⊣ γ ⊣ color ⊣ pitch ⊣ tone ═══" rst "\n"))))

;; ═══════════════════════════════════════════════════════════════════════════
;; CLI
;; ═══════════════════════════════════════════════════════════════════════════

(defn -main [& args]
  (cond
    (some #{"--champions" "-c"} args)
    (play-champions)
    
    :else
    (let [seed (if (seq args)
                 (Long/decode (first args))
                 0x42D)
          steps (if (> (count args) 1)
                  (Integer/parseInt (second args))
                  12)]
      (sonify-stream seed steps))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
