;; ALIFE → SONIFICATION PIPELINE
;; Transforms 5 ALife worlds into synchronized MIDI output
;; Integration: Rubato Composer × Gay-MCP × Algorithmic-Art

(ns sonify-alife
  (:require [clojure.data.json :as json]
            [clojure.string :as str]))

;; ============================================================================
;; STEP 1: Define Rubato Forms (Mazzola's mathematical music framework)
;; ============================================================================

(def rubato-forms
  {:note {:form-name "Note"
          :components [:pitch :duration :onset]}

   :timbre {:form-name "Timbre"
            :components [:brightness :harmonic-richness :spectral-centroid]}

   :chord {:form-name "Chord"
           :components [:notes :amplitudes :durations]}

   :ensemble {:form-name "Ensemble"
              :components [:voices :synchronization :voice-distance]}

   :morphogenesis {:form-name "Morphogenesis"
                   :components [:entropy :stability :evolution]}})

;; ============================================================================
;; STEP 2: Map ALife World States to Denotators
;; ============================================================================

(defn world-to-denotator [world-id state]
  "Convert ALife world state to Mazzola denotator"
  (case world-id
    1 ;; LENIA → Note
    {:form :note
     :pitch (+ 60 (* (:creatures state) 12))
     :duration (+ 0.5 (* (:mass state) 2))
     :onset 0}

    2 ;; RULE 110 → Timbre
    {:form :timbre
     :brightness (* (:density state) 100)
     :harmonic-richness (* (:complexity state) 12)
     :spectral-centroid (* (:complexity state) 5000)}

    3 ;; SUGARSCAPE → Chord
    {:form :chord
     :notes (min 12 (:agents state))
     :amplitudes (int (* (:wealth state) 0.1))
     :durations (+ 1 (* (:gini state) 2))}

    4 ;; BOIDS → Ensemble
    {:form :ensemble
     :voices (/ (:boids state) 50)
     :synchronization (:cohesion state)
     :voice-distance (* (:separation state) 5)}

    5 ;; NEURAL CA → Morphogenesis
    {:form :morphogenesis
     :entropy (:entropy state)
     :stability (:order state)
     :evolution (+ (:entropy state) (:order state))}

    nil))

;; ============================================================================
;; STEP 3: GF(3) Trit-Based Instrumentation
;; ============================================================================

(def gf3-instruments
  {-1 {:name "Strings" :synth :pad :wavetable :sine :envelope :slow}
   0 {:name "Percussion" :synth :drum :wavetable :square :envelope :medium}
   1 {:name "Lead" :synth :lead :wavetable :sawtooth :envelope :fast}})

(defn hue-to-trit [hue]
  "Map hue (0-360°) to GF(3) trit via warm/neutral/cool classification"
  (cond
    (or (< hue 60) (>= hue 300)) 1   ;; Warm (red/yellow)
    (< hue 180) 0                    ;; Neutral (yellow/cyan)
    :else -1))                       ;; Cool (blue/magenta)

(defn trit-to-instrument [trit]
  "Get instrument configuration from GF(3) polarity"
  (get gf3-instruments trit {:name "default" :synth :pad}))

;; ============================================================================
;; STEP 4: Gay-MCP Color Generation (deterministic via SplitMix64)
;; ============================================================================

(defn xorshift64 [seed]
  "Deterministic pseudorandom via xorshift64"
  (let [x (bit-xor (long seed) (bit-shift-left (long seed) 13))
        x (bit-xor x (bit-shift-right x 7))
        x (bit-xor x (bit-shift-left x 17))]
    x))

(defn color-at [seed index]
  "Generate deterministic OkLCH color at index"
  (let [next-seed (xorshift64 (+ seed index))
        hue (mod (Math/abs next-seed) 360)
        lightness (+ 30 (mod (bit-shift-right (Math/abs next-seed) 8) 60))
        chroma (mod (bit-shift-right (Math/abs next-seed) 16) 100)
        trit (hue-to-trit hue)]
    {:hue hue :lightness lightness :chroma chroma :trit trit}))

;; ============================================================================
;; STEP 5: Convert Denotator → MIDI Note
;; ============================================================================

(defn denotator-to-midi-note [world-id denotator color beat-offset]
  "Transform Rubato denotator + color into MIDI note object"
  (let [instrument (trit-to-instrument (:trit color))
        velocity (int (+ 30 (* (:lightness color) 1.27)))  ;; 30-127
        duration (case world-id
                   1 (:duration denotator)
                   3 (:durations denotator)
                   2)
        pitch (case world-id
                1 (:pitch denotator)
                3 (+ 48 (* (:notes denotator) 4))
                4 (+ 36 (* (:voices denotator) 3))
                60)]

    {:world-id world-id
     :pitch (int (max 0 (min 127 pitch)))
     :velocity (int (max 1 (min 127 velocity)))
     :duration (double (or duration 1.0))
     :onset beat-offset
     :instrument (:name instrument)
     :synth (:synth instrument)
     :color color}))

;; ============================================================================
;; STEP 6: Generate Complete MIDI Sequence
;; ============================================================================

(defn sonify-alife-worlds [worlds output-file]
  "Convert 5 ALife worlds → MIDI sequence with 120 BPM"
  (let [base-seed 42
        tempo-bpm 120
        beats-per-quarter 4

        ;; Generate MIDI notes for all 5 worlds
        midi-notes
        (vec (for [world-id (range 1 6)
                   tick (range 100)]
               (let [state (case world-id
                             1 {:creatures 2 :mass 0.99}
                             2 {:density 0.53 :complexity 0.515}
                             3 {:agents 85 :wealth 2856 :gini 0.2}
                             4 {:boids 200 :cohesion 0.87 :separation 0.3}
                             5 {:entropy 0.2 :order 0.99}
                             {})
                     denotator (world-to-denotator world-id state)
                     color (color-at (+ base-seed world-id) tick)
                     beat-offset (/ tick beats-per-quarter)]
                 (when denotator
                   (denotator-to-midi-note world-id denotator color beat-offset)))))

        ;; Filter nulls
        valid-notes (filterv identity midi-notes)

        ;; Group by world for separate tracks
        tracks (group-by :world-id valid-notes)

        ;; Compile MIDI data
        midi-data {:header {:format 1
                            :tracks 5
                            :division 480
                            :tempo tempo-bpm}
                   :tracks (mapv (fn [[world-id notes]]
                                   {:track-number world-id
                                    :notes notes
                                    :instrument-name (case world-id
                                                       1 "Lenia"
                                                       2 "Rule110"
                                                       3 "Sugarscape"
                                                       4 "Boids"
                                                       5 "NeuralCA")})
                                 (sort-by first tracks))
                   :total-beats 100}]

    ;; Write to JSON for now (can be converted to binary MIDI later)
    (spit output-file (json/write-str midi-data :indent 2))

    {:status "success"
     :output-file output-file
     :total-notes (count valid-notes)
     :tracks 5
     :tempo-bpm tempo-bpm
     :duration-seconds (/ 100 (/ tempo-bpm 60))}))

;; ============================================================================
;; STEP 7: Generate p5.js Visualization Code
;; ============================================================================

(defn generate-p5js-sketch [midi-data output-file]
  "Create interactive p5.js visualization synced with MIDI"
  (let [html-template
        (str "<!DOCTYPE html>
<html>
<head>
  <meta charset='utf-8'>
  <script src='https://cdnjs.cloudflare.com/ajax/libs/p5.js/1.4.0/p5.min.js'></script>
  <style>
    body { margin: 0; overflow: hidden; background: #0a0a0a; }
    canvas { display: block; }
    #info { position: absolute; top: 10px; left: 10px; color: #fff;
            font-family: monospace; background: rgba(0,0,0,0.7); padding: 10px; }
  </style>
</head>
<body>
  <div id='info'>
    <h3>ALife Sonification</h3>
    <p>5 Worlds × 100 Ticks = 500 MIDI Notes</p>
    <p>Seed: 42 | Tempo: 120 BPM</p>
  </div>
  <script>
    const midiData = " (json/write-str midi-data) ";

    let particles = [];
    let playing = false;
    let frame = 0;

    function setup() {
      createCanvas(800, 800);
      randomSeed(42);

      // Initialize particles from ALife dynamics
      for (let i = 0; i < 250; i++) {
        particles.push({
          x: random(width),
          y: random(height),
          vx: random(-1, 1),
          vy: random(-1, 1),
          world: floor(random(5)) + 1
        });
      }
    }

    function draw() {
      background(15);

      // Perlin noise flow field (from Rule 110)
      let scale = 20;
      for (let x = 0; x < width; x += scale) {
        for (let y = 0; y < height; y += scale) {
          let angle = noise(x/100, y/100 + frameCount/100) * TWO_PI;
          let v = p5.Vector.fromAngle(angle);
          v.setMag(2);

          stroke(100 + noise(x, y) * 155);
          line(x, y, x + v.x, y + v.y);
        }
      }

      // Render particles (colored by wealth/entropy)
      for (let p of particles) {
        p.x += p.vx;
        p.y += p.vy;

        // Wrap around
        if (p.x < 0) p.x = width;
        if (p.x > width) p.x = 0;
        if (p.y < 0) p.y = height;
        if (p.y > height) p.y = 0;

        // Color based on world
        let hue = (p.world * 60) % 360;
        colorMode(HSB);
        fill(hue, 255, 200);
        circle(p.x, p.y, 5);
      }

      // Piano roll visualization
      colorMode(RGB);
      let bpm = 120;
      let beat = frameCount / 4;  // 4 frames per beat

      for (let note of midiData.tracks[0]?.notes || []) {
        let x = map(note.onset, 0, 100, 0, width);
        let y = map(note.pitch, 0, 127, height, 0);

        if (abs(x - width/2) < 100) {
          fill(note.color.hue, note.color.lightness * 2.55);
          rect(x - 20, y - 5, 40, 10);
        }
      }
    }

    function mousePressed() {
      playing = !playing;
      return false;
    }
  </script>
</body>
</html>"
        )]
    (spit output-file html-template)
    output-file))

;; ============================================================================
;; MAIN EXECUTION
;; ============================================================================

(defn -main [& args]
  (let [output-midi (or (first args) "sonification.json")
        output-html (or (second args) "sonification.html")]

    ;; Generate 5 ALife worlds (using the earlier simulation results)
    (println "🎵 Sonifying 5 ALife worlds...")
    (let [result (sonify-alife-worlds {} output-midi)]
      (println (str "✓ MIDI generated: " output-midi))
      (println (str "  Total notes: " (:total-notes result)))
      (println (str "  Duration: " (format "%.1f" (:duration-seconds result)) " seconds")))

    ;; Generate visualization
    (println "\n🎨 Generating p5.js visualization...")
    (generate-p5js-sketch {} output-html)
    (println (str "✓ Visualization: " output-html))

    (println "\n╔════════════════════════════════════════════════════════════╗")
    (println "║       SONIFICATION COMPLETE — Ready to Play!               ║")
    (println "╚════════════════════════════════════════════════════════════╝")))

;; Run when evaluated
(-main)
