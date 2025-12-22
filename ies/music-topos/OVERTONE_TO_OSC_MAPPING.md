# Overtone Patterns → Pure OSC Implementation

## Overview
The cloned Overtone examples (in ~/worlds/o) demonstrate sophisticated music composition patterns. This document maps those patterns to our pure OSC implementation, showing how to achieve the same musical results without the Overtone library dependency that fails on ARM64 macOS.

---

## Pattern 1: High-Level Abstraction (overtone.live)

### Overtone Approach
```clojure
(ns my-music (:use [overtone.live]))

(defsynth sine [freq 440 dur 1]
  (let [env (env-gen (perc 0.01 dur) :action FREE)]
    (out 0 (* env (sin-osc freq)))))

(sine 60)  ;; Just call the synth like a function!
```

**What overtone.live provides:**
- `defsynth`: Define synths and get callable functions
- `env-gen`, `perc`: Envelope generators
- `sin-osc`: Sine oscillator
- `out`: Route to output
- `FREE`: Automatic cleanup
- Connection to SuperCollider is automatic
- Server booting is automatic

### Pure OSC Approach
```clojure
(ns my-music (:require [overtone.osc :as osc]))

;; Manual connection
(def client (osc/osc-client "127.0.0.1" 57110))

;; Manual synth definition via SynthDef (needs to be in startup.scd)
;; SynthDef("sine", {|freq=440, amp=0.3, sustain=1|
;;   var env = EnvGen.kr(Env([0,1,1,0], [0.01, sustain, 0.01], 'lin'), doneAction: Done.freeSelf);
;;   Out.ar(0, env * 0.3 * SinOsc.ar(freq));
;; }).send(Server.local);

;; Manual synth invocation
(defn sine [freq dur]
  (let [node-id (next-node-id)]
    (osc/osc-send client "/s_new" "sine" node-id 1 0
                  "freq" (double freq)
                  "sustain" (double dur))))

(sine 60 1)  ;; Call the function, it sends OSC message
```

**Tradeoffs:**
- ✓ No native dependencies (works on ARM64)
- ✓ Full control over every OSC message
- ✓ Explicit connection management
- ✗ More verbose
- ✗ Must manage SynthDef separately (startup.scd)

---

## Pattern 2: Scheduling with Metronome

### Overtone Approach
```clojure
(def metro (metronome 120))  ;; 120 BPM

(dorun (map-indexed
  #(at (metro (+ (metro) %)) (sine (+ 60 %2)))
  [0 2 7 12]))  ;; Play notes at metronome ticks
```

**What happens:**
- `metronome`: Creates a global timestamp function
- `metro`: Returns current beat number
- `at`: Schedules synth for a specific future beat
- Beats are automatically converted to milliseconds

### Pure OSC Approach
```clojure
(def bpm 120)
(def beat-duration-ms (/ 60000.0 bpm))  ;; 500ms per beat at 120 BPM

(defn schedule-at-beat [beat-number sync-function]
  "Calculate when to send OSC message based on beat number"
  (let [beat-time (+ (current-time-ms) (* beat-number beat-duration-ms))]
    beat-time))

(defn now-beats [metro-atom]
  (/ (current-time-ms) beat-duration-ms))

;; Manual scheduling with Thread/sleep
(doseq [[i interval] (map-indexed (fn [i x] [i x]) [0 2 7 12])]
  (let [beat-time (schedule-at-beat i)]
    (future (Thread/sleep (- beat-time (current-time-ms)))
            (sine (+ 60 interval) 1))))
```

**Tradeoffs:**
- ✓ Precise timing control
- ✓ No dependency on Overtone's metronome
- ✗ Must manually calculate beat times
- ✗ Thread/sleep is less accurate than Overtone's native scheduling

**Better approach: Use at-at library**
```clojure
;; Add to project.clj: [overtone/at-at "1.1.1"]
(ns my-music (:require [overtone.at-at :as at-at]))

(def pool (at-at/mk-pool))
(at-at/every beat-duration-ms
  (fn [beat-num] (sine (+ 60 (nth [0 2 7 12] (mod beat-num 4))) 1))
  pool)
```

---

## Pattern 3: Separating Music Concerns

### Overtone Approach (from ex01_phrasestudy.clj)
```clojure
;; Concern 1: Pattern definition (pure data)
(def a [0 2 7 12])     ;; Major arpeggio
(def b [0 2 6 12])     ;; Minor arpeggio

;; Concern 2: Pattern transformation (pure functions)
(defn repeat-phrases [n offset & phrases]
  (->> phrases (repeat n) (flatten)
       (map (partial + (if (keyword? offset) (note offset) offset)))))

;; Concern 3: Playback (has side effects)
(defn play-phrases [metro inst dur offset n & phrases]
  (let [notes (apply repeat-phrases n offset phrases)
        play (partial play-note-at metro (metro))]
    (->> notes
         (map-indexed #(play % dur inst %2))
         (dorun))))

(play-phrases metro piano 1/16 :c4 2 a a b b)
```

### Pure OSC Approach (Music Topos style)
```clojure
;; Concern 1: Music specification (pure data)
(def initial-world
  {:pitch-classes (range 60 72)
   :harmonic-functions
   [{:name "Tonic" :chord [60 64 67]}
    {:name "Subdominant" :chord [65 69 72]}
    {:name "Dominant" :chord [67 71 74]}]})

;; Concern 2: OSC message generation (pure functions)
(defn notes->osc-messages [notes start-beat bpm]
  "Convert music notes to OSC commands with timing"
  (let [beat-duration-ms (/ 60000.0 bpm)]
    (map-indexed
      (fn [i note]
        {:path "/s_new"
         :args ["sine" (+ 1000 i) 1 0
                "freq" (double note)
                "sustain" 0.5]
         :time-ms (+ (* start-beat beat-duration-ms)
                      (* i beat-duration-ms))})
      notes)))

;; Concern 3: Playback (has side effects)
(defn play-osc-messages [client messages]
  "Send OSC messages at scheduled times"
  (doseq [{:keys [path args time-ms]} messages]
    (future
      (let [sleep-time (- time-ms (current-time-ms))]
        (when (> sleep-time 0)
          (Thread/sleep sleep-time))
        (apply osc/osc-send client path args)))))

;; Usage:
(let [notes [60 62 67 72]
      osc-cmds (notes->osc-messages notes 0 120)]
  (play-osc-messages client osc-cmds))
```

**Architecture:**
- Pure data layer: untouched by side effects
- Pure transformation layer: notes → OSC messages
- Effect layer: send OSC at correct times

This IS the Hickey principle applied to audio!

---

## Pattern 4: Instrument Definition

### Overtone Approach
```clojure
(definst fatso-saw [note 60 dur 1.0 amp 1.0]
  (let [freq (midicps note)
        src (saw [freq (* freq 0.51)])
        env (env-gen (perc (* 0.1 dur) dur amp) :action FREE)]
    (* src env)))

(fatso-saw 60 0.5)  ;; Invoke with parameters
```

### Pure OSC Approach
```clojure
;; Option 1: Pre-define synths in startup.scd
(def instrument-specs
  {:fatso-saw
   {:synthdef-name "fatso-saw"
    :parameters [:note :dur :amp]
    :defaults [60 1.0 1.0]
    :supercollider-code
    "SynthDef('fatso-saw', {|note=60, dur=1.0, amp=1.0|
      var freq = note.midicps;
      var src = Saw.ar([freq, freq * 0.51]);
      var env = EnvGen.kr(Perc(dur * 0.1, dur, amp), doneAction: Done.freeSelf);
      Out.ar(0, src * env);
    }).send(Server.local);"}})

;; Option 2: Create instruments dynamically
(defn fatso-saw [note dur amp]
  (let [node-id (next-node-id)]
    (osc/osc-send client "/s_new" "fatso-saw" node-id 1 0
                  "note" (double note)
                  "dur" (double dur)
                  "amp" (double amp))))

(fatso-saw 60 0.5 1.0)
```

---

## Pattern 5: Rhythm and Temporal Composition

### Overtone Approach
```clojure
(def rhythm [3/8 1/8 1/8])  ;; Durations in quarter notes

(defn rhythmic-phrase [rhythm factor phrase]
  (->> rhythm
       (cycle)
       (take (count phrase))
       (reductions (fn[t d] (+ t (* d factor 4))) 0)
       (map (fn [n t] [n t]) phrase)))

;; Returns: ([60 0] [62 1.5] [67 3.0] ...)
(rhythmic-phrase rhythm 1 [60 62 67])
```

### Pure OSC Approach
```clojure
(defn rhythm-timings [rhythm beat-duration-ms phrase]
  "Convert rhythm pattern and phrase to absolute timings"
  (let [notes phrase
        durations rhythm
        cumulative-beats (reductions + 0 (repeat (count notes) 1))
        beat-times (map #(* % beat-duration-ms) cumulative-beats)]
    (map (fn [note beat-time]
           {:note note :time-ms beat-time})
         notes beat-times)))

;; More Clojure-idiomatic
(def rhythm [3/8 1/8 1/8])
(def phrase [60 62 67])
(def bpm 120)

(defn render-rhythm [bpm rhythm phrase]
  (let [beat-ms (/ 60000.0 bpm)
        durations (take (count phrase) (cycle rhythm))
        beat-offsets (reductions + 0 durations)]
    (map (fn [note offset]
           {:note note :time-ms (* offset beat-ms)})
         phrase beat-offsets)))

(render-rhythm 120 [3/8 1/8 1/8] [60 62 67])
```

---

## Direct Translation: InitialObjectWorld → Pure OSC

### Our Music Topos Structure
```clojure
(def initial-world
  {:pitch-classes (range 60 72)
   :harmonic-functions
   [{:name "Tonic" :chord [60 64 67]}
    {:name "Subdominant" :chord [65 69 72]}
    {:name "Dominant" :chord [67 71 74]}]
   :modulation-keys [0 7 2 5]})
```

### Transformation Pipeline (Pure)
```clojure
;; Stage 1: World spec → Music notes
(defn world->notes [world]
  (let [initial [(-> world :pitch-classes first)]
        pitch-classes (:pitch-classes world)
        harmonics (mapcat :chord (:harmonic-functions world))
        modulation (map #(+ 60 %) (:modulation-keys world))]
    (concat initial pitch-classes harmonics modulation)))

;; Stage 2: Notes → OSC messages
(defn notes->osc-bundle [notes bpm start-time-ms]
  (let [beat-ms (/ 60000.0 bpm)]
    (map-indexed
      (fn [i note]
        {:path "/s_new"
         :args ["sine" (+ 2000 i) 1 0 "freq" (double note) "sustain" 0.5]
         :time-ms (+ start-time-ms (* i beat-ms))})
      notes)))

;; Stage 3: OSC messages → Network transmission (Has effects)
(defn send-osc-bundle [client messages]
  (doseq [{:keys [path args time-ms]} messages]
    (schedule-at-time time-ms #(apply osc/osc-send client path args))))

;; Complete pipeline
(let [notes (world->notes initial-world)
      messages (notes->osc-bundle notes 120 (current-time-ms))]
  (send-osc-bundle client messages))
```

---

## Summary: Overtone is a Wrapper, Not Magic

**What Overtone does:**
1. Wraps JNA calls to SuperCollider's internal server
2. Provides syntactic sugar (defsynth, definst, at, etc.)
3. Handles metronome and scheduling
4. Manages connection lifecycle

**What pure OSC does:**
1. Sends OSC messages directly via UDP
2. Requires explicit SynthDef definitions
3. Requires manual scheduling
4. Requires explicit connection management

**For Music Topos on ARM64:**
- We use pure OSC + at-at library for scheduling
- SynthDefs defined in startup.scd
- Same musical results, different implementation
- More transparent, fewer dependencies
- Fully compatible with "in perpetuity" requirement

**Files needed:**
1. `project.clj`: Clojure dependencies (osc-clj, at-at)
2. `startup.scd`: SuperCollider synth definitions
3. `core.clj`: Our pure OSC music implementation
4. `music_topos/worlds.clj`: Music specifications (untouched data)
5. `tests/`: Pure function tests (no audio hardware needed)
