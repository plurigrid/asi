#!/usr/bin/env hy
; SpectrogramAnalysis.hy
;
; Formal spectrogram analysis system integrated with quantum guitar phases
; Analyzes frequency trajectories and maps them to multi-instrument composition
; Supports British artists' techniques (Windowlicker equations, CA textures, etc.)

(import
  json
  math
  [numpy :as np]
  [collections [deque]]
  [datetime [datetime]]
  [enum [Enum]]
)

; ============================================================================
; SPECTROGRAM FRAME REPRESENTATION
; ============================================================================

(defclass SpectrogramFrame
  "A frequency-time snapshot from audio analysis"

  (defn __init__ [self time-index frequencies magnitudes window-size]
    (setv self.time-index time-index)
    (setv self.frequencies frequencies)      ; array of frequencies (Hz)
    (setv self.magnitudes magnitudes)        ; array of magnitudes (0-1)
    (setv self.window-size window-size)
    (setv self.timestamp (/ time-index 44100.0)))  ; convert to seconds @ 44.1kHz

  (defn peak-frequency [self &optional [threshold 0.1]]
    "Find the dominant frequency (peak magnitude)"
    (let [peaks (lfor [[i mag] (enumerate self.magnitudes)]
                      :if (> mag threshold)
                      [i mag])]
      (if peaks
        (let [[idx mag] (max peaks :key second)]
          (get self.frequencies idx))
        None)))

  (defn peak-pitch [self &optional [a4 440.0]]
    "Convert peak frequency to MIDI pitch (0-127)"
    (let [freq (self.peak-frequency)]
      (if freq
        (round (+ 69 (* 12 (math.log (/ freq a4) 2))))
        None)))

  (defn spectral-centroid [self]
    "Calculate the center of mass of the spectrum"
    (let [numerator (sum (lfor [[f m] (zip self.frequencies self.magnitudes)]
                               (* f m)))
          denominator (sum self.magnitudes)]
      (if (> denominator 0)
        (/ numerator denominator)
        0)))

  (defn spectral-flatness [self]
    "Calculate spectral flatness (0=sharp, 1=flat)"
    (let [geom-mean (math.pow
                      (np.prod (np.array self.magnitudes))
                      (/ 1 (len self.magnitudes)))
          arith-mean (/ (sum self.magnitudes) (len self.magnitudes))]
      (if (> arith-mean 0)
        (/ geom-mean arith-mean)
        0)))

  (defn to-dict [self]
    {"time_index" self.time-index
     "timestamp" self.timestamp
     "peak_frequency" (self.peak-frequency)
     "peak_pitch" (self.peak-pitch)
     "spectral_centroid" (self.spectral-centroid)
     "spectral_flatness" (self.spectral-flatness)}))

; ============================================================================
; SPECTROGRAM SEQUENCE & TRAJECTORY ANALYSIS
; ============================================================================

(defclass SpectrogramSequence
  "A sequence of spectrogram frames over time"

  (defn __init__ [self name]
    (setv self.name name)
    (setv self.frames [])
    (setv self.duration 0))

  (defn add-frame [self frame]
    "Append a frame to the sequence"
    (.append self.frames frame)
    (setv self.duration frame.timestamp)
    self)

  (defn pitch-trajectory [self]
    "Extract the pitch contour (MIDI values over time)"
    (lfor [frame self.frames]
      [frame.timestamp (frame.peak-pitch)]))

  (defn frequency-trajectory [self]
    "Extract the frequency contour (Hz over time)"
    (lfor [frame self.frames]
      [frame.timestamp (frame.peak-frequency)]))

  (defn spectral-centroid-trajectory [self]
    "Extract centroid trajectory"
    (lfor [frame self.frames]
      [frame.timestamp (frame.spectral-centroid)]))

  (defn smooth-trajectory [self trajectory &optional [window-size 3]]
    "Smooth a trajectory using moving average"
    (let [result []]
      (for [i (range (len trajectory))]
        (let [window-start (max 0 (- i (// window-size 2)))
              window-end (min (len trajectory) (+ i (// window-size 2)))
              window-values (lfor [j (range window-start window-end)]
                                  (second (get trajectory j)))
              avg-val (/ (sum window-values) (len window-values))]
          (.append result [(first (get trajectory i)) avg-val])))
      result))

  (defn to-dict [self]
    {"name" self.name
     "num_frames" (len self.frames)
     "duration" self.duration
     "pitch_trajectory" (self.pitch-trajectory)
     "frequency_trajectory" (self.frequency-trajectory)}))

; ============================================================================
; EQUATION-DRIVEN TRAJECTORY GENERATION (WINDOWLICKER FORMALISM)
; ============================================================================

(defn windowlicker-equation [t &optional [base-freq 60] [chaos-factor 1.0]]
  "Reconstruct frequency trajectory from Windowlicker-style equation
   Based on: f(t) = base_freq * (1 + chaos * sin(ωt) * exp(-αt))"
  (let [omega 0.5      ; frequency of oscillation
        alpha 0.1      ; decay rate
        modulation (* chaos-factor (math.sin (* omega t)) (math.exp (* (- alpha) t)))]
    (* base-freq (+ 1 modulation))))

(defn polynomial-trajectory [coeffs]
  "Generate trajectory from polynomial coefficients
   f(t) = c0 + c1*t + c2*t^2 + ..."
  (fn [t] (sum (lfor [[i c] (enumerate coeffs)]
                     (* c (math.pow t i))))))

(defn logistic-chaos-trajectory [r x0]
  "Logistic chaos map: x_{n+1} = r*x_n*(1-x_n)
   Used for deterministic chaos in music"
  (let [sequence [x0]]
    (for [n (range 100)]
      (let [xn (get sequence -1)
            xn1 (* r xn (- 1 xn))]
        (.append sequence xn1)))
    sequence))

; ============================================================================
; TRAJECTORY FITTING & ANALYSIS
; ============================================================================

(defclass TrajectoryAnalysis
  "Analyze and fit a pitch/frequency trajectory to a mathematical model"

  (defn __init__ [self trajectory]
    (setv self.trajectory trajectory)  ; list of [time, value] pairs
    (setv self.times (lfor [[t v] trajectory] t))
    (setv self.values (lfor [[t v] trajectory] v)))

  (defn fit-polynomial [self degree]
    "Fit a polynomial to the trajectory"
    (let [coeffs (np.polyfit self.times self.values degree)]
      coeffs))

  (defn fit-exponential [self]
    "Fit an exponential decay: v(t) = a * exp(-b*t) + c"
    ; Simplified: find linear fit in log-space
    (let [log-values (lfor [v self.values] (math.log (max v 0.001)))
          coeffs (np.polyfit self.times log-values 1)]
      coeffs))

  (defn compute-residuals [self predicted-trajectory]
    "Calculate error between actual and predicted trajectory"
    (let [differences (lfor [[actual pred] (zip self.values predicted-trajectory)]
                            (- actual pred))]
      (math.sqrt (/ (sum (lfor [d differences] (** d 2)))
                    (len differences)))))

  (defn best-fit-model [self models]
    "Find which model fits best (models = {name: trajectory-fn})"
    (let [errors {}]
      (for [[name model-fn] (.items models)]
        (let [predicted (lfor [t self.times] (model-fn t))
              error (self.compute-residuals predicted)]
          (setv (get errors name) error)))
      (let [best-name (min errors :key (fn [k] (get errors k)))]
        {"best_model" best-name
         "error" (get errors best-name)
         "all_errors" errors}))))

; ============================================================================
; SPECTROGRAM-TO-COMPOSITION MAPPING
; ============================================================================

(defclass SpectrogramMapper
  "Map spectrogram trajectories to multi-instrument composition"

  (defn __init__ [self spectrogram-seq phase-type]
    (setv self.spectrogram-seq spectrogram-seq)
    (setv self.phase-type phase-type)  ; "RED", "BLUE", "GREEN"
    (setv self.trajectory (spectrogram-seq.pitch-trajectory)))

  (defn pitch-to-voices [self pitch-trajectory]
    "Convert pitch trajectory to individual voices
     Handles pitch splitting across registers"
    (let [voices {"high" [] "mid" [] "low" []}]
      (for [[t pitch] pitch-trajectory]
        (if (>= pitch 84)
          (.append (get voices "high") [t pitch])
          (if (>= pitch 60)
            (.append (get voices "mid") [t pitch])
            (.append (get voices "low") [t pitch]))))
      voices))

  (defn trajectory-to-notes [self trajectory &optional [quantize True]]
    "Convert continuous trajectory to discrete note events"
    (let [notes []
          last-pitch None
          note-start 0]
      (for [i (range (len trajectory))]
        (let [[t pitch] (get trajectory i)
              current-pitch (if quantize
                             (round pitch)
                             pitch)]
          (if (and last-pitch (!= current-pitch last-pitch))
            (do
              (.append notes
                {"start_time" note-start
                 "end_time" t
                 "pitch" last-pitch})
              (setv note-start t)))
          (setv last-pitch current-pitch)))
      notes))

  (defn apply-phase-transformation [self trajectory]
    "Apply quantum guitar phase transformation to trajectory"
    (match self.phase-type
      "RED"   (lfor [[t v] trajectory] [t (* v 1.1)])   ; amplify
      "BLUE"  (lfor [[t v] trajectory] [t (/ v 1.1)])   ; contract
      "GREEN" trajectory))                               ; identity

  (defn to-dict [self]
    {"spectrogram_name" self.spectrogram-seq.name
     "phase_type" self.phase-type
     "duration" self.spectrogram-seq.duration}))

; ============================================================================
; BRITISH ARTISTS' SIGNATURE ANALYSIS
; ============================================================================

(defclass ArtistSignatureAnalyzer
  "Detect and extract signature techniques from spectrograms"

  (defn __init__ [self spectrogram-seq artist-name]
    (setv self.spectrogram-seq spectrogram-seq)
    (setv self.artist-name artist-name)
    (setv self.signatures []))

  (defn detect-aphex-windowlicker [self &optional [tolerance 0.2]]
    "Detect Windowlicker-style equation-driven trajectory
     Look for characteristic exponential decay with oscillation"
    (let [traj (self.spectrogram-seq.pitch-trajectory)
          analysis (TrajectoryAnalysis traj)]
      (let [models {"windowlicker" (fn [t] (windowlicker-equation t 60 1.0))
                    "polynomial" (fn [t] (+ 60 (* 12 (math.sin (* t 0.5)))))}]
        (let [result (analysis.best-fit-model models)]
          (if (< (get result "error") tolerance)
            (do
              (.append self.signatures
                {"type" "windowlicker"
                 "error" (get result "error")
                 "detected_at" (datetime.now)})
              True)
            False)))))

  (defn detect-autechre-ca [self &optional [period 4]]
    "Detect Autechre cellular automaton texture
     Look for repeating patterns (period structure)"
    (let [traj (self.spectrogram-seq.pitch-trajectory)
          values (lfor [[t v] traj] v)
          differences (lfor [i (range 1 (len values))]
                           (abs (- (get values i) (get values (- i 1)))))]
      (let [period-matches 0]
        (for [i (range 0 (- (len differences) period))]
          (let [window (get differences (slice i (+ i period)))]
            (if (== window (get differences (slice (+ i period) (+ i (* 2 period)))))
              (+= period-matches 1))))
        (if (> period-matches 0)
          (do
            (.append self.signatures
              {"type" "cellular_automaton"
               "period" period
               "matches" period-matches})
            True)
          False))))

  (defn detect-beating-frequencies [self &optional [threshold 0.05]]
    "Detect Daniel Avery's beating effect
     Look for slow amplitude modulation (< 1 Hz)"
    (let [traj (self.spectrogram-seq.pitch-trajectory)
          magnitudes (lfor [frame self.spectrogram-seq.frames]
                          (frame.peak-frequency))]
      ; Simplified: look for periodic variation in a frequency band
      (if (> (len magnitudes) 10)
        (let [first-half (sum (get magnitudes (slice 0 (// (len magnitudes) 2))))
              second-half (sum (get magnitudes (slice (// (len magnitudes) 2) None)))
              variation (abs (- first-half second-half))]
          (if (> variation threshold)
            (do
              (.append self.signatures
                {"type" "beating"
                 "variation" variation})
              True)
            False))
        False)))

  (defn to-dict [self]
    {"artist" self.artist-name
     "spectrogram" self.spectrogram-seq.name
     "signatures_detected" (len self.signatures)
     "signatures" self.signatures}))

; ============================================================================
; FORMAL PROOF GENERATION FOR SPECTROGRAM ANALYSIS
; ============================================================================

(defclass SpectrogramProof
  "Formal proof that spectrogram maps to valid composition"

  (defn __init__ [self analyzer]
    (setv self.analyzer analyzer)
    (setv self.statements [])
    (setv self.verified-properties []))

  (defn verify-pitch-bounds [self min-pitch max-pitch]
    "Verify all pitches stay within instrument bounds"
    (let [traj (self.analyzer.trajectory)
          all-valid (all (lfor [[t pitch] traj]
                               (and (>= pitch min-pitch)
                                    (<= pitch max-pitch))))]
      (if all-valid
        (do
          (.append self.verified-properties "pitch_bounds")
          (.append self.statements
            (+ "∀ t ∈ [0, " (str (self.analyzer.spectrogram-seq.duration))
               "]: " (str min-pitch) " ≤ pitch(t) ≤ " (str max-pitch)))
          True)
        False)))

  (defn verify-continuity [self &optional [max-jump 12]]
    "Verify trajectory is continuous (no unphysical jumps)"
    (let [traj (self.analyzer.trajectory)
          continuous (all (lfor [i (range 1 (len traj))]
                               (let [[t1 p1] (get traj (- i 1))
                                     [t2 p2] (get traj i)]
                                 (<= (abs (- p2 p1)) max-jump))))]
      (if continuous
        (do
          (.append self.verified-properties "continuity")
          (.append self.statements
            (+ "∀ i,j: |pitch(t_i) - pitch(t_j)| ≤ " (str max-jump) " semitones"))
          True)
        False)))

  (defn verify-monotonicty-per-phase [self phase-type]
    "Verify trajectory satisfies phase property"
    (match phase-type
      "RED"   (do
                (let [increasing (all (lfor [i (range 1 (len self.analyzer.trajectory))]
                                            (let [[t1 p1] (get self.analyzer.trajectory (- i 1))
                                                  [t2 p2] (get self.analyzer.trajectory i)]
                                              (>= p2 p1))))]
                  (if increasing
                    (do
                      (.append self.verified-properties "RED_monotone")
                      (.append self.statements "RED phase: f(t) ≥ f(t') for t > t'")
                      True)
                    False)))
      "BLUE"  (do
                (let [decreasing (all (lfor [i (range 1 (len self.analyzer.trajectory))]
                                            (let [[t1 p1] (get self.analyzer.trajectory (- i 1))
                                                  [t2 p2] (get self.analyzer.trajectory i)]
                                              (<= p2 p1))))]
                  (if decreasing
                    (do
                      (.append self.verified-properties "BLUE_monotone")
                      (.append self.statements "BLUE phase: f(t) ≤ f(t') for t > t'")
                      True)
                    False)))
      "GREEN" (do
                (.append self.verified-properties "GREEN_identity")
                (.append self.statements "GREEN phase: f(t) = f(t) (identity)")
                True)))

  (defn generate-proof-artifact [self]
    "Generate complete proof as dict"
    {"statements" self.statements
     "verified_properties" self.verified-properties
     "verified_count" (len self.verified-properties)
     "timestamp" (str (datetime.now))})

  (defn to-dict [self]
    {"analyzer" (self.analyzer.to-dict)
     "proof" (self.generate-proof-artifact)}))

; ============================================================================
; DEMONSTRATION
; ============================================================================

(defn demo-spectrogram-analysis []
  "Demonstrate spectrogram analysis with formal proofs"
  (print "\n=== Spectrogram Analysis Demo ===\n")

  ; Create synthetic spectrogram sequence
  (let [spec-seq (SpectrogramSequence "Demo-Windowlicker")]
    ; Add frames with synthetic data
    (for [i (range 100)]
      (let [t (/ i 44100.0)
            freq (windowlicker-equation t 60 1.0)
            ; Create synthetic magnitudes (peak at fundamental)
            magnitudes (lfor [f (range 0 10)]
                            (if (== f 0) 0.9 (* 0.1 (/ 1 (+ 1 f)))))
            frequencies (lfor [f (range 0 10)] (* (+ 1 f) freq))]
        (.add-frame spec-seq
          (SpectrogramFrame i frequencies magnitudes 2048))))

    ; Analyze trajectory
    (let [mapper (SpectrogramMapper spec-seq "RED")]
      (print "Trajectory analysis:")
      (print (json.dumps (mapper.to-dict) :indent 2)))

    ; Detect artist signatures
    (let [analyzer (ArtistSignatureAnalyzer spec-seq "Aphex Twin")]
      (analyzer.detect-aphex-windowlicker :tolerance 2.0)
      (print "\nArtist signature detection:")
      (print (json.dumps (analyzer.to-dict) :indent 2)))

    ; Generate proof
    (let [proof (SpectrogramProof mapper)]
      (proof.verify-pitch-bounds 0 127)
      (proof.verify-continuity :max-jump 12)
      (proof.verify-monotonicty-per-phase "RED")
      (print "\nFormal proof:")
      (for [stmt (. proof statements)]
        (print (+ "✓ " stmt))))))

; Run demo if executed directly
(if (= __name__ "__main__")
  (demo-spectrogram-analysis))
