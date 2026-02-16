;;; asi/core.hy
;;; Algebraic Superintelligence - Core module in Hy
;;;
;;; GF(3) Conservation Law:
;;;   inject(+1) + bridge(0) + emit(-1) ≡ 0 (mod 3)

(import pathlib [Path])
(import rich.console [Console])
(import rich.table [Table])
(import rich.panel [Panel])
(import rich.text [Text])

;; ═══════════════════════════════════════════════════════════════════════════════
;; GF(3) CONSTANTS
;; ═══════════════════════════════════════════════════════════════════════════════

(setv PLUS 1)       ; Generation, synthesis, forward
(setv ERGODIC 0)    ; Coordination, balance, transport  
(setv MINUS -1)     ; Verification, validation, backward

(setv CANONICAL-SEED 1069)  ; Same seed → same colors (Gay.jl)

(setv TRIT-SYMBOLS {1 "+" 0 "○" -1 "−"})
(setv TRIT-COLORS {1 "green" 0 "cyan" -1 "magenta"})
(setv TRIT-NAMES {1 "PLUS" 0 "ERGODIC" -1 "MINUS"})

;; ═══════════════════════════════════════════════════════════════════════════════
;; SPI COLOR GENERATION (matches Gay.jl SplitMix64)
;; ═══════════════════════════════════════════════════════════════════════════════

(defn splitmix32-next [state]
  "Advance PRNG state (simplified for Python compatibility)"
  (setv a 1103515245)
  (setv c 12345)
  (setv m (** 2 31))
  (setv state-prime (% (+ (* a (% state m)) c) m))
  #(state-prime state-prime))

(defn color-at [seed index]
  "Get deterministic LCH color from seed and index"
  (setv state (abs seed))
  (for [_ (range (+ index 1))]
    (setv #(state _) (splitmix32-next state)))
  
  (setv max-val 2147483647.0)
  
  ;; L component
  (setv #(state z1) (splitmix32-next state))
  (setv L (+ 10.0 (* (/ z1 max-val) 85.0)))
  
  ;; C component  
  (setv #(state z2) (splitmix32-next state))
  (setv C (* (/ z2 max-val) 100.0))
  
  ;; H component
  (setv #(state z3) (splitmix32-next state))
  (setv H (* (/ z3 max-val) 360.0))
  
  {"L" L "C" C "H" H "index" index "seed" seed})

(defn hue->polarity [hue]
  "Map hue to Girard polarity"
  (cond
    (or (< hue 60) (>= hue 300)) "positive"
    (and (>= hue 180) (< hue 300)) "negative"
    True "neutral"))

(defn polarity->trit [polarity]
  "Convert polarity to GF(3) trit"
  (get {"positive" 1 "neutral" 0 "negative" -1} polarity 0))

;; ═══════════════════════════════════════════════════════════════════════════════
;; SKILL LOADING
;; ═══════════════════════════════════════════════════════════════════════════════

(defn get-asi-root []
  "Get ASI root directory"
  (.parent (.parent (.parent (Path __file__)))))

(defn get-skills-dir []
  "Get skills directory path"
  (/ (get-asi-root) "skills"))

(defn load-skills []
  "Load all skills from the skills directory"
  (setv skills-dir (get-skills-dir))
  (setv skills [])
  
  (when (.exists skills-dir)
    (for [#(i skill-dir) (enumerate (sorted (.iterdir skills-dir)))]
      (when (and (.is-dir skill-dir) 
                 (not (.startswith skill-dir.name ".")))
        (setv skill {"name" skill-dir.name
                     "path" (str skill-dir)
                     "index" i
                     "trit" 0
                     "description" ""})
        
        ;; Try to read manifest.toml
        (setv manifest (/ skill-dir "manifest.toml"))
        (when (.exists manifest)
          (try
            (import tomllib)
            (with [f (open manifest "rb")]
              (setv data (tomllib.load f))
              (setv (get skill "trit") (.get data "trit" 0))
              (setv (get skill "description") (.get data "description" "")))
            (except [e Exception]
              None)))
        
        (.append skills skill))))
  
  skills)

;; ═══════════════════════════════════════════════════════════════════════════════
;; GF(3) ANALYSIS
;; ═══════════════════════════════════════════════════════════════════════════════

(defn gf3-balance [skills]
  "Calculate GF(3) balance for a list of skills"
  (setv plus-count (len (lfor s skills :if (= (.get s "trit" 0) 1) s)))
  (setv ergodic-count (len (lfor s skills :if (= (.get s "trit" 0) 0) s)))
  (setv minus-count (len (lfor s skills :if (= (.get s "trit" 0) -1) s)))
  (setv total (- plus-count minus-count))
  (setv conserved (= 0 (% total 3)))
  
  {"plus" plus-count
   "ergodic" ergodic-count
   "minus" minus-count
   "sum" total
   "mod3" (% total 3)
   "conserved" conserved})

(defn verify-triplet [a b c]
  "Verify a triplet conserves GF(3)"
  (setv sum (+ a b c))
  {"trits" #(a b c)
   "sum" sum
   "conserved" (= 0 (% sum 3))})

;; ═══════════════════════════════════════════════════════════════════════════════
;; TAP CONTROL
;; ═══════════════════════════════════════════════════════════════════════════════

(setv TAP-BACKFILL -1)  ; Historical sync
(setv TAP-VERIFY 0)     ; Self-check (BEAVER)
(setv TAP-LIVE 1)       ; Forward sync

(defn tap->prime [tap-state]
  "Map TAP state to prime (multiplicative structure)"
  (get {-1 2 0 3 1 5} tap-state 3))

(defn tap->girard [tap-state]
  "Map TAP state to Girard polarity"
  (get {-1 "negative" 0 "neutral" 1 "positive"} tap-state "neutral"))

;; ═══════════════════════════════════════════════════════════════════════════════
;; DISPLAY HELPERS
;; ═══════════════════════════════════════════════════════════════════════════════

(defn trit-symbol [trit]
  "Get symbol for trit value with color"
  (setv sym (.get TRIT-SYMBOLS trit "?"))
  (setv color (.get TRIT-COLORS trit "white"))
  (+ "[" color "]" sym "[/]"))

(defn format-gf3-status [balance]
  "Format GF(3) balance as rich text"
  (setv conserved-sym (if (get balance "conserved") "[green]✓[/]" "[red]✗[/]"))
  (+ "[green]+" (str (get balance "plus")) "[/] | "
     "[cyan]○" (str (get balance "ergodic")) "[/] | "
     "[magenta]−" (str (get balance "minus")) "[/] = "
     (str (get balance "sum")) " ≡ " (str (get balance "mod3")) " (mod 3) "
     conserved-sym))
