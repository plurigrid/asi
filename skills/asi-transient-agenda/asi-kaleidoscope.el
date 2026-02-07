;; ASI Kaleidoscope: Oscillating color-graded Emacs faces via Gay.jl
;; Mode-line = current color, header = complement, fringes = preceding/next

(require 'color)

;; ═══════════════════════════════════════════════════════════
;; Gay.jl 24-color genesis palette (seed=1069, indices 0-23)
;; ═══════════════════════════════════════════════════════════

(defvar asi-k--palette
  '("#769c7d" "#55b0e6" "#c8a0c2" "#ffa6c2" "#789a20" "#54c1ed"
    "#285dd0" "#6233ef" "#d4be57" "#389bc3" "#7278c0" "#5fa42b"
    "#c3f7fa" "#de1fbe" "#ec6698" "#b81660" "#49b0f2" "#50a9e3"
    "#6fc6f9" "#7d13cb" "#5fb501" "#636fa4" "#5b63de" "#58e0a8")
  "Gay.jl 24-color genesis palette from seed 1069.")

(defvar asi-k--index 0 "Current palette index.")
(defvar asi-k--timer nil "Kaleidoscope animation timer.")
(defvar asi-k--speed 0.8 "Seconds between color transitions.")
(defvar asi-k--running nil "Whether kaleidoscope is active.")

;; ═══════════════════════════════════════════════════════════
;; Color math: complement, darken, lighten
;; ═══════════════════════════════════════════════════════════

(defun asi-k--complement (hex)
  "Return polar opposite (180° hue rotation) of HEX color."
  (let* ((rgb (color-name-to-rgb hex))
         (hsl (apply #'color-rgb-to-hsl rgb))
         (h (car hsl))
         (s (cadr hsl))
         (l (caddr hsl))
         (new-h (mod (+ h 0.5) 1.0)))
    (apply #'color-rgb-to-hex (color-hsl-to-rgb new-h s l))))

(defun asi-k--darken (hex amount)
  "Darken HEX color by AMOUNT (0-1)."
  (let* ((rgb (color-name-to-rgb hex))
         (hsl (apply #'color-rgb-to-hsl rgb))
         (h (car hsl))
         (s (cadr hsl))
         (l (max 0.05 (- (caddr hsl) amount))))
    (apply #'color-rgb-to-hex (color-hsl-to-rgb h s l))))

(defun asi-k--lighten (hex amount)
  "Lighten HEX color by AMOUNT (0-1)."
  (let* ((rgb (color-name-to-rgb hex))
         (hsl (apply #'color-rgb-to-hsl rgb))
         (h (car hsl))
         (s (cadr hsl))
         (l (min 0.95 (+ (caddr hsl) amount))))
    (apply #'color-rgb-to-hex (color-hsl-to-rgb h s l))))

(defun asi-k--desaturate (hex amount)
  "Desaturate HEX by AMOUNT (0-1)."
  (let* ((rgb (color-name-to-rgb hex))
         (hsl (apply #'color-rgb-to-hsl rgb))
         (h (car hsl))
         (s (max 0.0 (- (cadr hsl) amount)))
         (l (caddr hsl)))
    (apply #'color-rgb-to-hex (color-hsl-to-rgb h s l))))

(defun asi-k--at (offset)
  "Get palette color at current index + OFFSET (wrapping)."
  (nth (mod (+ asi-k--index offset) (length asi-k--palette))
       asi-k--palette))

;; ═══════════════════════════════════════════════════════════
;; Face application: mode-line, header, fringes, cursor, etc.
;; ═══════════════════════════════════════════════════════════

(defun asi-k--apply-colors ()
  "Apply current kaleidoscope colors to all Emacs chrome."
  (let* ((current   (asi-k--at 0))          ;; mode-line: THIS color
         (prev      (asi-k--at -1))         ;; preceding element
         (next      (asi-k--at 1))          ;; subsequent element
         (complement (asi-k--complement current))  ;; polar opposite
         (dark-cur  (asi-k--darken current 0.25))
         (light-cur (asi-k--lighten current 0.15))
         (desat-cur (asi-k--desaturate current 0.3))
         (dark-comp (asi-k--darken complement 0.2))
         (fg-on-cur (if (> (caddr (apply #'color-rgb-to-hsl
                                         (color-name-to-rgb current)))
                          0.5)
                        "#000000" "#ffffff")))

    ;; ── Mode line: CURRENT color ──
    (set-face-attribute 'mode-line nil
                        :background current
                        :foreground fg-on-cur
                        :box `(:line-width 2 :color ,dark-cur))

    ;; ── Mode line inactive: desaturated current ──
    (set-face-attribute 'mode-line-inactive nil
                        :background desat-cur
                        :foreground (asi-k--darken desat-cur 0.3)
                        :box `(:line-width 1 :color ,(asi-k--darken desat-cur 0.15)))

    ;; ── Header line: COMPLEMENT (polar opposite) ──
    (set-face-attribute 'header-line nil
                        :background complement
                        :foreground (if (> (caddr (apply #'color-rgb-to-hsl
                                                         (color-name-to-rgb complement)))
                                          0.5)
                                        "#000000" "#ffffff"))

    ;; ── Left fringe: PRECEDING color ──
    (set-face-attribute 'fringe nil
                        :background (asi-k--darken prev 0.15)
                        :foreground prev)

    ;; ── Vertical border: NEXT color ──
    (set-face-attribute 'vertical-border nil
                        :foreground next)

    ;; ── Cursor: complement ──
    (set-face-attribute 'cursor nil
                        :background complement)

    ;; ── Region (selection): lightened current ──
    (set-face-attribute 'region nil
                        :background (asi-k--lighten current 0.2)
                        :foreground "#000000")

    ;; ── Minibuffer prompt: next color ──
    (set-face-attribute 'minibuffer-prompt nil
                        :foreground next
                        :weight 'bold)

    ;; ── Line number current: current ──
    (when (facep 'line-number-current-line)
      (set-face-attribute 'line-number-current-line nil
                          :foreground current
                          :weight 'bold))

    ;; ── Line numbers: preceding ──
    (when (facep 'line-number)
      (set-face-attribute 'line-number nil
                          :foreground (asi-k--darken prev 0.1)))

    ;; Advance index with oscillation
    (setq asi-k--index (mod (1+ asi-k--index) (length asi-k--palette)))))

;; ═══════════════════════════════════════════════════════════
;; Timer control
;; ═══════════════════════════════════════════════════════════

(defun asi-kaleidoscope-start ()
  "Start the oscillating color kaleidoscope."
  (interactive)
  (asi-kaleidoscope-stop)
  (setq asi-k--running t)
  (asi-k--apply-colors)  ;; immediate first frame
  (setq asi-k--timer
        (run-at-time asi-k--speed asi-k--speed #'asi-k--apply-colors))
  (message "Kaleidoscope started (%.1fs cycle, %d colors)" asi-k--speed (length asi-k--palette)))

(defun asi-kaleidoscope-stop ()
  "Stop the kaleidoscope and freeze current colors."
  (interactive)
  (when asi-k--timer
    (cancel-timer asi-k--timer)
    (setq asi-k--timer nil))
  (setq asi-k--running nil)
  (message "Kaleidoscope stopped at index %d: %s" asi-k--index (asi-k--at 0)))

(defun asi-kaleidoscope-faster ()
  "Speed up the kaleidoscope."
  (interactive)
  (setq asi-k--speed (max 0.1 (- asi-k--speed 0.1)))
  (when asi-k--running (asi-kaleidoscope-start))
  (message "Speed: %.1fs" asi-k--speed))

(defun asi-kaleidoscope-slower ()
  "Slow down the kaleidoscope."
  (interactive)
  (setq asi-k--speed (min 5.0 (+ asi-k--speed 0.2)))
  (when asi-k--running (asi-kaleidoscope-start))
  (message "Speed: %.1fs" asi-k--speed))

(defun asi-kaleidoscope-step ()
  "Advance one step without timer."
  (interactive)
  (asi-k--apply-colors)
  (message "Step %d: %s → complement %s"
           asi-k--index (asi-k--at -1) (asi-k--complement (asi-k--at -1))))

;; ═══════════════════════════════════════════════════════════
;; Hydra integration
;; ═══════════════════════════════════════════════════════════

(defhydra asi-kaleidoscope-hydra (:color pink :hint nil)
  "
 Kaleidoscope [%s(if asi-k--running \"ON\" \"OFF\")] idx=%s(number-to-string asi-k--index) speed=%s(format \"%.1f\" asi-k--speed)s
 ─────────────────────────────────────
  _k_ Start    _s_ Stop     _n_ Step
  _+_ Faster   _-_ Slower   _q_ Quit
"
  ("k" asi-kaleidoscope-start)
  ("s" asi-kaleidoscope-stop)
  ("n" asi-kaleidoscope-step)
  ("+" asi-kaleidoscope-faster)
  ("-" asi-kaleidoscope-slower)
  ("q" nil :exit t))

;; Wire into main ASI agenda
(defun asi-agenda-kaleidoscope ()
  "Open kaleidoscope control hydra."
  (interactive)
  (asi-kaleidoscope-hydra/body))

;; Rebuild main hydra with kaleidoscope key
(defhydra asi-agenda (:color blue :hint nil :exit t)
  "
 ASI Agenda: %s(asi-agenda--repo-count) repos | %s(asi-agenda--skill-count) skills
 ────────────────────────────────────────────────
  _r_ Repos        _s_ Skills      _m_ MCP
  _j_ Julia REPL   _d_ DuckDB      _t_ Triads
  _c_ Colors       _k_ Kaleidoscope _q_ Quit
"
  ("r" asi-agenda-repos)
  ("s" asi-agenda-skills)
  ("m" asi-agenda-mcp)
  ("j" asi-agenda-julia)
  ("d" asi-agenda-duckdb)
  ("t" (message "Triads: emacs(-1) + agenda(+1) + bb(0) = 0"))
  ("c" asi-agenda-colors)
  ("k" asi-agenda-kaleidoscope)
  ("q" nil))

(global-set-key (kbd "C-c a") 'asi-agenda/body)
(global-set-key (kbd "C-c k") 'asi-kaleidoscope-hydra/body)

(message "Kaleidoscope loaded. C-c k to control, C-c a k from agenda.")
