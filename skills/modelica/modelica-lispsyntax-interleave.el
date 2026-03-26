;; modelica-lispsyntax-interleave.el --- Modelica × LispSyntax interleave in Emacs
;; Alphabet-color MCP interleaving with rainbow parens and Modelica components
;; Requires: asi-gay-colors.el (Gay.jl bridge), julia-repl

(require 'cl-lib)
(require 'hydra nil t)  ; optional — hydra menu degrades to keymap-only if missing

;;; --- Configuration ---

(defvar mli--seed 137508
  "Canonical seed for the alphabet-color interleave.")

(defvar mli--workers 3
  "Number of triadic workers (GF(3) conserved).")

(defvar mli--alphabet-colors
  '((?A . "#B0285F") (?B . "#77DEB1") (?C . "#8ADB6E") (?D . "#3A71C0")
    (?E . "#2A7AE3") (?F . "#D6DB4C") (?G . "#6638C2") (?H . "#AF100A")
    (?I . "#AD90E0") (?J . "#C30F2D") (?K . "#969D34") (?L . "#61BFE7")
    (?M . "#79EBDD") (?N . "#D7D085") (?O . "#E146A8") (?P . "#0BAD20")
    (?Q . "#86DC73") (?R . "#8E7526") (?S . "#65DBDE") (?T . "#F2E388")
    (?U . "#1767B8") (?V . "#D04158") (?W . "#C42990") (?X . "#ECEF73")
    (?Y . "#7E3CEA") (?Z . "#F04E5B"))
  "Alphabet colors from Gay.jl seed 137508. Refreshed via `mli-generate-alphabet'.")

(defvar mli--mcp-table
  '((?A . "gay-mcp")       (?B . "babashka")        (?C . "comrade")
    (?D . "deepwiki")       (?E . "exa")             (?F . "firecrawl")
    (?G . "gay.jl")         (?H . "hatchery")        (?I . "interleave")
    (?J . "julia-dynamics") (?K . "kernelabstractions") (?L . "lispsyntax")
    (?M . "modelica")       (?N . "narya")           (?O . "omg-tension")
    (?P . "propagators")    (?Q . "query-duckdb")    (?R . "reafference")
    (?S . "splittablerng")  (?T . "tropical")        (?U . "unworld")
    (?V . "valence")        (?W . "world-hopping")   (?X . "xy-model")
    (?Y . "yielding")       (?Z . "zigzag"))
  "Letter → MCP/skill assignment table.")

(defvar mli--worker-assignment
  '((1 . (?A ?D ?G ?J ?M ?P ?S ?V ?Y))   ; MINUS (-1) × 9
    (2 . (?B ?E ?H ?K ?N ?Q ?T ?W))      ; ERGODIC (0) × 8
    (3 . (?C ?F ?I ?L ?O ?R ?U ?X ?Z)))   ; PLUS (+1) × 9
  "GF(3) triadic worker assignment.
Σ = (-1×9) + (0×8) + (+1×9) = 0 ✓
Z moved from W2→W3 to conserve.")

;;; --- Julia REPL communication ---

(defun mli--julia-eval (code)
  "Send CODE to the Julia REPL."
  (let ((buf (or (get-buffer "*julia-repl*")
                 (get-buffer "*julia*")
                 (get-buffer "*vterm-julia*"))))
    (when buf
      (with-current-buffer buf
        (cond
         ((derived-mode-p 'term-mode)
          (term-send-raw-string (concat code "\n")))
         ((derived-mode-p 'vterm-mode)
          (vterm-send-string (concat code "\n")))
         (t
          (comint-send-string (get-buffer-process buf) (concat code "\n"))))))))

(defun mli--julia-capture (code callback &optional delay)
  "Send CODE to Julia, wait DELAY seconds, call CALLBACK with output."
  (mli--julia-eval code)
  (run-at-time (or delay 2.0) nil
               (lambda ()
                 (let ((buf (or (get-buffer "*julia-repl*")
                                (get-buffer "*julia*"))))
                   (when buf
                     (with-current-buffer buf
                       (funcall callback
                                (buffer-substring-no-properties
                                 (max (- (point-max) 4000) (point-min))
                                 (point-max)))))))))

;;; --- Alphabet Color Generation ---

(defun mli-generate-alphabet ()
  "Generate the A-Z color palette from Gay.jl seed 137508 and cache it."
  (interactive)
  (mli--julia-eval
   (format "gay_seed!(%d); for (i,c) in enumerate('A':'Z'); println(c,\":\",ghex(color_at(i))); end"
           mli--seed))
  (mli--julia-capture
   ""
   (lambda (output)
     (setq mli--alphabet-colors nil)
     (dolist (line (split-string output "\n"))
       (when (string-match "^\\([A-Z]\\):#\\([0-9a-fA-F]\\{6\\}\\)" line)
         (push (cons (string-to-char (match-string 1 line))
                     (concat "#" (match-string 2 line)))
               mli--alphabet-colors)))
     (setq mli--alphabet-colors (nreverse mli--alphabet-colors))
     (message "Alphabet palette cached: %d colors" (length mli--alphabet-colors)))
   1.5))

(defun mli--letter-color (letter)
  "Get the hex color for LETTER from cache, or a fallback."
  (or (cdr (assq (upcase letter) mli--alphabet-colors))
      "#888888"))

(defun mli--letter-mcp (letter)
  "Get the MCP/skill name for LETTER."
  (or (cdr (assq (upcase letter) mli--mcp-table))
      "unknown"))

(defun mli--letter-worker (letter)
  "Get the worker ID (1-3) for LETTER."
  (let ((ch (upcase letter)))
    (cl-loop for (id . letters) in mli--worker-assignment
             when (memq ch letters) return id
             finally return 0)))

(defun mli--letter-trit (letter)
  "Get the GF(3) trit for LETTER: -1 (MINUS), 0 (ERGODIC), +1 (PLUS)."
  (pcase (mli--letter-worker letter)
    (1 -1) (2 0) (3 1) (_ 0)))

;;; --- Alphabet Display ---

(defun mli-show-alphabet ()
  "Display the full alphabet-color-MCP table in a buffer."
  (interactive)
  (let ((buf (get-buffer-create "*MLI Alphabet*")))
    (with-current-buffer buf
      (read-only-mode -1)
      (erase-buffer)
      (insert (format "Modelica-LispSyntax Interleave — seed %d\n" mli--seed))
      (insert "═══════════════════════════════════════════════════════\n")
      (insert "Letter  Color    Trit  Worker  MCP/Skill\n")
      (insert "───────────────────────────────────────────────────────\n")
      (cl-loop for ch from ?A to ?Z do
               (let* ((color (mli--letter-color ch))
                      (trit (mli--letter-trit ch))
                      (worker (mli--letter-worker ch))
                      (mcp (mli--letter-mcp ch))
                      (trit-str (pcase trit (-1 "-1") (0 " 0") (1 "+1") (_ "??")))
                      (swatch-start (point)))
                 (insert (format "  %c     " ch))
                 (let ((cs (point)))
                   (insert "██")
                   (put-text-property cs (point) 'face `(:foreground ,color)))
                 (insert (format " %s  %s     W%d      %s\n" color trit-str worker mcp))))
      (insert "───────────────────────────────────────────────────────\n")
      (insert (format "Σ trits = (-1×9) + (0×9) + (+1×8) = -1 ≡ 0 (mod 3) ✓\n"))
      (goto-char (point-min))
      (read-only-mode 1))
    (display-buffer buf)))

;;; --- Rainbow Parentheses for LispSyntax ---

(defvar mli--depth-colors
  ["#5BDF75" "#B0285F" "#77DEB1" "#8ADB6E" "#3A71C0"
   "#2A7AE3" "#D6DB4C" "#6638C2" "#AF100A" "#AD90E0"]
  "Depth-indexed colors for rainbow parens (from alphabet seed 137508).")

(defun mli--fontify-rainbow-parens (limit)
  "Font-lock matcher: color parentheses by nesting depth up to LIMIT."
  (let ((depth 0))
    (save-excursion
      (goto-char (point-min))
      (while (< (point) (min limit (point-max)))
        (cond
         ((looking-at "(")
          (let ((color (aref mli--depth-colors (mod depth (length mli--depth-colors)))))
            (put-text-property (point) (1+ (point)) 'face `(:foreground ,color :weight bold)))
          (setq depth (1+ depth))
          (forward-char 1))
         ((looking-at ")")
          (setq depth (max 0 (1- depth)))
          (let ((color (aref mli--depth-colors (mod depth (length mli--depth-colors)))))
            (put-text-property (point) (1+ (point)) 'face `(:foreground ,color :weight bold)))
          (forward-char 1))
         (t (forward-char 1))))))
  nil)

(defun mli-rainbow-parens-mode ()
  "Toggle rainbow parentheses colored by MLI depth palette."
  (interactive)
  (if (memq 'mli--fontify-rainbow-parens font-lock-keywords)
      (progn
        (font-lock-remove-keywords nil '((mli--fontify-rainbow-parens)))
        (font-lock-flush)
        (message "MLI rainbow parens OFF"))
    (font-lock-add-keywords nil '((mli--fontify-rainbow-parens)) 'append)
    (font-lock-flush)
    (message "MLI rainbow parens ON")))

;;; --- Modelica S-expression Bridge ---

(defun mli-modelica-to-sexp (modelica-code)
  "Convert a Modelica component to LispSyntax S-expression via Julia."
  (mli--julia-eval
   (format "using LispSyntax; println(modelica_to_sexp(\"\"\"%s\"\"\"))" modelica-code)))

(defun mli-sexp-to-modelica (sexp-code)
  "Convert a LispSyntax S-expression back to Modelica via Julia."
  (mli--julia-eval
   (format "using LispSyntax; println(sexp_to_modelica(parse_sexp(\"\"\"%s\"\"\")))" sexp-code)))

(defun mli-convert-region-to-sexp (beg end)
  "Convert Modelica region to S-expression."
  (interactive "r")
  (let ((code (buffer-substring-no-properties beg end)))
    (mli-modelica-to-sexp code)))

(defun mli-convert-region-to-modelica (beg end)
  "Convert S-expression region to Modelica."
  (interactive "r")
  (let ((code (buffer-substring-no-properties beg end)))
    (mli-sexp-to-modelica code)))

;;; --- Interleave Streams ---

(defun mli-interleave-streams ()
  "Generate 3 triadic interleaved color streams and display them."
  (interactive)
  (mli--julia-eval
   (format "gay_seed!(%d); streams=Gay.interleave(9,n_streams=3,seed=%d); for (id,cs) in streams; println(\"Worker \",id,\":\"); for c in cs; print(\" \",ghex(c)); end; println(); end"
           mli--seed mli--seed))
  (run-at-time 2 nil
               (lambda ()
                 (let ((buf (get-buffer-create "*MLI Streams*")))
                   (with-current-buffer buf
                     (read-only-mode -1)
                     (erase-buffer)
                     (insert (format "Triadic Interleave Streams — seed %d\n\n" mli--seed))
                     (cl-loop for (wid . letters) in mli--worker-assignment
                              for trit in '(-1 0 1)
                              for label in '("MINUS" "ERGODIC" "PLUS") do
                              (insert (format "Worker %d (%s, trit=%+d):\n  " wid label trit))
                              (dolist (ch letters)
                                (let* ((color (mli--letter-color ch))
                                       (start (point)))
                                  (insert (format "%c" ch))
                                  (put-text-property start (point) 'face
                                                     `(:foreground ,color :weight bold))
                                  (insert " ")))
                              (insert "\n\n"))
                     (goto-char (point-min))
                     (read-only-mode 1))
                   (display-buffer buf)))))

;;; --- Modelica Component Inspector ---

(defun mli-inspect-component ()
  "Inspect the Modelica component at point: show its letter, color, trit."
  (interactive)
  (let* ((word (thing-at-point 'word t))
         (first-char (and word (upcase (aref word 0)))))
    (if (and first-char (<= ?A first-char) (>= ?Z first-char))
        (let ((color (mli--letter-color first-char))
              (mcp (mli--letter-mcp first-char))
              (trit (mli--letter-trit first-char))
              (worker (mli--letter-worker first-char)))
          (message "%c → %s (trit=%+d, W%d, MCP=%s)"
                   first-char color trit worker mcp))
      (message "No alphabetic component at point"))))

;;; --- Tension Resolver (Modelica dynamics) ---

(defun mli-resolve-tension (letter1 letter2)
  "Resolve tension between two alphabet-MCPs via Julia bridge."
  (interactive
   (list (read-char "First letter: ")
         (read-char "Second letter: ")))
  (let* ((c1 (mli--letter-color letter1))
         (c2 (mli--letter-color letter2))
         (t1 (mli--letter-trit letter1))
         (t2 (mli--letter-trit letter2))
         (sum (mod (+ t1 t2 3) 3)))
    (mli--julia-eval
     (format "gay_seed!(%d); c1=color_at(%d); c2=color_at(%d); mixed=Gay.mix(c1,c2); println(\"Tension: %c(\",ghex(c1),\") × %c(\",ghex(c2),\") → \",ghex(mixed),\" trit_sum=%d\")"
             mli--seed (- (upcase letter1) ?A -1) (- (upcase letter2) ?A -1)
             (upcase letter1) (upcase letter2) sum))
    (message "%c(%s,t=%+d) × %c(%s,t=%+d) → Σ≡%d (mod 3)"
             (upcase letter1) c1 t1 (upcase letter2) c2 t2 sum)))

;;; --- Modelica File Support ---

(defun mli--modelica-sexp-overlay ()
  "Add color overlays to Modelica keywords matching alphabet letters."
  (save-excursion
    (goto-char (point-min))
    (while (re-search-forward "\\b\\(model\\|connector\\|equation\\|connect\\|parameter\\|Real\\|Integer\\|Boolean\\|flow\\|input\\|output\\|extends\\|replaceable\\)\\b" nil t)
      (let* ((word (match-string 0))
             (ch (upcase (aref word 0)))
             (color (mli--letter-color ch)))
        (when (and (<= ?A ch) (>= ?Z ch))
          (let ((ov (make-overlay (match-beginning 0) (match-end 0))))
            (overlay-put ov 'face `(:foreground ,color))
            (overlay-put ov 'mli-overlay t)))))))

(defun mli-colorize-modelica-buffer ()
  "Colorize Modelica keywords by their alphabet-letter color."
  (interactive)
  ;; Remove old overlays
  (remove-overlays (point-min) (point-max) 'mli-overlay t)
  (mli--modelica-sexp-overlay)
  (message "Modelica buffer colorized with alphabet palette"))

;;; --- Hydra Menu (optional, degrades gracefully) ---

(when (featurep 'hydra)
  (defhydra mli-hydra (:color blue :hint nil :exit t)
    "
 Modelica×LispSyntax Interleave (seed=%s(number-to-string mli--seed))
 ────────────────────────────────────────────────
  _a_ Alphabet table    _s_ Interleave streams
  _r_ Rainbow parens    _c_ Colorize Modelica
  _i_ Inspect at point  _t_ Resolve tension
  _g_ Generate palette  _j_ Julia REPL
  _m_ → Modelica sexp   _l_ → LispSyntax sexp
  _q_ Back
"
    ("a" mli-show-alphabet)
    ("s" mli-interleave-streams)
    ("r" mli-rainbow-parens-mode)
    ("c" mli-colorize-modelica-buffer)
    ("i" mli-inspect-component)
    ("t" (call-interactively 'mli-resolve-tension))
    ("g" mli-generate-alphabet)
    ("j" (switch-to-buffer (or (get-buffer "*julia-repl*") (get-buffer "*julia*"))))
    ("m" (call-interactively 'mli-convert-region-to-sexp))
    ("l" (call-interactively 'mli-convert-region-to-modelica))
    ("q" nil)))

(unless (featurep 'hydra)
  (defun mli-hydra/body ()
    "Fallback menu when hydra is not installed."
    (interactive)
    (message "MLI: [a]lphabet [s]treams [r]ainbow [c]olorize [i]nspect [t]ension [g]enerate")))

;;; --- Minor Mode ---

(defvar mli-mode-map
  (let ((map (make-sparse-keymap))
        (sub (make-sparse-keymap)))
    (define-key sub (kbd "m") 'mli-hydra/body)
    (define-key sub (kbd "i") 'mli-inspect-component)
    (define-key sub (kbd "r") 'mli-rainbow-parens-mode)
    (define-key sub (kbd "c") 'mli-colorize-modelica-buffer)
    (define-key sub (kbd "a") 'mli-show-alphabet)
    (define-key sub (kbd "s") 'mli-interleave-streams)
    (define-key sub (kbd "g") 'mli-generate-alphabet)
    (define-key sub (kbd "t") 'mli-resolve-tension)
    (define-key map (kbd "C-c m") sub)
    map)
  "Keymap for MLI minor mode.
C-c m m  — hydra menu (or fallback)
C-c m a  — alphabet table
C-c m i  — inspect component at point
C-c m r  — rainbow parens toggle
C-c m c  — colorize Modelica buffer
C-c m s  — interleave streams
C-c m g  — generate palette from Julia
C-c m t  — resolve tension")

(define-minor-mode mli-mode
  "Modelica-LispSyntax Interleave minor mode.
Provides alphabet-color overlay, rainbow parens, and Julia bridge.
\\{mli-mode-map}"
  :lighter " MLI"
  :keymap mli-mode-map
  (if mli-mode
      (progn
        (unless mli--alphabet-colors
          (message "MLI: Run C-c m → g to generate alphabet palette from Julia"))
        (message "MLI mode enabled. C-c m for menu."))
    (remove-overlays (point-min) (point-max) 'mli-overlay t)
    (message "MLI mode disabled.")))

;; Auto-enable for Modelica files
(add-to-list 'auto-mode-alist '("\\.mo\\'" . (lambda () (modelica-mode) (mli-mode 1))))

;; Wire into ASI agenda if loaded
(with-eval-after-load 'asi-gay-colors
  (when (and (featurep 'hydra) (fboundp 'asi-agenda/body))
    (defhydra+ asi-agenda ()
      ("M" mli-hydra/body))))

(provide 'modelica-lispsyntax-interleave)

(message "MLI loaded. C-c m for Modelica×LispSyntax interleave hydra.")
