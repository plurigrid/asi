;; ASI Gay.jl Color Generation via emacsclient → Julia REPL
;; Rapid color generation commands for the ASI Agenda hydra

(require 'ansi-color)

(defvar asi-gay--julia-buffer "*julia-repl*"
  "Buffer name for the Julia REPL.")

(defvar asi-gay--last-palette nil
  "Last generated palette as list of hex strings.")

(defvar asi-gay--seed 1069
  "Current Gay.jl seed (canonical: 1069 = 0x42D).")

(defun asi-gay--julia-eval (code)
  "Send CODE to Julia REPL and return after brief pause."
  (when (get-buffer asi-gay--julia-buffer)
    (with-current-buffer asi-gay--julia-buffer
      (term-send-raw-string (concat code "\n")))))

(defun asi-gay--julia-capture (code callback)
  "Send CODE to Julia REPL, wait, then call CALLBACK with buffer tail."
  (asi-gay--julia-eval code)
  (run-at-time 1.5 nil
               (lambda ()
                 (when (get-buffer asi-gay--julia-buffer)
                   (with-current-buffer asi-gay--julia-buffer
                     (let ((output (buffer-substring-no-properties
                                    (max (- (point-max) 2000) (point-min))
                                    (point-max))))
                       (when callback
                         (funcall callback output))))))))

(defun asi-gay-genesis ()
  "Display the Gay.jl genesis color chain (seed 1069, indices 0-11)."
  (interactive)
  (asi-gay--julia-eval
   (format "for i in 0:11; c=color_at(i;seed=%d); println(lpad(i,2),\": \",ghex(c),\"  \",c); end"
           asi-gay--seed))
  (run-at-time 2 nil #'asi-gay--show-color-buffer "Genesis Colors"))

(defun asi-gay-palette (n)
  "Generate N-color palette from current seed."
  (interactive "nPalette size: ")
  (asi-gay--julia-eval
   (format "gay_seed!(%d); p=next_palette(%d); for (i,c) in enumerate(p); println(lpad(i,2),\": \",ghex(c)); end"
           asi-gay--seed n))
  (run-at-time 2 nil #'asi-gay--show-color-buffer (format "Palette (%d colors)" n)))

(defun asi-gay-random-seed ()
  "Generate colors from a random seed."
  (interactive)
  (let ((seed (random 65536)))
    (setq asi-gay--seed seed)
    (asi-gay--julia-eval
     (format "s=%d; gay_seed!(s); println(\"Seed: \",s); for i in 0:7; println(lpad(i,2),\": \",ghex(color_at(i;seed=s))); end"
             seed))
    (run-at-time 2 nil #'asi-gay--show-color-buffer (format "Random Seed %d" seed))))

(defun asi-gay-set-seed (seed)
  "Set the Gay.jl seed."
  (interactive "nSeed: ")
  (setq asi-gay--seed seed)
  (message "Gay.jl seed set to %d (0x%X)" seed seed))

(defun asi-gay--show-color-buffer (title)
  "Capture Julia output and display with colored swatches."
  (when (get-buffer asi-gay--julia-buffer)
    (let* ((output (with-current-buffer asi-gay--julia-buffer
                     (buffer-substring-no-properties
                      (max (- (point-max) 2000) (point-min))
                      (point-max))))
           (lines (split-string output "\n"))
           (buf (get-buffer-create "*ASI Colors*")))
      (with-current-buffer buf
        (read-only-mode -1)
        (erase-buffer)
        (insert (format "#+TITLE: %s (seed=%d)\n\n" title asi-gay--seed))
        (dolist (line lines)
          (when (string-match "\\([0-9]+\\): #\\([0-9a-fA-F]\\{6\\}\\)" line)
            (let* ((idx (match-string 1 line))
                   (hex (match-string 2 line))
                   (color (concat "#" hex)))
              ;; Insert colored block + hex
              (let ((start (point)))
                (insert "  ")
                (put-text-property start (point) 'face `(:background ,color))
                (insert (format " %s  %s\n" color (propertize (make-string 20 ?█)
                                                               'face `(:foreground ,color))))))))
        (org-mode)
        (goto-char (point-min))
        (read-only-mode 1))
      (display-buffer buf))))

(defun asi-gay-interleave ()
  "Generate interleaved color streams."
  (interactive)
  (asi-gay--julia-eval
   (format "gay_seed!(%d); a,b=gay_interleave_streams(2,4); println(\"Stream A:\"); for c in a; print(ghex(c),\" \"); end; println(); println(\"Stream B:\"); for c in b; print(ghex(c),\" \"); end; println()"
           asi-gay--seed))
  (run-at-time 2 nil #'asi-gay--show-color-buffer "Interleaved Streams"))

(defun asi-gay-pride (flag)
  "Show a pride flag palette."
  (interactive
   (list (completing-read "Flag: " '("rainbow" "bisexual" "transgender" "nonbinary" "pansexual" "asexual") nil t)))
  (asi-gay--julia-eval
   (format "p=%s(); for (i,c) in enumerate(p); println(lpad(i,2),\": \",ghex(c)); end" flag))
  (run-at-time 2 nil #'asi-gay--show-color-buffer (format "Pride: %s" flag)))

(defun asi-gay-sweep ()
  "Run a Monte Carlo color sweep."
  (interactive)
  (asi-gay--julia-eval
   (format "ctx=GayMCContext(%d,8); gay_sweep!(ctx,100); println(\"Sweep done\"); for i in 1:8; println(lpad(i,2),\": \",ghex(color_state(ctx,i))); end"
           asi-gay--seed))
  (run-at-time 3 nil #'asi-gay--show-color-buffer "MC Sweep"))

;; Extend the ASI Agenda hydra with color submenu
(defhydra asi-gay-hydra (:color blue :hint nil :exit t)
  "
 Gay.jl Colors (seed=%s(number-to-string asi-gay--seed))
 ──────────────────────────────
  _g_ Genesis chain   _p_ Palette (N)
  _r_ Random seed     _s_ Set seed
  _i_ Interleave      _f_ Pride flag
  _w_ MC sweep        _j_ Julia REPL
  _q_ Back
"
  ("g" asi-gay-genesis)
  ("p" asi-gay-palette)
  ("r" asi-gay-random-seed)
  ("s" asi-gay-set-seed)
  ("i" asi-gay-interleave)
  ("f" asi-gay-pride)
  ("w" asi-gay-sweep)
  ("j" (switch-to-buffer "*julia-repl*"))
  ("q" nil))

;; Wire into main ASI agenda
(defun asi-agenda-colors ()
  "Open Gay.jl color generation hydra."
  (interactive)
  (asi-gay-hydra/body))

;; Rebind the main hydra with color key
(defhydra asi-agenda (:color blue :hint nil :exit t)
  "
 ASI Agenda: %s(asi-agenda--repo-count) repos | %s(asi-agenda--skill-count) skills
 ────────────────────────────────────────────────
  _r_ Repos        _s_ Skills      _m_ MCP
  _j_ Julia REPL   _d_ DuckDB      _t_ Triads
  _c_ Colors (Gay.jl)              _q_ Quit
"
  ("r" asi-agenda-repos)
  ("s" asi-agenda-skills)
  ("m" asi-agenda-mcp)
  ("j" asi-agenda-julia)
  ("d" asi-agenda-duckdb)
  ("t" (message "Triads: emacs(-1) + agenda(+1) + bb(0) = 0"))
  ("c" asi-agenda-colors)
  ("q" nil))

(global-set-key (kbd "C-c a") 'asi-agenda/body)

(message "Gay.jl color hydra loaded. C-c a → c for colors.")
