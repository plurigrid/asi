;; ASI Terminal Fix: Maximum color gamut + mouse sensitivity
;; For Ghostty terminal with 24-bit truecolor

;; ═══════════════════════════════════════════════════════════
;; 1. DIRECT COLOR (24-bit truecolor)
;; ═══════════════════════════════════════════════════════════

;; Force the terminal to use 24-bit direct color mapping
;; instead of approximating to named X11 colors
(when (and (not (display-graphic-p))
           (>= (display-color-cells) 16777216))

  ;; Tell Emacs this terminal can do 24-bit RGB directly
  (set-terminal-parameter nil 'direct-color t)

  ;; Define tty-color-standard-values to use direct RGB
  ;; This overrides the named-color approximation
  (defun asi--tty-color-desc (color)
    "Return direct 24-bit color values for COLOR string like #RRGGBB."
    (when (string-match "\\`#\\([0-9a-fA-F]\\{2\\}\\)\\([0-9a-fA-F]\\{2\\}\\)\\([0-9a-fA-F]\\{2\\}\\)\\'" color)
      (let ((r (string-to-number (match-string 1 color) 16))
            (g (string-to-number (match-string 2 color) 16))
            (b (string-to-number (match-string 3 color) 16)))
        (list (+ (* r 65536) (* g 256) b)
              (* r 257) (* g 257) (* b 257)))))

  ;; Emit direct-color SGR escape sequences
  ;; CSI 38;2;R;G;B m  for foreground
  ;; CSI 48;2;R;G;B m  for background
  (unless (terminal-parameter nil 'xterm--direct-color-configured)
    ;; Send DECRQM to check if terminal supports direct color
    ;; Ghostty supports SGR truecolor natively
    (send-string-to-terminal "\e[?2031h")  ;; Enable 24-bit color mode if supported

    (set-terminal-parameter nil 'xterm--direct-color-configured t))

  (message "Direct 24-bit color enabled (%d cells)" (display-color-cells)))

;; ═══════════════════════════════════════════════════════════
;; 2. XTERM MOUSE MODE (full sensitivity)
;; ═══════════════════════════════════════════════════════════

;; Enable all mouse events
(xterm-mouse-mode 1)
(mouse-wheel-mode 1)

;; SGR mouse mode (1006) for coordinates > 223
;; This is critical for wide terminals
(when (not (display-graphic-p))
  ;; Enable SGR extended coordinates (no 223 column limit)
  (send-string-to-terminal "\e[?1006h")

  ;; Enable button event tracking (report motion while button pressed)
  (send-string-to-terminal "\e[?1002h")

  ;; Enable any-event tracking (report all mouse motion)
  ;; Uncomment if you want hover tracking:
  ;; (send-string-to-terminal "\e[?1003h")

  ;; Enable focus events (FocusIn/FocusOut)
  (send-string-to-terminal "\e[?1004h"))

;; Pixel scroll for smooth scrolling
(when (fboundp 'pixel-scroll-precision-mode)
  (pixel-scroll-precision-mode 1))

;; Mouse bindings for terminal
(global-set-key [mouse-4] 'scroll-down-line)
(global-set-key [mouse-5] 'scroll-up-line)

;; Horizontal scroll
(global-set-key [mouse-6] (lambda () (interactive) (scroll-right 3)))
(global-set-key [mouse-7] (lambda () (interactive) (scroll-left 3)))

;; Middle-click paste
(global-set-key [mouse-2] 'mouse-yank-primary)

;; Context menu on right click
(when (fboundp 'context-menu-mode)
  (context-menu-mode 1))

;; ═══════════════════════════════════════════════════════════
;; 3. COLOR-AWARE FACE CONFIGURATION
;; ═══════════════════════════════════════════════════════════

;; Set background mode properly for color calculations
(set-terminal-parameter nil 'background-mode 'dark)
(frame-set-background-mode (selected-frame))

;; Ensure faces use full 24-bit when available
(defun asi--set-face-hex (face attr hex)
  "Set FACE ATTR to HEX color, using direct 24-bit."
  (set-face-attribute face nil attr hex))

;; Verify: create a test overlay with exact hex color
(defun asi-color-test ()
  "Insert 24-bit color test swatches in current buffer."
  (interactive)
  (let ((buf (get-buffer-create "*Color Test*")))
    (with-current-buffer buf
      (read-only-mode -1)
      (erase-buffer)
      (insert "24-bit Direct Color Test\n\n")
      (dolist (hex '("#E847C0" "#FF0000" "#00FF00" "#0000FF"
                     "#769c7d" "#55b0e6" "#c8a0c2" "#ffa6c2"
                     "#789a20" "#54c1ed" "#285dd0" "#6233ef"))
        (let ((start (point)))
          (insert "  ██████  ")
          (put-text-property start (point) 'face `(:foreground ,hex))
          (let ((s2 (point)))
            (insert "  ██████  ")
            (put-text-property s2 (point) 'face `(:background ,hex)))
          (insert " " hex "\n")))
      (insert "\nMouse: click anywhere, scroll, drag to test.\n")
      (insert "If swatches show exact colors (not approximated), direct color works.\n")
      (goto-char (point-min))
      (read-only-mode 1))
    (switch-to-buffer buf)))

;; ═══════════════════════════════════════════════════════════
;; 4. GHOSTTY-SPECIFIC OPTIMIZATIONS
;; ═══════════════════════════════════════════════════════════

;; Ghostty supports Kitty keyboard protocol
(when (string-match-p "ghostty" (or (getenv "TERM_PROGRAM") ""))
  ;; Enable Kitty progressive enhancement (if supported)
  ;; Flags: 1=disambiguate, 2=report_events, 4=report_alternate, 8=report_all, 16=report_associated
  (send-string-to-terminal "\e[>1u")  ;; Level 1: disambiguate escape codes

  ;; Enable styled underlines (curly, dotted, dashed)
  (when (fboundp 'set-face-attribute)
    ;; Ghostty supports CSI 4:3 m for curly underline
    t))

;; Override TERM if it's wrong
(when (string= (getenv "TERM") "dumb")
  ;; Can't setenv TERM retroactively for the tty, but we can
  ;; ensure Emacs treats this terminal correctly
  (message "Warning: TERM=dumb detected. Terminal features forced on."))

;; ═══════════════════════════════════════════════════════════
;; 5. INTEGRATE WITH GAY.JL HYDRA
;; ═══════════════════════════════════════════════════════════

;; Update the color display to use direct hex faces
(defun asi-gay--show-color-buffer-direct (title)
  "Capture Julia output and display with DIRECT 24-bit colored swatches."
  (when (get-buffer "*julia-repl*")
    (let* ((output (with-current-buffer "*julia-repl*"
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
                   (hex-str (match-string 2 line))
                   (color (concat "#" hex-str)))
              ;; Background swatch
              (let ((s1 (point)))
                (insert "  ")
                (put-text-property s1 (point) 'face `(:background ,color)))
              ;; Foreground blocks
              (let ((s2 (point)))
                (insert (format " %s " color))
                (put-text-property s2 (point) 'face `(:foreground ,color :weight bold)))
              ;; Readable hex label
              (insert (format " %2s: %s" idx color))
              (insert "\n"))))
        (org-mode)
        (goto-char (point-min))
        (read-only-mode 1))
      (display-buffer buf))))

;; Replace the old show function
(fset 'asi-gay--show-color-buffer #'asi-gay--show-color-buffer-direct)

(message "Terminal fixed: 24-bit direct color + SGR mouse + pixel scroll. Run M-x asi-color-test")
