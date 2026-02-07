;;; init-example.el --- Example configuration for transcendental-keyboard -*- lexical-binding: t -*-

;; Example Emacs configuration for transcendental keyboard control surface
;; Add to your init.el or use as standalone config

;;; ============================================================================
;;; Dependencies
;;; ============================================================================

;; Proof General
(use-package proof-general
  :straight (proof-general
             :type git
             :host github
             :repo "ProofGeneral/PG")
  :config
  (setq proof-splash-enable nil)
  (setq proof-three-window-mode-policy 'hybrid))

;; Gay.jl color integration
(use-package gay
  :load-path "~/i/"  ; Adjust path to your gay.el location
  :config
  (setq gay-seed 1069)
  (setq gay-color-target 'mode-line)
  (setq gay-apply-faces t))

;;; ============================================================================
;;; Transcendental Keyboard
;;; ============================================================================

(use-package transcendental-keyboard
  :load-path "~/asi/skills/transcendental-keyboard"
  :after (gay proof-site)

  ;; Auto-enable for proof files
  :hook ((coq-mode . transcendental-keyboard-mode)
         (lean-mode . transcendental-keyboard-mode))

  :config

  ;; === Core Settings ===
  (setq trans-kb-gay-seed 1069)
  (setq trans-kb-color-mode t)
  (setq trans-kb-auto-save t)

  ;; === Proof Assistant Paths ===
  (setq trans-kb-proof-assistants
        '((narya . "~/.local/bin/narya")
          (lean . "~/.elan/bin/lean")
          (coq . "coqtop")
          (stellogen . "~/stellogen/_build/default/bin/sgen")))

  ;; === Auto-Prove Tactics ===
  ;; Customize for your domain
  (setq trans-kb-auto-tactics
        '(;; Basic tactics
          "reflexivity"
          "apply assumption"
          "intro"
          "intros"
          "split"
          "constructor"
          "left"
          "right"
          "exact rfl"

          ;; Coq-specific
          "auto"
          "simpl"
          "unfold"
          "ring"
          "omega"
          "lia"

          ;; Lean-specific
          "simp"
          "rfl"
          "exact?"))

  ;; === Custom Key Bindings ===
  ;; Optional: Add your preferred shortcuts
  (with-eval-after-load 'transcendental-keyboard
    ;; Vim-style navigation (optional)
    ;; (define-key transcendental-keyboard-mode-map (kbd "C-j") #'trans-kb-proof-forward)
    ;; (define-key transcendental-keyboard-mode-map (kbd "C-k") #'trans-kb-proof-backward)

    ;; Quick auto-prove
    (define-key transcendental-keyboard-mode-map (kbd "M-a") #'trans-kb-auto-prove)

    ;; Stellogen shortcuts
    (define-key transcendental-keyboard-mode-map (kbd "C-c s r") #'trans-kb-stellogen-run-file)))

;;; ============================================================================
;;; Optional: Narya Mode
;;; ============================================================================

;; If you have narya.el from the Narya repo
(use-package narya-mode
  :load-path "~/narya/proofgeneral/"  ; Adjust path
  :mode "\\.ny\\'"
  :config
  (when (featurep 'transcendental-keyboard)
    (add-hook 'narya-mode-hook #'transcendental-keyboard-mode)))

;;; ============================================================================
;;; Optional: Stellogen Mode
;;; ============================================================================

;; Basic syntax highlighting for Stellogen
(define-derived-mode stellogen-mode prog-mode "Stellogen"
  "Major mode for Stellogen transcendental syntax."
  (setq-local comment-start "' ")
  (setq-local comment-end "")

  ;; Syntax highlighting
  (setq-local font-lock-defaults
              '((("\\<\\(spec\\|galaxy\\|show\\|process\\|end\\)\\>" . font-lock-keyword-face)
                 ("\\<\\(ok\\|accept\\|done\\)\\>" . font-lock-constant-face)
                 ("\\(+\\|-\\)\\w+" . font-lock-variable-name-face))))

  ;; Enable transcendental keyboard
  (when (featurep 'transcendental-keyboard)
    (transcendental-keyboard-mode 1)))

(add-to-list 'auto-mode-alist '("\\.sg\\'" . stellogen-mode))

;;; ============================================================================
;;; Optional: State Change Hooks
;;; ============================================================================

;; Log proof state changes
(defvar trans-kb-state-log-file "~/.emacs.d/proof-state.log"
  "File to log proof state changes.")

(defun trans-kb-log-state-change ()
  "Log state change to file."
  (when (bound-and-true-p transcendental-keyboard-mode)
    (with-temp-buffer
      (insert (format "%s | %s | %s | color-index:%d\n"
                      (format-time-string "%Y-%m-%d %H:%M:%S")
                      (buffer-name)
                      trans-kb-current-state
                      trans-kb-color-index))
      (append-to-file (point-min) (point-max) trans-kb-state-log-file))))

;; Uncomment to enable logging
;; (add-hook 'trans-kb-proof-forward-hook #'trans-kb-log-state-change)

;;; ============================================================================
;;; Optional: Integration with NATS
;;; ============================================================================

;; Publish proof state to NATS (requires gay.el with NATS support)
(defun trans-kb-publish-to-nats ()
  "Publish current proof state to NATS."
  (when (and (featurep 'gay)
             (fboundp 'gay-publish)
             (bound-and-true-p transcendental-keyboard-mode))
    (gay-publish "proof.state"
                 (json-encode
                  `((timestamp . ,(format-time-string "%Y-%m-%dT%H:%M:%S"))
                    (buffer . ,(buffer-name))
                    (state . ,trans-kb-current-state)
                    (trit . ,(trans-kb-state-trit trans-kb-current-state))
                    (color-index . ,trans-kb-color-index))))))

;; Uncomment to enable NATS publishing
;; (add-hook 'trans-kb-proof-forward-hook #'trans-kb-publish-to-nats)

;;; ============================================================================
;;; Optional: Dashboard
;;; ============================================================================

(defun trans-kb-show-dashboard ()
  "Show transcendental keyboard dashboard."
  (interactive)
  (let ((buf (get-buffer-create "*Transcendental Dashboard*")))
    (with-current-buffer buf
      (erase-buffer)
      (insert "╔═══════════════════════════════════════════════════════════╗\n")
      (insert "║       TRANSCENDENTAL KEYBOARD CONTROL SURFACE             ║\n")
      (insert "╚═══════════════════════════════════════════════════════════╝\n\n")
      (insert (format "Current State:   %s\n" trans-kb-current-state))
      (insert (format "GF(3) Trit:      %d\n" (trans-kb-state-trit trans-kb-current-state)))
      (insert (format "Color Index:     %d\n" trans-kb-color-index))
      (insert (format "Gay.jl Seed:     %d\n" trans-kb-gay-seed))
      (insert (format "Color Mode:      %s\n" (if trans-kb-color-mode "ON" "OFF")))
      (insert (format "Auto-save:       %s\n" (if trans-kb-auto-save "ON" "OFF")))
      (insert "\n")
      (insert "State History:\n")
      (insert (format "  Total steps:   %d\n" (length trans-kb-state-history)))
      (insert (format "  Proved:        %d\n"
                      (cl-count 'proved trans-kb-state-history)))
      (insert (format "  Unproved:      %d\n"
                      (cl-count 'unproved trans-kb-state-history)))
      (insert (format "  Processing:    %d\n"
                      (cl-count 'processing trans-kb-state-history)))
      (insert "\n")
      (insert "GF(3) Conservation Analysis:\n")
      (let ((triads 0)
            (conserved 0))
        (cl-loop for (s1 s2 s3) on trans-kb-state-history by #'cdddr
                 while s3
                 do (cl-incf triads)
                 when (trans-kb-state-conserved-p s1 s2 s3)
                 do (cl-incf conserved))
        (insert (format "  Triads:        %d\n" triads))
        (insert (format "  Conserved:     %d (%.1f%%)\n"
                        conserved
                        (if (> triads 0)
                            (* 100.0 (/ (float conserved) triads))
                          0.0))))
      (insert "\n")
      (insert "Key Bindings:\n")
      (insert "  C-c t         Main menu\n")
      (insert "  C-c C-n       Step forward\n")
      (insert "  C-c C-u       Step backward\n")
      (insert "  C-c C-a       Auto-prove\n")
      (insert "  C-c t c       Color menu\n")
      (insert "\n")
      (insert "Press q to close\n")
      (local-set-key (kbd "q") #'quit-window)
      (special-mode))
    (display-buffer buf)))

;; Bind to C-c t d
(with-eval-after-load 'transcendental-keyboard
  (define-key transcendental-keyboard-mode-map (kbd "C-c t d") #'trans-kb-show-dashboard))

;;; init-example.el ends here
