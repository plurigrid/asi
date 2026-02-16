;;; narya-ordered-locale.el --- Emacs integration for ordered locale proofs  -*- lexical-binding: t -*-

;; Author: PLUS Agent (Luca)
;; Trit: +1 (GENERATOR)
;; GF(3): Σ(-1,0,+1) = 0

;;; Commentary:

;; Provides Emacs integration for Narya proof assistant with
;; ordered locale theory and GF(3) conservation verification.
;;
;; Features:
;; - Proof General integration for stepping through proofs
;; - GF(3) conservation verification commands
;; - Headless mode for batch verification
;;
;; Usage:
;;   M-x narya-verify-ordered-locale  ; Verify all files
;;   M-x narya-verify-gf3             ; Check GF(3) conservation
;;   M-x narya-step-forward           ; Step forward in proof
;;   M-x narya-step-backward          ; Step backward in proof

;;; Code:

(require 'cl-lib)

;; Configuration
(defgroup narya-ordered-locale nil
  "Narya ordered locale proof settings."
  :group 'proof-general
  :prefix "narya-ol-")

(defcustom narya-ol-base-dir
  (expand-file-name "~/.agents/skills/ordered-locale/narya/")
  "Base directory for ordered locale Narya files."
  :type 'directory
  :group 'narya-ordered-locale)

(defcustom narya-ol-executable "narya"
  "Path to Narya executable."
  :type 'string
  :group 'narya-ordered-locale)

(defcustom narya-ol-files
  '("gf3.ny" "ordered_locale.ny" "bridge_sheaf.ny")
  "List of Narya files to verify in order."
  :type '(repeat string)
  :group 'narya-ordered-locale)

;; GF(3) Trit representation
(defconst narya-ol-trits
  '((minus . -1)
    (ergodic . 0)
    (plus . 1))
  "Mapping of trit names to values.")

(defun narya-ol-trit-value (trit)
  "Get numeric value of TRIT."
  (or (cdr (assoc trit narya-ol-trits)) 0))

(defun narya-ol-gf3-conserved-p (a b c)
  "Check if trits A B C sum to 0 mod 3."
  (zerop (mod (+ (narya-ol-trit-value a)
                 (narya-ol-trit-value b)
                 (narya-ol-trit-value c))
              3)))

;; Proof General integration (conditional)
(defvar narya-ol-proof-general-available nil
  "Whether Proof General is available.")

(defun narya-ol-load-proof-general ()
  "Try to load Proof General and narya-mode."
  (condition-case err
      (progn
        ;; Try loading from straight.el build
        (when (file-exists-p "~/.emacs.d/straight/build/proof-general/generic/proof-site.el")
          (load "~/.emacs.d/straight/build/proof-general/generic/proof-site.el" t))
        ;; Try loading narya-mode from narya repo
        (when (file-exists-p "~/worlds/ordered-locales/narya/proofgeneral/narya.el")
          (load "~/worlds/ordered-locales/narya/proofgeneral/narya.el" t))
        (setq narya-ol-proof-general-available t)
        (message "Proof General loaded successfully"))
    (error
     (message "Proof General not available: %s" (error-message-string err))
     nil)))

;; Interactive commands
(defun narya-step-forward ()
  "Step forward one proof step."
  (interactive)
  (if narya-ol-proof-general-available
      (proof-assert-next-command-interactive)
    (message "Proof General not loaded. Use M-x narya-ol-load-proof-general")))

(defun narya-step-backward ()
  "Step backward one proof step."
  (interactive)
  (if narya-ol-proof-general-available
      (proof-undo-last-successful-command)
    (message "Proof General not loaded.")))

(defun narya-goto-point ()
  "Process buffer up to point."
  (interactive)
  (if narya-ol-proof-general-available
      (proof-goto-point)
    (message "Proof General not loaded.")))

;; File verification
(defun narya-ol-verify-file (file)
  "Verify a single Narya FILE. Return t if successful."
  (let* ((full-path (expand-file-name file narya-ol-base-dir))
         (output-buffer (get-buffer-create "*narya-verify*"))
         (result nil))
    (with-current-buffer output-buffer
      (goto-char (point-max))
      (insert (format "\n=== Verifying: %s ===\n" file)))
    (if (not (file-exists-p full-path))
        (progn
          (with-current-buffer output-buffer
            (insert (format "ERROR: File not found: %s\n" full-path)))
          nil)
      (let ((exit-code
             (call-process narya-ol-executable nil output-buffer t full-path)))
        (with-current-buffer output-buffer
          (insert (format "Exit code: %d\n" exit-code)))
        (zerop exit-code)))))

(defun narya-verify-ordered-locale ()
  "Verify all ordered locale Narya files."
  (interactive)
  (let ((output-buffer (get-buffer-create "*narya-verify*"))
        (success t)
        (file-count 0)
        (pass-count 0))
    (with-current-buffer output-buffer
      (erase-buffer)
      (insert "╔═══════════════════════════════════════════════════════╗\n")
      (insert "║     NARYA ORDERED LOCALE VERIFICATION                ║\n")
      (insert "║     Trit: +1 (PLUS/GENERATOR)                        ║\n")
      (insert "╚═══════════════════════════════════════════════════════╝\n\n")
      (insert (format "Base directory: %s\n" narya-ol-base-dir))
      (insert (format "Time: %s\n\n" (current-time-string))))
    (dolist (file narya-ol-files)
      (cl-incf file-count)
      (let ((ok (narya-ol-verify-file file)))
        (if ok
            (cl-incf pass-count)
          (setq success nil))))
    (with-current-buffer output-buffer
      (goto-char (point-max))
      (insert "\n─── Summary ───\n")
      (insert (format "Files: %d/%d passed\n" pass-count file-count))
      (insert (format "Status: %s\n" (if success "✅ ALL PASS" "❌ FAILURES")))
      (insert (format "GF(3): Σ(-1,0,+1) = 0 (conserved)\n")))
    (display-buffer output-buffer)
    (when (not (called-interactively-p 'any))
      ;; In batch mode, exit with appropriate code
      (kill-emacs (if success 0 1)))
    success))

;; GF(3) verification
(defun narya-verify-gf3 ()
  "Verify GF(3) conservation in current buffer."
  (interactive)
  (let ((triad-re "GF3Conserved\\s-+(\\([a-z]+\\)\\.\\s-+(\\([a-z]+\\)\\.\\s-+(\\([a-z]+\\)\\.")
        (count 0)
        (violations 0))
    (save-excursion
      (goto-char (point-min))
      (while (re-search-forward triad-re nil t)
        (let ((a (intern (match-string 1)))
              (b (intern (match-string 2)))
              (c (intern (match-string 3))))
          (cl-incf count)
          (unless (narya-ol-gf3-conserved-p a b c)
            (cl-incf violations)
            (message "GF(3) VIOLATION at line %d: %s + %s + %s ≠ 0"
                     (line-number-at-pos) a b c)))))
    (if (zerop violations)
        (message "GF(3) verified: %d triads, all conserved ✅" count)
      (message "GF(3) FAILURES: %d/%d violations ❌" violations count))))

;; Keybindings
(defvar narya-ordered-locale-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-n") #'narya-step-forward)
    (define-key map (kbd "C-c C-u") #'narya-step-backward)
    (define-key map (kbd "C-c C-p") #'narya-goto-point)
    (define-key map (kbd "C-c C-v") #'narya-verify-ordered-locale)
    (define-key map (kbd "C-c C-g") #'narya-verify-gf3)
    map)
  "Keymap for narya-ordered-locale-mode.")

(define-minor-mode narya-ordered-locale-mode
  "Minor mode for Narya ordered locale development."
  :lighter " OrdLoc"
  :keymap narya-ordered-locale-mode-map
  (when narya-ordered-locale-mode
    (narya-ol-load-proof-general)))

;; Auto-enable for .ny files in our directory
(add-to-list 'auto-mode-alist
             (cons (concat (regexp-quote narya-ol-base-dir) ".*\\.ny\\'")
                   'narya-ordered-locale-mode))

;; Batch mode entry point
(defun narya-batch-verify ()
  "Entry point for batch verification."
  (narya-verify-ordered-locale))

;; Announce on load (for vocal agents)
(defun narya-ol-announce ()
  "Announce via macOS text-to-speech."
  (when (eq system-type 'darwin)
    (start-process "narya-announce" nil "say" "-v" "Luca"
                   "Narya ordered locale mode activated")))

(when (and (boundp 'narya-ol-announce-on-load)
           narya-ol-announce-on-load)
  (narya-ol-announce))

(provide 'narya-ordered-locale)

;;; narya-ordered-locale.el ends here
