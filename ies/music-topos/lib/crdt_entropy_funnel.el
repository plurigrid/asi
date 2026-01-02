;;; crdt-entropy-funnel.el --- Keystroke/REPL Entropy → Gay Seed → CRDT Merge Priority -*- lexical-binding: t -*-

;; Copyright (C) 2025 Music Topos
;; Author: Plurigrid Tripartite System
;; Keywords: crdt, entropy, keystroke, misophonia, interstitial

;;; Commentary:

;; ENTROPY FUNNEL: Terminal interaction entropy seeds CRDT merge decisions
;;
;; Architecture (from misophonia → cognitive ignition isomorphism):
;;
;;   Terminal₁ ─── KTE (keystroke timing entropy) ───┐
;;                                                    ├──→ Entropy Funnel
;;   Terminal₂ ─── MVE (mouse velocity entropy) ─────┤       ↓
;;                                                    │  gay_seed(entropy)
;;   Terminal₃ ─── RHE (REPL hesitation entropy) ────┘       ↓
;;                                                     deterministic merge
;;
;; Key metrics (from M5_BEHAVIORAL_ENTROPY_IDENTIFICATION.md):
;;   - Keystroke timing: 5-8 bits (task-invariant)
;;   - Mouse velocity: 4-7 bits (task-invariant)
;;   - REPL hesitation: 3-6 bits (cognitive load signature)
;;
;; Signal vs Noise discrimination:
;;   - High entropy (>10 bits): Human cognitive engagement (signal)
;;   - Low entropy (<5 bits): Automated/bot traffic (noise)
;;   - Medium entropy: Requires additional context
;;
;; Integration with crdt_trifurcate.el:
;;   - Entropy seeds gay_seed for merge tiebreaking
;;   - GF(3) conservation applies to entropy-seeded operations
;;   - Self-avoiding walk ensures unique interaction paths

;;; Code:

(require 'cl-lib)

;; Load crdt_trifurcate from same directory (feature is 'crdt-trifurcate)
(let ((dir (file-name-directory (or load-file-name buffer-file-name))))
  (load (expand-file-name "crdt_trifurcate.el" dir) nil t))

;;;; Constants

(defconst crdt-entropy-funnel-kte-bins 40
  "Number of bins for keystroke timing histogram (50ms each, 0-2000ms).")

(defconst crdt-entropy-funnel-mve-bins 50
  "Number of bins for mouse velocity histogram (20 px/sec each, 0-1000 px/sec).")

(defconst crdt-entropy-funnel-signal-threshold 10.0
  "Entropy bits threshold: above = human signal, below = possible automation.")

(defconst crdt-entropy-funnel-noise-threshold 5.0
  "Entropy bits threshold: below = likely bot/background radiation.")

;;;; Data Structures

(cl-defstruct (crdt-entropy-terminal (:constructor crdt-entropy-terminal--create))
  "Terminal with entropy measurement capabilities."
  (id nil :type string)
  (keystroke-times nil :type list)      ; List of (timestamp . key) pairs
  (repl-intervals nil :type list)       ; Time between eval and next input
  (correction-events nil :type list)    ; Backspace bursts
  (expression-depths nil :type list)    ; Nesting depth trajectory
  (entropy-history nil :type list)      ; Running entropy calculations
  (last-active nil :type number)
  (gay-seed nil :type integer)
  (trit nil :type integer))

(cl-defstruct (crdt-entropy-measurement (:constructor crdt-entropy-measurement--create))
  "Entropy measurement at a point in time."
  (timestamp nil :type number)
  (kte nil :type number)                ; Keystroke timing entropy
  (rhe nil :type number)                ; REPL hesitation entropy
  (cve nil :type number)                ; Correction velocity entropy
  (total nil :type number)              ; Combined entropy
  (classification nil :type symbol))    ; 'signal, 'noise, or 'ambiguous

;;;; Entropy Calculation (from M5 research)

(defun crdt-entropy-funnel--shannon-entropy (histogram)
  "Calculate Shannon entropy from HISTOGRAM (list of counts).
Returns entropy in bits: H = -Σ p_i log₂(p_i)"
  (let* ((total (float (apply #'+ histogram)))
         (probs (mapcar (lambda (c)
                          (if (> c 0)
                              (/ (float c) total)
                            0.0))
                        histogram))
         (entropy 0.0))
    (dolist (p probs)
      (when (> p 0)
        (setq entropy (- entropy (* p (log p 2))))))
    entropy))

(defun crdt-entropy-funnel--keystroke-timing-entropy (keystroke-times)
  "Calculate keystroke timing entropy from KEYSTROKE-TIMES.
Quantizes intervals into 50ms bins, calculates Shannon entropy."
  (when (>= (length keystroke-times) 2)
    (let* ((times (mapcar #'car keystroke-times))
           (intervals (cl-loop for (a b) on times by #'cdr
                               while b
                               collect (- b a)))
           (histogram (make-list crdt-entropy-funnel-kte-bins 0)))
      ;; Fill histogram (bin = interval / 50ms, capped at max bins)
      (dolist (interval intervals)
        (let ((bin (min (1- crdt-entropy-funnel-kte-bins)
                        (max 0 (floor interval 50)))))
          (cl-incf (nth bin histogram))))
      (crdt-entropy-funnel--shannon-entropy histogram))))

(defun crdt-entropy-funnel--repl-hesitation-entropy (repl-intervals)
  "Calculate REPL hesitation entropy from REPL-INTERVALS.
Time between result display and next input = cognitive processing time."
  (when (>= (length repl-intervals) 3)
    (let* ((histogram (make-list 20 0)))  ; 500ms bins, 0-10sec
      (dolist (interval repl-intervals)
        (let ((bin (min 19 (max 0 (floor interval 500)))))
          (cl-incf (nth bin histogram))))
      (crdt-entropy-funnel--shannon-entropy histogram))))

(defun crdt-entropy-funnel--correction-velocity-entropy (correction-events)
  "Calculate correction velocity entropy from CORRECTION-EVENTS.
Backspace bursts = syntactic confusion; slow deletions = conceptual revision."
  (when (>= (length correction-events) 3)
    (let* ((velocities (mapcar #'car correction-events))  ; corrections/sec
           (histogram (make-list 10 0)))  ; 1 c/s bins, 0-10 c/s
      (dolist (v velocities)
        (let ((bin (min 9 (max 0 (floor v)))))
          (cl-incf (nth bin histogram))))
      (crdt-entropy-funnel--shannon-entropy histogram))))

;;;; Terminal Management

(defvar crdt-entropy-funnel--terminals (make-hash-table :test 'equal)
  "Hash table of terminal-id → crdt-entropy-terminal.")

(defvar crdt-entropy-funnel--last-keystroke-time nil
  "Timestamp of last keystroke for interval calculation.")

(defvar crdt-entropy-funnel--last-eval-time nil
  "Timestamp of last REPL evaluation for hesitation calculation.")

(defun crdt-entropy-funnel-create-terminal (id)
  "Create and register a new entropy-measuring terminal with ID."
  (let ((terminal (crdt-entropy-terminal--create
                   :id id
                   :keystroke-times nil
                   :repl-intervals nil
                   :correction-events nil
                   :expression-depths nil
                   :entropy-history nil
                   :last-active (float-time)
                   :gay-seed crdt-trifurcate-seed-default
                   :trit 0)))
    (puthash id terminal crdt-entropy-funnel--terminals)
    terminal))

(defun crdt-entropy-funnel-get-terminal (id)
  "Get terminal by ID, creating if necessary."
  (or (gethash id crdt-entropy-funnel--terminals)
      (crdt-entropy-funnel-create-terminal id)))

;;;; Event Recording

(defun crdt-entropy-funnel-record-keystroke (terminal-id key)
  "Record keystroke event for TERMINAL-ID."
  (let* ((terminal (crdt-entropy-funnel-get-terminal terminal-id))
         (now (float-time))
         (times (crdt-entropy-terminal-keystroke-times terminal)))
    ;; Keep last 100 keystrokes for entropy calculation
    (setf (crdt-entropy-terminal-keystroke-times terminal)
          (cons (cons now key)
                (seq-take times 99)))
    (setf (crdt-entropy-terminal-last-active terminal) now)))

(defun crdt-entropy-funnel-record-repl-input (terminal-id)
  "Record REPL input event for TERMINAL-ID (user started typing after eval)."
  (let* ((terminal (crdt-entropy-funnel-get-terminal terminal-id))
         (now (float-time))
         (last-eval crdt-entropy-funnel--last-eval-time)
         (intervals (crdt-entropy-terminal-repl-intervals terminal)))
    (when last-eval
      (let ((hesitation (- now last-eval)))
        (setf (crdt-entropy-terminal-repl-intervals terminal)
              (cons hesitation (seq-take intervals 49)))))))

(defun crdt-entropy-funnel-record-eval (terminal-id)
  "Record REPL evaluation event for TERMINAL-ID."
  (setq crdt-entropy-funnel--last-eval-time (float-time)))

(defun crdt-entropy-funnel-record-correction (terminal-id velocity)
  "Record correction event with VELOCITY (deletions/sec) for TERMINAL-ID."
  (let* ((terminal (crdt-entropy-funnel-get-terminal terminal-id))
         (now (float-time))
         (events (crdt-entropy-terminal-correction-events terminal)))
    (setf (crdt-entropy-terminal-correction-events terminal)
          (cons (cons velocity now)
                (seq-take events 29)))))

;;;; Entropy Measurement

(defun crdt-entropy-funnel-measure (terminal-id)
  "Measure current entropy for TERMINAL-ID, return measurement struct."
  (let* ((terminal (crdt-entropy-funnel-get-terminal terminal-id))
         (now (float-time))
         (kte (or (crdt-entropy-funnel--keystroke-timing-entropy
                   (crdt-entropy-terminal-keystroke-times terminal))
                  0.0))
         (rhe (or (crdt-entropy-funnel--repl-hesitation-entropy
                   (crdt-entropy-terminal-repl-intervals terminal))
                  0.0))
         (cve (or (crdt-entropy-funnel--correction-velocity-entropy
                   (crdt-entropy-terminal-correction-events terminal))
                  0.0))
         ;; Combined entropy (weighted sum)
         (total (+ (* 0.5 kte) (* 0.3 rhe) (* 0.2 cve)))
         ;; Classification
         (class (cond
                 ((> total crdt-entropy-funnel-signal-threshold) 'signal)
                 ((< total crdt-entropy-funnel-noise-threshold) 'noise)
                 (t 'ambiguous)))
         (measurement (crdt-entropy-measurement--create
                       :timestamp now
                       :kte kte
                       :rhe rhe
                       :cve cve
                       :total total
                       :classification class)))
    ;; Record in history
    (push measurement (crdt-entropy-terminal-entropy-history terminal))
    measurement))

;;;; Gay Seed Derivation

(defun crdt-entropy-funnel-derive-gay-seed (measurement)
  "Derive gay_seed from MEASUREMENT using SplitMix64."
  (let* ((total (crdt-entropy-measurement-total measurement))
         (timestamp (crdt-entropy-measurement-timestamp measurement))
         ;; Combine entropy and timestamp for seed
         (combined (logxor
                    (floor (* total 1000000))
                    (floor (* timestamp 1000))))
         ;; SplitMix64 mixing
         (z combined)
         (z (logand (* (logxor z (ash z -30)) #xbf58476d1ce4e5b9)
                    crdt-trifurcate-mask64))
         (z (logand (* (logxor z (ash z -27)) #x94d049bb133111eb)
                    crdt-trifurcate-mask64))
         (z (logxor z (ash z -31))))
    (logand z crdt-trifurcate-mask64)))

(defun crdt-entropy-funnel-update-terminal-seed (terminal-id)
  "Update TERMINAL-ID's gay_seed from current entropy measurement."
  (let* ((terminal (crdt-entropy-funnel-get-terminal terminal-id))
         (measurement (crdt-entropy-funnel-measure terminal-id))
         (seed (crdt-entropy-funnel-derive-gay-seed measurement)))
    (setf (crdt-entropy-terminal-gay-seed terminal) seed)
    ;; Derive trit from seed
    (let* ((color-result (crdt-trifurcate-next-color seed))
           (color (cdr color-result))
           (trit (crdt-trifurcate-hue-to-trit (plist-get color :H))))
      (setf (crdt-entropy-terminal-trit terminal) trit))
    (list :seed seed
          :measurement measurement
          :terminal-id terminal-id)))

;;;; Entropy Funnel for Merge Decisions

(cl-defstruct (crdt-entropy-funnel (:constructor crdt-entropy-funnel--create))
  "Funnel aggregating entropy from multiple terminals for merge decisions."
  (terminal-ids nil :type list)
  (measurements nil :type list)
  (aggregated-seed nil :type integer)
  (merge-priority nil :type list)       ; Terminal IDs sorted by priority
  (signal-count 0 :type integer)
  (noise-count 0 :type integer))

(defun crdt-entropy-funnel-create (terminal-ids)
  "Create entropy funnel for TERMINAL-IDS."
  (let* ((measurements (mapcar
                        (lambda (tid)
                          (cons tid (crdt-entropy-funnel-measure tid)))
                        terminal-ids))
         (signals (cl-count 'signal measurements
                            :key (lambda (m)
                                   (crdt-entropy-measurement-classification (cdr m)))))
         (noises (cl-count 'noise measurements
                           :key (lambda (m)
                                  (crdt-entropy-measurement-classification (cdr m)))))
         ;; Aggregate seed: XOR all individual seeds
         (seeds (mapcar
                 (lambda (m)
                   (crdt-entropy-funnel-derive-gay-seed (cdr m)))
                 measurements))
         (agg-seed (cl-reduce #'logxor seeds))
         ;; Priority: sort by total entropy descending (high entropy = more human)
         (priority (mapcar #'car
                           (cl-sort (copy-sequence measurements)
                                    #'>
                                    :key (lambda (m)
                                           (crdt-entropy-measurement-total (cdr m)))))))
    (crdt-entropy-funnel--create
     :terminal-ids terminal-ids
     :measurements measurements
     :aggregated-seed agg-seed
     :merge-priority priority
     :signal-count signals
     :noise-count noises)))

(defun crdt-entropy-funnel-merge-tiebreak (funnel)
  "Use FUNNEL's aggregated seed to break ties in CRDT merge.
Returns a color-based trit for deterministic resolution."
  (let* ((seed (crdt-entropy-funnel-aggregated-seed funnel))
         (color-result (crdt-trifurcate-next-color seed))
         (color (cdr color-result))
         (trit (crdt-trifurcate-hue-to-trit (plist-get color :H))))
    (list :trit trit
          :color color
          :seed seed
          :priority (crdt-entropy-funnel-merge-priority funnel)
          :signal-ratio (/ (float (crdt-entropy-funnel-signal-count funnel))
                          (max 1 (length (crdt-entropy-funnel-terminal-ids funnel)))))))

;;;; Integration with crdt-trifurcate

(defun crdt-entropy-funnel-integrate-with-agent (agent terminal-id)
  "Integrate entropy funnel with AGENT for TERMINAL-ID.
Updates agent's seed based on terminal's interaction entropy."
  (let* ((result (crdt-entropy-funnel-update-terminal-seed terminal-id))
         (seed (plist-get result :seed))
         (measurement (plist-get result :measurement)))
    ;; Update agent's seed chain
    (setf (crdt-agent-seed agent)
          (logand (logxor (crdt-agent-seed agent) seed)
                  crdt-trifurcate-mask64))
    (list :agent-id (crdt-agent-id agent)
          :new-seed (crdt-agent-seed agent)
          :entropy-class (crdt-entropy-measurement-classification measurement)
          :entropy-total (crdt-entropy-measurement-total measurement))))

;;;; Signal/Noise Discrimination for Interstitial Re-Weaving

(defun crdt-entropy-funnel-filter-by-signal (terminal-ids)
  "Filter TERMINAL-IDS to only those with signal-level entropy.
This re-densifies the interstitial by excluding bot traffic."
  (cl-remove-if
   (lambda (tid)
     (let ((m (crdt-entropy-funnel-measure tid)))
       (eq (crdt-entropy-measurement-classification m) 'noise)))
   terminal-ids))

(defun crdt-entropy-funnel-interstitial-density (terminal-ids)
  "Calculate interstitial density metric for TERMINAL-IDS.
Higher = more genuine human connections, lower = sparser/more automated."
  (let* ((measurements (mapcar #'crdt-entropy-funnel-measure terminal-ids))
         (signals (cl-count 'signal measurements
                            :key #'crdt-entropy-measurement-classification))
         (total (length terminal-ids))
         (avg-entropy (/ (cl-reduce #'+
                                    (mapcar #'crdt-entropy-measurement-total
                                            measurements))
                        (max 1.0 (float total)))))
    (list :density (/ (float signals) (max 1 total))
          :signal-count signals
          :total-count total
          :average-entropy avg-entropy
          :health (cond
                   ((> (/ (float signals) (max 1 total)) 0.7) 'healthy)
                   ((> (/ (float signals) (max 1 total)) 0.3) 'degraded)
                   (t 'sparse)))))

;;;; Emacs Integration Hooks

(defvar crdt-entropy-funnel-mode nil
  "Non-nil if entropy funnel mode is active.")

(defvar crdt-entropy-funnel-current-terminal "emacs-default"
  "Current terminal ID for entropy recording.")

(defun crdt-entropy-funnel--post-command-hook ()
  "Hook to record keystrokes after each command."
  (when crdt-entropy-funnel-mode
    (when (eq this-command 'self-insert-command)
      (crdt-entropy-funnel-record-keystroke
       crdt-entropy-funnel-current-terminal
       last-command-event))
    (when (memq this-command '(delete-backward-char backward-delete-char-untabify))
      (crdt-entropy-funnel-record-correction
       crdt-entropy-funnel-current-terminal
       1.0))))  ; Simplified: 1 correction per event

(defun crdt-entropy-funnel-mode-enable ()
  "Enable entropy funnel mode."
  (interactive)
  (setq crdt-entropy-funnel-mode t)
  (add-hook 'post-command-hook #'crdt-entropy-funnel--post-command-hook)
  (message "Entropy funnel enabled for terminal: %s"
           crdt-entropy-funnel-current-terminal))

(defun crdt-entropy-funnel-mode-disable ()
  "Disable entropy funnel mode."
  (interactive)
  (setq crdt-entropy-funnel-mode nil)
  (remove-hook 'post-command-hook #'crdt-entropy-funnel--post-command-hook)
  (message "Entropy funnel disabled"))

;;;; Demo

(defun crdt-entropy-funnel-demo ()
  "Demonstrate entropy funnel with simulated terminals."
  (interactive)
  (let* ((result-buffer (get-buffer-create "*Entropy Funnel Demo*")))
    (with-current-buffer result-buffer
      (erase-buffer)
      (insert "")
      (insert "  ENTROPY FUNNEL: Keystroke → Gay Seed → CRDT Merge  \n")
      (insert "\n\n")

      ;; Create simulated terminals with different entropy profiles
      (insert "--- Simulating 3 Terminals ---\n\n")

      ;; Terminal A: High entropy (human)
      (let ((t-a (crdt-entropy-funnel-create-terminal "terminal-A")))
        (dotimes (i 50)
          (setf (crdt-entropy-terminal-keystroke-times t-a)
                (cons (cons (+ (* i 0.15) (random 0.1)) ?a)
                      (crdt-entropy-terminal-keystroke-times t-a))))
        (dotimes (i 10)
          (push (+ 1.0 (random 3.0))
                (crdt-entropy-terminal-repl-intervals t-a))))

      ;; Terminal B: Medium entropy
      (let ((t-b (crdt-entropy-funnel-create-terminal "terminal-B")))
        (dotimes (i 30)
          (setf (crdt-entropy-terminal-keystroke-times t-b)
                (cons (cons (* i 0.2) ?b)
                      (crdt-entropy-terminal-keystroke-times t-b))))
        (dotimes (i 5)
          (push 0.5
                (crdt-entropy-terminal-repl-intervals t-b))))

      ;; Terminal C: Low entropy (bot-like)
      (let ((t-c (crdt-entropy-funnel-create-terminal "terminal-C")))
        (dotimes (i 20)
          (setf (crdt-entropy-terminal-keystroke-times t-c)
                (cons (cons (* i 0.1) ?c)
                      (crdt-entropy-terminal-keystroke-times t-c)))))

      ;; Measure each terminal
      (dolist (tid '("terminal-A" "terminal-B" "terminal-C"))
        (let ((m (crdt-entropy-funnel-measure tid)))
          (insert (format "  %s:\n" tid))
          (insert (format "    KTE: %.2f bits\n" (crdt-entropy-measurement-kte m)))
          (insert (format "    RHE: %.2f bits\n" (crdt-entropy-measurement-rhe m)))
          (insert (format "    Total: %.2f bits\n" (crdt-entropy-measurement-total m)))
          (insert (format "    Class: %s\n\n"
                          (crdt-entropy-measurement-classification m)))))

      ;; Create funnel
      (insert "--- Entropy Funnel ---\n\n")
      (let* ((funnel (crdt-entropy-funnel-create
                      '("terminal-A" "terminal-B" "terminal-C")))
             (tiebreak (crdt-entropy-funnel-merge-tiebreak funnel)))
        (insert (format "  Aggregated seed: 0x%x\n"
                        (crdt-entropy-funnel-aggregated-seed funnel)))
        (insert (format "  Merge priority: %s\n"
                        (crdt-entropy-funnel-merge-priority funnel)))
        (insert (format "  Signal/Noise: %d/%d\n"
                        (crdt-entropy-funnel-signal-count funnel)
                        (crdt-entropy-funnel-noise-count funnel)))
        (insert (format "\n  Tiebreak decision:\n"))
        (insert (format "    Trit: %+d\n" (plist-get tiebreak :trit)))
        (insert (format "    Color H: %.1f\n"
                        (plist-get (plist-get tiebreak :color) :H)))
        (insert (format "    Signal ratio: %.2f\n"
                        (plist-get tiebreak :signal-ratio))))

      ;; Interstitial density
      (insert "\n--- Interstitial Health ---\n\n")
      (let ((density (crdt-entropy-funnel-interstitial-density
                      '("terminal-A" "terminal-B" "terminal-C"))))
        (insert (format "  Density: %.2f\n" (plist-get density :density)))
        (insert (format "  Average entropy: %.2f bits\n"
                        (plist-get density :average-entropy)))
        (insert (format "  Health: %s\n" (plist-get density :health))))

      (insert "\n\n")
      (insert "Entropy funnel converts terminal interaction patterns\n")
      (insert "into deterministic gay_seed for CRDT merge decisions.\n")
      (insert "High entropy = human signal, Low entropy = noise/bots.\n")
      (insert "\n")

      (goto-char (point-min)))
    (display-buffer result-buffer)))

(provide 'crdt-entropy-funnel)

;;; crdt-entropy-funnel.el ends here
