;;; gwern-emacs.el --- Gwern methodology in Emacs -*- lexical-binding: t -*-

;; Author: bmorphism
;; Keywords: tools, productivity, science
;; Package-Requires: ((emacs "29.1") (chatgpt-shell "0.98.0") (acp "0.1") (org-fc "0.3"))

;;; Commentary:
;; Implements Gwern's empirical rationality methods:
;; - Spaced repetition with forgetting curve visualization
;; - Self-experimentation with n=1 protocol tracking
;; - Bitter Lesson scaling heuristics for LLM selection
;; - Tool AI philosophy via acp.el agents

;;; Code:

(require 'cl-lib)
(require 'org)

;;; Gay.jl Color Integration

(defvar gwern-gay-seed #x15de8b98c900de7
  "Default Gay.jl seed for Gwern concept coloring.")

(defvar gwern-concept-streams
  '((spaced-rep . 2)
    (self-experiment . 4)
    (bitter-lesson . 3)
    (scaling . 2)
    (tool-ai . 4)
    (neural-art . 2)
    (daydreaming . 5))
  "Map Gwern concepts to Gay.jl color streams.")

(defvar gwern-stream-colors
  '((2 . ["#E6F463" "#73A0E1" "#D87E0E" "#D72676" "#D13FD6" "#7FD971" "#5BCCB1"])
    (3 . ["#63B6F0" "#89DF91" "#CF6971" "#8E9EDF" "#C25828" "#ED6BDB" "#D1E598"])
    (4 . ["#5713C0" "#D3E06F" "#C02982" "#5AE9DF" "#CB6354" "#916FE0" "#C4A512"])
    (5 . ["#532FA6" "#D3E06F" "#C02982" "#5AE9DF" "#CB6354" "#916FE0" "#C4A512"]))
  "Color arrays per stream from gwern_worlds JSON.")

(defun gwern-color-at (concept index)
  "Get color for CONCEPT at INDEX within its stream."
  (let* ((stream (alist-get concept gwern-concept-streams))
         (colors (alist-get stream gwern-stream-colors)))
    (aref colors (mod index (length colors)))))

;;; Spaced Repetition Integration

(defcustom gwern-sr-intervals '(1 2 4 7 14 30 60)
  "Spaced repetition intervals in days (based on Gwern's analysis)."
  :type '(repeat integer)
  :group 'gwern)

(defun gwern-sr-optimal-interval (ease factor)
  "Calculate optimal interval using EASE and retention FACTOR.
Based on Gwern's meta-analysis of forgetting curves."
  (let* ((base-interval (nth (min ease (1- (length gwern-sr-intervals)))
                             gwern-sr-intervals))
         (adjusted (* base-interval factor)))
    (round adjusted)))

;;; Self-Experimentation

(defvar gwern-experiments nil
  "Active self-experiments.")

(cl-defstruct gwern-experiment
  name hypothesis protocol start-date
  blinding-method measure observations
  gay-seed conclusion)

(defun gwern-new-experiment (name hypothesis)
  "Create new self-experiment with NAME and HYPOTHESIS."
  (interactive "sExperiment name: \nsHypothesis: ")
  (let ((exp (make-gwern-experiment
              :name name
              :hypothesis hypothesis
              :start-date (current-time)
              :gay-seed (random (expt 2 64))
              :observations nil)))
    (push exp gwern-experiments)
    (message "Created experiment: %s (seed: %x)"
             name (gwern-experiment-gay-seed exp))))

(defun gwern-log-observation (experiment measure &optional notes)
  "Log MEASURE for EXPERIMENT with optional NOTES."
  (interactive
   (list (completing-read "Experiment: "
                          (mapcar #'gwern-experiment-name gwern-experiments))
         (read-number "Measure: ")
         (read-string "Notes: ")))
  (let* ((exp (cl-find experiment gwern-experiments
                       :key #'gwern-experiment-name
                       :test #'string=))
         (obs (list :time (current-time)
                    :measure measure
                    :notes notes
                    :color (gwern-color-at 'self-experiment
                                           (length (gwern-experiment-observations exp))))))
    (push obs (gwern-experiment-observations exp))
    (message "Logged: %.2f for %s" measure experiment)))

;;; Bitter Lesson Model Selection

(defvar gwern-model-tiers
  '((1 . "gpt-4o-mini")
    (3 . "gpt-4o")
    (5 . "claude-3-5-sonnet")
    (7 . "claude-3-opus")
    (9 . "o1-preview"))
  "Model selection by task complexity (Bitter Lesson heuristic).")

(defun gwern-select-model-by-complexity (complexity)
  "Select model based on COMPLEXITY (1-10) using Bitter Lesson."
  (let ((tier (car (cl-find-if (lambda (pair) (>= complexity (car pair)))
                               (reverse gwern-model-tiers)))))
    (or (alist-get tier gwern-model-tiers) "gpt-4o")))

(defun gwern-bitter-lesson-prompt ()
  "Interactively select model using Bitter Lesson heuristics."
  (interactive)
  (let* ((complexity (read-number "Task complexity (1-10): " 5))
         (model (gwern-select-model-by-complexity complexity))
         (color (gwern-color-at 'bitter-lesson complexity)))
    (when (boundp 'chatgpt-shell-model-version)
      (setq chatgpt-shell-model-version model))
    (message "Bitter Lesson → %s (complexity %d, color %s)"
             model complexity color)))

;;; Tool AI Agent Definition

(defvar gwern-tool-ai-prompt
  "You are a Tool AI assistant following Gwern's principles:
1. AUGMENT human decision-making, never replace it
2. Provide information and analysis ON REQUEST only
3. NEVER take autonomous actions without explicit approval
4. Clearly FLAG uncertainty and limitations
5. Support EMPIRICAL self-experimentation with data logging
6. Apply the BITTER LESSON: prefer general methods + compute

Your role is to be a powerful tool that amplifies human capability
while keeping the human firmly in control of decisions."
  "System prompt for Tool AI agent.")

;;; Transient Interface

(require 'transient nil t)

(when (featurep 'transient)
  (transient-define-prefix gwern-transient ()
    "Gwern methodology commands."
    ["Self-Experimentation"
     ("e" "New experiment" gwern-new-experiment)
     ("o" "Log observation" gwern-log-observation)
     ("l" "List experiments" gwern-list-experiments)]
    ["Bitter Lesson"
     ("m" "Model by complexity" gwern-bitter-lesson-prompt)]
    ["Integration"
     ("c" "ChatGPT shell" chatgpt-shell :if (lambda () (fboundp 'chatgpt-shell)))
     ("a" "Agent shell" agent-shell :if (lambda () (fboundp 'agent-shell)))])
  
  (global-set-key (kbd "C-c w") 'gwern-transient))

(defun gwern-list-experiments ()
  "Display active experiments."
  (interactive)
  (with-current-buffer (get-buffer-create "*Gwern Experiments*")
    (erase-buffer)
    (insert "# Active Self-Experiments\n\n")
    (dolist (exp gwern-experiments)
      (insert (format "## %s\n" (gwern-experiment-name exp)))
      (insert (format "Hypothesis: %s\n" (gwern-experiment-hypothesis exp)))
      (insert (format "Observations: %d\n" (length (gwern-experiment-observations exp))))
      (insert (format "Seed: %x\n\n" (gwern-experiment-gay-seed exp))))
    (goto-char (point-min))
    (org-mode)
    (pop-to-buffer (current-buffer))))

(provide 'gwern-emacs)
;;; gwern-emacs.el ends here
