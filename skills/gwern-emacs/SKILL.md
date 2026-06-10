---
name: gwern-emacs
description: 'The Bitter Lesson: *General methods leveraging compute beat specialized methods.*'
---
# gwern-emacs Skill

> *Gwern's empirical rationality meets xenodium's Emacs philosophy*

## Core Synthesis

| Gwern Concept | Emacs Integration | Gay.jl Stream |
|---------------|-------------------|---------------|
| Spaced Repetition | org-drill, org-fc | Stream 2 `#E6F463` |
| Self-Experimentation | org-capture, sqlite-mode | Stream 4 `#5713C0` |
| Bitter Lesson | chatgpt-shell scaling | Stream 3 `#63B6F0` |
| Scaling Hypothesis | agent-shell hierarchies | Stream 2 `#E6F463` |
| Tool AI | acp.el + MCP servers | Stream 4 `#5713C0` |

## Spaced Repetition in Emacs

```elisp
(use-package org-fc
  :custom
  (org-fc-directories '("~/org/flashcards/"))
  :config
  ;; Gwern-style forgetting curve with Gay.jl colors
  (defun gwern/org-fc-colorize-by-interval ()
    "Color cards by retention interval using stream 2 colors."
    (let* ((interval (org-fc-card-interval))
           (index (min 6 (floor (/ interval 7))))  ; Week-based indexing
           (colors ["#E6F463" "#73A0E1" "#D87E0E" 
                    "#D72676" "#D13FD6" "#7FD971" "#5BCCB1"]))
      (overlay-put (make-overlay (point) (line-end-position))
                   'face `(:background ,(aref colors index))))))
```

## Self-Experimentation Protocol

### Org-Capture for n=1 Studies

```elisp
(add-to-list 'org-capture-templates
  '("e" "Self-Experiment" entry
    (file+headline "~/org/experiments.org" "Active")
    "* %^{Experiment} :experiment:
:PROPERTIES:
:HYPOTHESIS: %^{Hypothesis}
:START_DATE: %U
:BLINDING: %^{Blinding method}
:MEASURE: %^{Primary measure}
:GAY_SEED: %(format \"%x\" (random (expt 2 64)))
:END:
** Protocol
%?
** Data Log
| Date | Measure | Notes |
|------+---------+-------|
** Analysis
** Conclusion"
    :jump-to-captured t))
```

### sqlite-mode-extras for Experiment Data

```elisp
(defun gwern/experiment-db (experiment-name)
  "Open or create SQLite DB for experiment tracking."
  (let ((db-path (expand-file-name 
                  (format "experiments/%s.db" experiment-name)
                  org-directory)))
    (unless (file-exists-p db-path)
      (with-temp-buffer
        (sqlite-mode-open db-path)
        (sqlite-mode-extras-execute
         "CREATE TABLE observations (
            id INTEGER PRIMARY KEY,
            timestamp TEXT DEFAULT CURRENT_TIMESTAMP,
            measure REAL,
            condition TEXT,
            notes TEXT,
            gay_color TEXT
          )")))
    (sqlite-mode-open db-path)))
```

## Bitter Lesson → chatgpt-shell

The Bitter Lesson: *General methods leveraging compute beat specialized methods.*

### Scaling-Aware Model Selection

```elisp
(defun gwern/bitter-lesson-model-select ()
  "Select model based on task complexity using scaling heuristics.
   
   Simple tasks → small models (efficiency)
   Complex tasks → largest available (Bitter Lesson)"
  (interactive)
  (let* ((task-complexity (read-number "Task complexity (1-10): "))
         (model (cond
                 ((< task-complexity 3) "gpt-4o-mini")
                 ((< task-complexity 6) "gpt-4o")
                 ((< task-complexity 8) "claude-3-5-sonnet")
                 (t "o1-preview")))
         (bitter-color (if (>= task-complexity 6) "#63B6F0" "#D1E598")))
    (setq chatgpt-shell-model-version model)
    (message "Bitter Lesson applied: %s (complexity %d)" model task-complexity)))
```

### Compute Budget Tracking

```elisp
(defvar gwern/compute-budget nil
  "Track API costs as empirical data on scaling returns.")

(defun gwern/log-api-call (model tokens cost)
  "Log API call for meta-analysis of scaling efficiency."
  (push (list :time (current-time)
              :model model
              :tokens tokens
              :cost cost
              :gay-color (gay-color-at gay-seed-default 
                                       (mod (sxhash model) 1000)))
        gwern/compute-budget))
```

## Tool AI → acp.el Integration

Gwern's Tool AI concept: *AI as augmentation, not replacement.*

```elisp
;; Tool AI philosophy in agent configuration
(acp-define-agent "gwern-tool-ai"
  :system-prompt "You are a Tool AI assistant. Your role is to:
1. Augment human decision-making, not replace it
2. Provide information and analysis on request
3. Never take autonomous actions without explicit approval
4. Flag uncertainty and limitations clearly
5. Support empirical self-experimentation"
  
  :tools '((:name "search-gwern"
            :description "Search gwern.net for relevant content"
            :parameters ((:name "query" :type "string")))
           (:name "log-observation"
            :description "Log self-experiment observation"
            :parameters ((:name "experiment" :type "string")
                        (:name "measure" :type "number")
                        (:name "notes" :type "string")))
           (:name "gay-color"
            :description "Get deterministic color for concept"
            :parameters ((:name "concept" :type "string")))))
```

## dwim-shell-command for Gwern-Style Analysis

```elisp
(dwim-shell-command-define
 :name "Gwern: N-gram analysis"
 :command "python3 -c \"
import sys
from collections import Counter
text = open('<<f>>').read()
ngrams = [text[i:i+3] for i in range(len(text)-2)]
for ng, count in Counter(ngrams).most_common(20):
    print(f'{count:>5} {ng!r}')
\""
 :utils "python3"
 :documentation "Character n-gram analysis for text patterns")

(dwim-shell-command-define
 :name "Gwern: Effect size"
 :command "python3 -c \"
import sys, numpy as np
a = np.array([float(x) for x in input('Control: ').split()])
b = np.array([float(x) for x in input('Treatment: ').split()])
pooled_std = np.sqrt((a.var() + b.var()) / 2)
cohens_d = (b.mean() - a.mean()) / pooled_std
print(f'Cohen\\'s d: {cohens_d:.3f}')
print('Effect: ' + ('small' if abs(cohens_d)<0.5 else 'medium' if abs(cohens_d)<0.8 else 'large'))
\""
 :utils "python3"
 :documentation "Calculate effect size for self-experiments")
```

## Gay.jl Color Integration

Each Gwern concept has a deterministic color stream:

```elisp
(defvar gwern/concept-colors
  '((spaced-rep . (:stream 2 :seed #x15de8b98c900de7 :color "#E6F463"))
    (self-experiment . (:stream 4 :seed #x334251d97027eb15 :color "#5713C0"))
    (bitter-lesson . (:stream 3 :seed #xb8976e5c302871c9 :color "#63B6F0"))
    (scaling . (:stream 2 :seed nil :color "#E6F463"))
    (tool-ai . (:stream 4 :seed nil :color "#5713C0"))
    (daydreaming . (:stream 5 :seed nil :color "#532FA6")))
  "Gwern concepts mapped to Gay.jl color streams.")

(defun gwern/concept-face (concept)
  "Get face for Gwern concept."
  (let ((color (plist-get (alist-get concept gwern/concept-colors) :color)))
    `(:background ,color :foreground ,(if (> (gwern/color-luminance color) 0.5)
                                          "black" "white"))))
```

## Transient Menu

```elisp
(transient-define-prefix gwern-transient ()
  "Gwern methodology commands."
  ["Experimentation"
   ("e" "New experiment" gwern/new-experiment)
   ("d" "Log data point" gwern/log-observation)
   ("a" "Analyze experiment" gwern/analyze-experiment)]
  ["Spaced Rep"
   ("r" "Review due cards" org-fc-review)
   ("s" "Schedule stats" org-fc-stats)]
  ["Scaling"
   ("m" "Model select (Bitter Lesson)" gwern/bitter-lesson-model-select)
   ("c" "Compute budget" gwern/show-compute-budget)]
  ["Tool AI"
   ("t" "Tool AI agent" (lambda () (interactive) (agent-shell "gwern-tool-ai")))
   ("g" "ChatGPT shell" chatgpt-shell)])

(global-set-key (kbd "C-c w") 'gwern-transient)
```

## Neighbor Skills

- **xenodium-elisp**: Core Emacs infrastructure (chatgpt-shell, acp.el, dwim-shell-command)
- **gay-mcp**: Deterministic color streams for concept tracking
- **compression-progress**: Schmidhuber's curiosity → Gwern's information-theoretic approach
- **self-validation-loop**: Empirical validation of predictions
- **duckdb-temporal-versioning**: Time-travel queries for experiment history

## Resources

- [gwern.net](https://gwern.net/) - Primary source
- [gwern.net/spaced-repetition](https://gwern.net/spaced-repetition) - SR meta-analysis
- [gwern.net/zeo](https://gwern.net/zeo) - Self-blinding experiments
- [gwern.net/scaling-hypothesis](https://gwern.net/scaling-hypothesis) - Scaling + Bitter Lesson


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
