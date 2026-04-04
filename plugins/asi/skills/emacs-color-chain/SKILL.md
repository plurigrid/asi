---
name: emacs-color-chain
description: Control Emacs via deterministic Gay-MCP color chains — seed-derived palettes drive buffer themes, mode-line, org headers, and window focus
version: 1.0.0
trit: 0
triggers:
  - emacs color chain
  - color-driven emacs
  - gay emacs
  - seed-driven emacs theme
dependencies:
  - gay-mcp
  - elisp
  - emacs
---

# Emacs Color Chain

Drive Emacs UI state from a SplitMix64 color chain. Same seed → same theme/mode-line/org-colors everywhere.

## Architecture

```
Seed (0x42D)
  │
  ├─ color_at(0) → mode-line face
  ├─ color_at(1) → cursor color
  ├─ color_at(2) → region highlight
  ├─ color_at(3..N) → org-level-{1..N} faces
  └─ trit sequence → window focus rotation
```

## Elisp: `gay-colors.el`

```elisp
;;; gay-colors.el --- SplitMix64 color chain for Emacs -*- lexical-binding: t -*-

(defvar gay-seed #x42D "Current color chain seed.")
(defvar gay-state nil "SplitMix64 internal state.")

(defconst gay--golden #x9E3779B97F4A7C15)
(defconst gay--mix1  #xBF58476D1CE4E5B9)
(defconst gay--mix2  #x94D049BB133111EB)
(defconst gay--mask  (1- (expt 2 64)))

(defun gay--u64* (a b)
  "Multiply A and B mod 2^64."
  (logand (* a b) gay--mask))

(defun gay--splitmix64 (state)
  "One SplitMix64 step. Returns (next-state . value)."
  (let* ((s (logand (+ state gay--golden) gay--mask))
         (z s)
         (z (gay--u64* (logxor z (ash z -30)) gay--mix1))
         (z (gay--u64* (logxor z (ash z -27)) gay--mix2))
         (z (logxor z (ash z -31))))
    (cons s z)))

(defun gay-color-at (seed index)
  "Deterministic color at INDEX from SEED. Returns (hex trit)."
  (let ((state seed))
    (dotimes (_ (1+ index))
      (let ((r (gay--splitmix64 state)))
        (setq state (car r))))
    (let* ((r1 (gay--splitmix64 state))
           (r2 (gay--splitmix64 (car r1)))
           (r3 (gay--splitmix64 (car r2)))
           (L (+ 25 (* (/ (float (logand (cdr r1) #xFFFF)) 65535.0) 50)))
           (H (* (/ (float (logand (cdr r2) #xFFFF)) 65535.0) 360.0))
           (S (* (/ (float (logand (cdr r3) #xFFFF)) 65535.0) 0.6))
           ;; Simple HSL→hex
           (trit (cond
                  ((or (< H 60) (> H 300)) 1)
                  ((< H 180) 0)
                  (t -1))))
      (list (gay--hsl-to-hex H S L) trit))))

(defun gay--hsl-to-hex (h s l)
  "Convert HSL to #RRGGBB hex string."
  (let* ((h (/ h 360.0))
         (c (* (- 1.0 (abs (- (* 2.0 (/ l 100.0)) 1.0))) s))
         (x (* c (- 1.0 (abs (- (mod (* h 6.0) 2.0) 1.0)))))
         (m (- (/ l 100.0) (/ c 2.0)))
         (h6 (* h 6.0))
         (rgb (cond
               ((< h6 1) (list c x 0))
               ((< h6 2) (list x c 0))
               ((< h6 3) (list 0 c x))
               ((< h6 4) (list 0 x c))
               ((< h6 5) (list x 0 c))
               (t        (list c 0 x)))))
    (format "#%02X%02X%02X"
            (round (* (+ (nth 0 rgb) m) 255))
            (round (* (+ (nth 1 rgb) m) 255))
            (round (* (+ (nth 2 rgb) m) 255)))))

(defun gay-apply-chain (&optional seed)
  "Apply color chain from SEED to Emacs faces."
  (interactive "nSeed (hex): ")
  (let ((seed (or seed gay-seed)))
    (setq gay-seed seed)
    (pcase-let* ((`(,ml-hex ,_)  (gay-color-at seed 0))
                 (`(,cur-hex ,_) (gay-color-at seed 1))
                 (`(,reg-hex ,_) (gay-color-at seed 2)))
      ;; Mode-line
      (set-face-attribute 'mode-line nil :background ml-hex)
      ;; Cursor
      (set-face-attribute 'cursor nil :background cur-hex)
      ;; Region
      (set-face-attribute 'region nil :background reg-hex)
      ;; Org levels
      (dotimes (i 8)
        (let* ((face (intern (format "org-level-%d" (1+ i))))
               (color-data (gay-color-at seed (+ 3 i)))
               (hex (car color-data)))
          (when (facep face)
            (set-face-attribute face nil :foreground hex))))
      (message "Color chain applied: seed=0x%X" seed))))

(defun gay-chain-next ()
  "Advance seed by chaining current trit and reapply."
  (interactive)
  (let* ((data (gay-color-at gay-seed 0))
         (trit (cadr data))
         (next (logand (+ gay-seed (* trit gay--golden)) gay--mask)))
    (gay-apply-chain next)))

(defun gay-trit-focus ()
  "Rotate window focus based on trit: +1=next, -1=prev, 0=stay."
  (interactive)
  (let ((trit (cadr (gay-color-at gay-seed 0))))
    (cond
     ((= trit 1)  (other-window 1))
     ((= trit -1) (other-window -1))
     (t (message "Ergodic: hold position")))))

(global-set-key (kbd "C-c g a") #'gay-apply-chain)
(global-set-key (kbd "C-c g n") #'gay-chain-next)
(global-set-key (kbd "C-c g f") #'gay-trit-focus)

(provide 'gay-colors)
;;; gay-colors.el ends here
```

## Keybindings

| Key | Action |
|-----|--------|
| `C-c g a` | Apply color chain from seed |
| `C-c g n` | Chain to next seed (trit-driven) |
| `C-c g f` | Trit-based window focus rotation |

## Install

```elisp
;; In init.el
(load "~/worlds/.agents/skills/emacs-color-chain/gay-colors.el")
(gay-apply-chain #x42D)
```

## Skill Triad

| Role | Skill | Trit |
|------|-------|------|
| Generator | gay-mcp | +1 |
| Coordinator | emacs-color-chain | 0 |
| Validator | elisp | -1 |
| **Sum** | | **0 ✓** |
