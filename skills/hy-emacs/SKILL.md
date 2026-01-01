---
name: hy-emacs
description: Hylang Emacs integration with hy-mode, Hyuga LSP, and DisCoPy sexp coloring
trit: 0
polarity: ERGODIC
---

# hy-emacs - Hylang Emacs Integration

> **Trit**: 0 (ERGODIC - Coordinator)
>
> Complete Hy development environment for Emacs with LSP, REPL,
> and deterministic sexp coloring via Gay.jl patterns.

## Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                    Hy → Emacs → LSP Pipeline                    │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│   .hy files                 Hyuga LSP              Gay.jl       │
│      │                         │                      │         │
│      ▼                         ▼                      ▼         │
│  ┌────────┐    ┌───────────────────────────┐    ┌──────────┐   │
│  │hy-mode │───▶│ completion, diagnostics,  │───▶│ rainbow  │   │
│  │ (MELPA)│    │ hover, go-to-definition   │    │ parens   │   │
│  └────────┘    └───────────────────────────┘    └──────────┘   │
│      │                         │                      │         │
│      │         jedhy           │                      │         │
│      ▼         (IDE)           ▼                      ▼         │
│  ┌────────┐    ┌───────────────────────────┐    ┌──────────┐   │
│  │hy-shell│───▶│ company-mode, eldoc-mode  │───▶│ depth→   │   │
│  │ (REPL) │    │ hy-describe-thing-at-pt   │    │ color    │   │
│  └────────┘    └───────────────────────────┘    └──────────┘   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## Triadic Structure

| Role | Component | Trit | Function |
|------|-----------|------|----------|
| **Validator** | slime-lisp | -1 | Common Lisp reference semantics |
| **Coordinator** | hy-emacs | 0 | Hy ↔ Python ↔ Emacs bridge |
| **Generator** | geiser-chicken | +1 | Scheme REPL with SplitMixTernary |

**GF(3) Conservation**: `slime-lisp (-1) ⊗ hy-emacs (0) ⊗ geiser-chicken (+1) = 0 ✓`

## Installation

### 1. Install Hyuga LSP

```bash
# Via pipx (recommended)
pipx install hyuga

# Or pip in venv
pip install hyuga

# Verify
hyuga --version  # Should show 1.0.0+
```

### 2. Install hy-mode (Emacs)

```elisp
;; From MELPA
M-x package-install RET hy-mode RET

;; Install jedhy for IDE features
;; In your Python environment:
;; pip install jedhy
```

### 3. Configure lsp-mode

```elisp
;; ~/.emacs.d/init.el or ~/.doom.d/config.el

(use-package hy-mode
  :ensure t
  :mode "\\.hy\\'"
  :hook ((hy-mode . company-mode)
         (hy-mode . eldoc-mode)
         (hy-mode . rainbow-delimiters-mode))
  :config
  (setq hy-jedhy--enable? t))

;; LSP via Hyuga
(use-package lsp-mode
  :ensure t
  :hook (hy-mode . lsp-deferred)
  :config
  ;; Register Hy language
  (add-to-list 'lsp-language-id-configuration '(hy-mode . "hy"))
  
  ;; Register Hyuga client
  (lsp-register-client
   (make-lsp-client
    :new-connection (lsp-stdio-connection "hyuga")
    :activation-fn (lsp-activate-on "hy")
    :server-id 'hyuga
    :priority -1)))

;; Rainbow delimiters with Gay.jl colors
(use-package rainbow-delimiters
  :ensure t
  :config
  (setq rainbow-delimiters-max-face-count 12)
  ;; Gay.jl golden angle palette
  (custom-set-faces
   '(rainbow-delimiters-depth-1-face ((t (:foreground "#FF6B6B"))))  ; 0°
   '(rainbow-delimiters-depth-2-face ((t (:foreground "#4ECDC4"))))  ; 137.5°
   '(rainbow-delimiters-depth-3-face ((t (:foreground "#FFE66D"))))  ; 275°
   '(rainbow-delimiters-depth-4-face ((t (:foreground "#95E1D3"))))  ; 52.5°
   '(rainbow-delimiters-depth-5-face ((t (:foreground "#F38181"))))  ; 190°
   '(rainbow-delimiters-depth-6-face ((t (:foreground "#AA96DA"))))  ; 327.5°
   '(rainbow-delimiters-depth-7-face ((t (:foreground "#FCBAD3"))))  ; 105°
   '(rainbow-delimiters-depth-8-face ((t (:foreground "#A8D8EA"))))  ; 242.5°
   '(rainbow-delimiters-depth-9-face ((t (:foreground "#FFFFD2"))))  ; 20°
   '(rainbow-delimiters-depth-10-face ((t (:foreground "#B5EAEA")))) ; 157.5°
   '(rainbow-delimiters-depth-11-face ((t (:foreground "#EAB5E2")))) ; 295°
   '(rainbow-delimiters-depth-12-face ((t (:foreground "#C9E4CA")))))); 72.5°
```

## Doom Emacs Configuration

```elisp
;; ~/.doom.d/packages.el
(package! hy-mode)
(package! rainbow-delimiters)

;; ~/.doom.d/config.el
(use-package! hy-mode
  :mode "\\.hy\\'"
  :config
  (setq hy-jedhy--enable? t)
  
  ;; LSP
  (after! lsp-mode
    (add-to-list 'lsp-language-id-configuration '(hy-mode . "hy"))
    (lsp-register-client
     (make-lsp-client
      :new-connection (lsp-stdio-connection "hyuga")
      :activation-fn (lsp-activate-on "hy")
      :server-id 'hyuga))))

(add-hook! 'hy-mode-hook
  #'rainbow-delimiters-mode
  #'lsp!)
```

## Spacemacs Layer

```elisp
;; ~/.spacemacs.d/layers/hy/packages.el
(defconst hy-packages '(hy-mode rainbow-delimiters))

(defun hy/init-hy-mode ()
  (use-package hy-mode
    :mode "\\.hy\\'"
    :init
    (add-hook 'hy-mode-hook #'lsp)
    :config
    (spacemacs/set-leader-keys-for-major-mode 'hy-mode
      "'" 'hy-shell-start-or-switch-to-shell
      "sb" 'hy-shell-eval-buffer
      "sr" 'hy-shell-eval-region
      "sf" 'hy-shell-eval-current-form)))
```

## UREPL Integration

Connect Hy to the unified REPL coordinator:

```elisp
;; hy-urepl-bridge.el

(defun hy-urepl-eval (code)
  "Send Hy code to UREPL coordinator."
  (let ((msg `(:type :eval
               :lang :hy
               :code ,code
               :timestamp ,(float-time))))
    (urepl-send-message msg)))

(defun hy-urepl-connect ()
  "Connect to UREPL server."
  (interactive)
  (setq urepl-connection
        (open-network-stream "urepl" "*urepl*" "localhost" 7888))
  (message "Connected to UREPL"))

;; Integration with hy-mode
(defun hy-eval-to-urepl ()
  "Evaluate current form via UREPL."
  (interactive)
  (let ((code (hy-shell--current-form-string)))
    (hy-urepl-eval code)))

(define-key hy-mode-map (kbd "C-c C-u") #'hy-eval-to-urepl)
```

## DisCoPy Sexp Coloring

For categorical diagram coloring in Hy files:

```elisp
;; discopy-hy-colors.el

(defun discopy-color-sexp (depth)
  "Return Gay.jl color for sexp at DEPTH."
  (let* ((golden-angle 137.508)
         (hue (mod (* depth golden-angle) 360))
         (sat 0.7)
         (lum 0.55))
    (color-hsl-to-rgb (/ hue 360.0) sat lum)))

(defun discopy-fontify-sexps ()
  "Apply DisCoPy coloring to all sexps in buffer."
  (interactive)
  (save-excursion
    (goto-char (point-min))
    (let ((depth 0))
      (while (not (eobp))
        (cond
         ((looking-at "(")
          (let ((color (discopy-color-sexp depth)))
            (put-text-property (point) (1+ (point))
                               'face `(:foreground ,color)))
          (setq depth (1+ depth)))
         ((looking-at ")")
          (setq depth (max 0 (1- depth)))
          (let ((color (discopy-color-sexp depth)))
            (put-text-property (point) (1+ (point))
                               'face `(:foreground ,color)))))
        (forward-char)))))

(add-hook 'hy-mode-hook
          (lambda ()
            (add-hook 'after-change-functions
                      (lambda (&rest _) (discopy-fontify-sexps))
                      nil t)))
```

## Ruler Configuration

Add to `.ruler/ruler.toml`:

```toml
[mcp_servers.hyuga]
command = "hyuga"
args = []
env = { HYRULE_MACROS = "true" }
description = "Hy Language Server for DisCoPy/ACSet sexp files"

[lsp.hy]
server = "hyuga"
filetypes = ["hy"]
root_markers = ["pyproject.toml", ".git", "setup.py"]
```

## Commands

```bash
# Start Hy REPL
just hy-repl

# Run Hy file
just hy-run lib/discohy.hy

# Check Hy syntax
just hy-check lib/*.hy

# Generate colors for Hy file
just hy-colors lib/discohy.hy

# Connect to UREPL
just urepl-hy
```

## Project Files

Your project has 24 Hy files in `lib/`:

| File | Purpose |
|------|---------|
| `discohy.hy` | DisCoPy + ACSet sexp traversal |
| `discohy_world.hy` | Word → World model bridges |
| `discohy_thread_operad.hy` | Thread operad composition |
| `interaction_entropy.hy` | Entropy-driven interleaving |
| `gay_world_ducklake.hy` | DuckDB + Gay.jl colors |
| `thread_duckdb_bridge.hy` | Thread ↔ DuckDB persistence |

## GF(3) Triads

```
# Lisp REPL Bundle
slime-lisp (-1) ⊗ hy-emacs (0) ⊗ geiser-chicken (+1) = 0 ✓

# Emacs Tool Bundle  
xenodium-elisp (-1) ⊗ hy-emacs (0) ⊗ cider-clojure (+1) = 0 ✓

# DisCoPy Integration Bundle
three-match (-1) ⊗ hy-emacs (0) ⊗ gay-mcp (+1) = 0 ✓

# LSP Configuration Bundle
polyglot-spi (-1) ⊗ hy-emacs (0) ⊗ gay-mcp (+1) = 0 ✓
```

## Key Bindings

| Key | Command | Description |
|-----|---------|-------------|
| `C-c C-z` | `hy-shell-start-or-switch` | Start/switch to REPL |
| `C-c C-c` | `hy-shell-eval-current-form` | Eval form at point |
| `C-c C-b` | `hy-shell-eval-buffer` | Eval entire buffer |
| `C-c C-r` | `hy-shell-eval-region` | Eval selected region |
| `C-c C-d` | `hy-describe-thing-at-point` | Show documentation |
| `C-c C-u` | `hy-jedhy-update-imports` | Update jedhy imports |
| `M-.` | `lsp-find-definition` | Go to definition |
| `M-?` | `lsp-find-references` | Find references |

## See Also

- `geiser-chicken` - Scheme REPL with SplitMixTernary
- `slime-lisp` - Common Lisp REPL
- `cider-clojure` - Clojure nREPL
- `xenodium-elisp` - Modern Emacs packages
- `discohy-streams` - DisCoPy categorical streams
- `uv-discohy` - UV toolchain for DiscoHy

## Dependencies

```yaml
python:
  - hy >= 1.0.0
  - hyuga >= 1.0.0
  - jedhy >= 0.1.0
  - hyrule >= 0.7.0

emacs:
  - hy-mode (MELPA)
  - lsp-mode (MELPA)
  - rainbow-delimiters (MELPA)
  - company (MELPA)
```



## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Graph Theory
- **networkx** [○] via bicomodule
  - Universal graph hub

### Bibliography References

- `general`: 734 citations in bib.duckdb

## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: ⊗
Kan Role: Adj
Color: #26D826
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

This ensures compositional coherence in the Cat# equipment structure.
