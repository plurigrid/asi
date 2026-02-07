# Transcendental Keyboard Control Surface

**Unified Emacs keyboard interface for proof environments with Gay.jl color feedback**

## Quick Start (30 seconds)

```elisp
;; 1. Load the package
(add-to-list 'load-path "~/asi/skills/transcendental-keyboard")
(require 'transcendental-keyboard)

;; 2. Enable the mode
(transcendental-keyboard-mode 1)

;; 3. Press C-c t for main menu
```

## What You Get

### ✅ Unified Control Surface
- **Proof General** - Coq, Lean, Agda, Narya integration
- **Stellogen** - Transcendental syntax execution
- **Narya** - Observational bridge type templates
- **Gay.jl** - Deterministic color feedback

### ✅ Visual State Feedback
```
Mode-line colors indicate proof state:
  🔴 RED    - Unproved (GF(3) trit: -1)
  🟡 YELLOW - Processing (GF(3) trit: 0)
  🟢 GREEN  - Proved (GF(3) trit: +1)
```

### ✅ Self-Operating Proofs
```
C-c C-a → Auto-prove with:
  - reflexivity
  - intro
  - split
  - assumption
  - exact rfl
  ...
```

## Key Bindings

| Key | Action |
|-----|--------|
| `C-c t` | Main control panel |
| `C-c C-n` | Step forward in proof |
| `C-c C-u` | Step backward |
| `C-c C-a` | Auto-prove current goal |
| `C-c t c` | Color menu |
| `C-c t s` | Stellogen menu |

## Installation

### Dependencies

```bash
# Proof General
git clone https://github.com/ProofGeneral/PG ~/.emacs.d/proof-general

# Gay.jl color integration
curl -O https://raw.githubusercontent.com/bmorphism/Gay.jl/main/gay.el
mv gay.el ~/.emacs.d/
```

### Emacs Config

```elisp
;; Add to init.el
(use-package gay
  :load-path "~/.emacs.d/"
  :config (setq gay-seed 1069))

(use-package transcendental-keyboard
  :load-path "~/asi/skills/transcendental-keyboard"
  :after (gay proof-site)
  :hook ((coq-mode lean-mode) . transcendental-keyboard-mode)
  :config
  (setq trans-kb-color-mode t)
  (setq trans-kb-auto-save t))
```

## Example: Narya Proof

```narya
-- bridge_example.ny

def add_comm (m n : Nat) : add m n ≡ add n m := {
  -- 1. C-c C-n to step forward
  --    Mode-line: 🔴 → 🟡 → 🟢
  --
  -- 2. C-c C-a to auto-prove
  --    ✅ Auto-proved with: reflexivity
}
```

## GF(3) Conservation

Every proof trajectory conserves GF(3):

```
Σ (state_i mod 3) ≡ 0 (mod 3)

Example: [proved, unproved, unproved, proved]
         (+1)    + (-1)     + (-1)     + (+1) = 0 ✓
```

Check with: `M-x trans-kb-analyze-conservation`

## Architecture

```
User Keyboard
     ↓
Transient Menu (C-c t)
     ↓
   ┌─┴─┬─────┬──────┐
   ↓   ↓     ↓      ↓
 Proof Stelle Narya Gay.jl
 Gen   gen   Bridge Colors
   └───┴─────┴──────┘
         ↓
   Mode-line Color
```

## Status

- [x] Proof General integration ✓
- [x] Stellogen execution ✓
- [x] Narya templates ✓
- [x] Gay.jl color feedback ✓
- [x] Auto-prove tactics ✓
- [x] GF(3) conservation tracking ✓
- [x] Transient menus ✓

**Ready for production** 🚀

## Documentation

- **Full spec**: [SKILL.md](SKILL.md)
- **Proof General**: [Skills: proofgeneral-narya](../proofgeneral-narya/SKILL.md)
- **Stellogen**: [Skills: stellogen](../stellogen/SKILL.md)
- **Gay.jl**: [~/i/gay.el](../../../gay.el)

**Ω**
