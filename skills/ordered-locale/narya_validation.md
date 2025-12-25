# Narya Proof Assistant Validation Report

**Agent**: MINUS (-1) VALIDATOR  
**Voice**: Anna (German)  
**Date**: 2024-12-24  
**GF(3) Trit**: -1 (Validation/Verification)

---

## Summary

| Component | Status | Notes |
|-----------|--------|-------|
| Narya Binary | ❌ NOT INSTALLED | Not in PATH, flox, opam, nix-profile |
| Proof General | ❌ NOT INSTALLED | Not in ~/.emacs.d/elpa/ |
| narya.el | ✅ AVAILABLE | In upstream repo (mikeshulman/narya) |
| Emacs Headless | ✅ WORKS | `emacs --batch` functional |
| .ott Files | ❌ NONE FOUND | No .ott files in ~/worlds/ or codebase |
| .ny Files | ✅ IN UPSTREAM | 10+ test files in narya repo |

---

## Detailed Findings

### 1. Narya Binary Location

**Status**: NOT FOUND

Searched locations:
- `which narya` → not in PATH
- `~/.local/bin/` → empty
- `~/worlds/` → no narya binary
- `/nix/store/` → not present
- `~/.nix-profile/` → not present
- `flox list` → flox environment not active or narya not installed
- `opam list` → opam not initialized

**Resolution**: Build from source via nix flake or opam

```bash
# Option 1: Nix (requires flakes enabled)
cd /tmp/narya-check
nix --extra-experimental-features "nix-command flakes" develop

# Option 2: Opam
opam install narya  # if published to opam
```

### 2. Proof General Installation

**Status**: NOT INSTALLED

Checked:
- `~/.emacs.d/elpa/` → no proof-general package
- `~/.emacs.d/init.el` → no proof/narya/coq/agda references
- `~/.emacs.d/site-lisp/` → only chatgpt-shell, shell-maker

**Installed Emacs packages**:
- async, cond-let, crdt, dash, emacsql, ledger-mode, llama
- magit-section, mcp-server-lib, org-bullets, org-download
- org-roam, package-lint

**Resolution**: Install via MELPA

```elisp
;; Add to init.el
(use-package proof-general
  :mode ("\\.ny\\'" . narya-mode)
  :config
  (setq proof-splash-enable nil))
```

### 3. Narya-specific Emacs Mode

**Status**: AVAILABLE IN UPSTREAM

Found in cloned narya repo at `/tmp/narya-check/proofgeneral/`:
- `narya.el` - Main Proof General instance
- `narya-syntax.el` - Syntax highlighting

Key features in narya.el:
- Hole overlay management
- ANSI color support
- Command preprocessing with formfeed delimiters
- Hole solving with reformatting

**Installation path**:
```bash
mkdir -p ~/.emacs.d/site-lisp/narya
cp /tmp/narya-check/proofgeneral/*.el ~/.emacs.d/site-lisp/narya/
```

### 4. Emacs Headless Mode

**Status**: WORKING

```
$ emacs --batch --eval "(message \"Emacs works\")"
Emacs works
```

### 5. Narya Source Files (.ny)

**Status**: AVAILABLE IN UPSTREAM

Example files found in `/tmp/narya-check/test/`:
- `sym.t/sym.ny` - Symmetry proofs with Id types
- `asclam.t/asclam.ny` - Ascription lambda
- `churchnat_uniqueness.t/churchnat_uniqueness.ny` - Church naturals
- `parametric_identity.t/parametric_identity.ny` - Parametricity
- `patterns.t/patterns.ny` - Pattern matching

Sample syntax from `sym.ny`:
```narya
axiom A : Type
axiom a00 : A
axiom a01 : A
axiom a02 : Id A a00 a01
axiom a10 : A
```

### 6. Proofgeneral-Narya Skill

**Status**: EXISTS

Found at `/Users/alice/.claude/skills/proofgeneral-narya/SKILL.md`

Describes:
- Observational bridge types for version control
- GF(3) trit mapping (Locked→+1, Processing→0, Unprocessed→-1)
- 27-agent hierarchy (3×3×3)
- Bruhat-Tits tree navigation
- Möbius inversion for trajectory analysis

---

## Installation Steps Required

### Step 1: Install Proof General
```bash
emacs --batch -l package --eval '
  (progn
    (add-to-list (quote package-archives)
                 (cons "melpa" "https://melpa.org/packages/") t)
    (package-refresh-contents)
    (package-install (quote proof-general)))'
```

### Step 2: Build Narya from Source
```bash
cd /tmp/narya-check
nix --extra-experimental-features "nix-command flakes" develop
dune build
# Binary will be at _build/default/bin/narya.exe
```

### Step 3: Install narya-mode
```bash
mkdir -p ~/.emacs.d/site-lisp/narya
cp /tmp/narya-check/proofgeneral/narya*.el ~/.emacs.d/site-lisp/narya/
```

### Step 4: Configure init.el
```elisp
(add-to-list 'load-path "~/.emacs.d/site-lisp/narya")
(require 'proof-site)
(require 'narya)
```

---

## GF(3) Conservation Check

| Check | Expected | Actual | Status |
|-------|----------|--------|--------|
| MINUS validator ran | -1 | -1 | ✅ |
| Complementary ERGODIC | 0 | (needs ERGODIC agent) | ⏳ |
| Complementary PLUS | +1 | (needs PLUS agent) | ⏳ |
| Sum mod 3 | 0 | TBD | ⏳ |

---

## Conclusion

**Narya and Proof General are NOT currently installed**, but:
1. Emacs is functional for headless operation
2. The proofgeneral-narya skill exists with documentation
3. Source code is available via git clone
4. Installation requires: nix flakes or opam + MELPA

**Next Steps**:
- ERGODIC agent: Coordinate installation
- PLUS agent: Execute installation commands

---

*Validation complete. Anna (German) voice.*
