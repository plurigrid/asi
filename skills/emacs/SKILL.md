# emacs

Emacs ecosystem = elisp + org + gnus + tramp + eglot.

## Atomic Skills

| Skill | Lines | Domain |
|-------|-------|--------|
| elisp | 106K | Programming |
| org | 25K | Documents |
| gnus | 15K | Mail/News |
| tramp | 8K | Remote files |
| eglot | 2K | LSP |
| transient | 3K | Menus |

## Info Access

```
C-h i           Info browser
C-h i m elisp   Elisp manual
C-h i m org     Org manual
C-h f           Describe function
C-h v           Describe variable
```

## Init

```elisp
(use-package org
  :config
  (setq org-directory "~/org"))

(use-package eglot
  :hook ((python-mode . eglot-ensure)))
```

## FloxHub

```bash
flox pull bmorphism/effective-topos
emacs --with-profile topos
```
