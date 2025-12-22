# elisp

Emacs Lisp reference (106K lines info).

## Basics

```elisp
(defun greet (name)
  "Greet NAME."
  (message "Hello, %s!" name))

(let ((x 1) (y 2))
  (+ x y))
```

## Macros

```elisp
(defmacro when-let ((var expr) &rest body)
  `(let ((,var ,expr))
     (when ,var ,@body)))
```

## Hooks

```elisp
(add-hook 'after-init-hook #'my-setup)
(remove-hook 'before-save-hook #'delete-trailing-whitespace)
```

## Advice

```elisp
(advice-add 'find-file :before #'my-before-find-file)
(advice-add 'save-buffer :after #'my-after-save)
```

## Info

```
C-h i m elisp RET
C-h f <function>
C-h v <variable>
```
