# goblins

Distributed object capability system (6.5K lines info).

## Model

```
peer → vat → actormap → {refr: behavior}
```

## Operators

```scheme
($  obj method args...)   ; Sync (near only)
(<- obj method args...)   ; Async (near/far)
```

## Vat

```scheme
(define vat (spawn-vat))
(define greeter
  (vat-spawn vat
    (lambda (bcom)
      (lambda (name)
        (format #f "Hello, ~a!" name)))))

($ greeter "World")  ; => "Hello, World!"
```

## OCapN

Object Capability Network for secure p2p via CapTP.
