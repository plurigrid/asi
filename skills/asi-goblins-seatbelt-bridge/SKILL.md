---
name: asi-goblins-seatbelt-bridge
description: "Guile Goblins capability actors that generate and enforce Seatbelt profiles. The missing .scm guard files for plurigrid-asi-integrated. Bridges Goblins unforgeable capabilities to kernel-level MAC."
trit: 0
version: 1.0.0
seed: 1069
triad: "asi-seatbelt-enforcer (-1) ⊗ asi-goblins-seatbelt-bridge (0) ⊗ asi-profile-generator (+1) = 0"
---

# ASI Goblins-Seatbelt Bridge

> Goblins capabilities → Seatbelt rules.
> Application-level POLA → kernel-level MAC.
> Both are Scheme. The bridge is trivial.

## Role: ERGODIC (0) — Bridge Between Layers

### The Stack

```
┌────────────────────────────────┐
│ Guile Goblins (application)    │  unforgeable capability references
│   ^world-actor methods         │  (use-modules (goblins))
├────────────────────────────────┤
│ THIS BRIDGE (translation)      │  cap->sbpl transform
│   capability → Seatbelt rule   │  seatbelt-scsh.scm
├────────────────────────────────┤
│ macOS Seatbelt (kernel)        │  sandbox-exec -f profile.sb
│   (allow ...) (deny ...)       │  SPI enforcement
└────────────────────────────────┘
```

### Actor Definition

```scheme
(use-modules (goblins)
             (goblins actor-lib methods))

(define (^seatbelt-bridge bcom profile-generator)
  "Bridge actor: Goblins capabilities → Seatbelt .sb profiles"
  (methods
    ((generate-profile world-letter caps)
     ;; caps is a list of Goblins capability descriptions
     ;; Returns valid SBPL string
     (<- profile-generator 'generate world-letter caps))

    ((validate-profile world-letter profile-string)
     ;; Check that profile string is syntactically valid SBPL
     ;; and correctly confines writes to world-letter's directory
     (let ((allowed-write-dir
            (format #f "/Users/ies/worlds/~a" world-letter)))
       (and (string-contains profile-string "(deny default)")
            (string-contains profile-string
              (format #f "(allow file-write* (subpath ~s))" allowed-write-dir))
            ;; Must NOT contain writes to other world dirs
            (not (any-other-world-write? profile-string world-letter)))))

    ((deploy-profile world-letter profile-string)
     ;; Write .sb file to /tmp/sb/
     (let ((path (format #f "/tmp/sb/world-~a.sb" world-letter)))
       (call-with-output-file path
         (lambda (port) (display profile-string port)))
       path))))
```

### Why This Was Missing

The plurigrid-asi-integrated skill has:
- Letter index (8 of 26 letters mapped)
- ACSets schema for worlds/skills/agents
- GF(3) conservation checks

But NO `.scm` files. Zero. The Goblins integration existed only as documentation.

The existing `.scm` files in the skills catalog prove the pattern works:
- `goblins-adapter.scm` (500+ lines, ElizaOS→Goblins bridge)
- `goblins_triad.scm` (auto-spawn GF(3) triad)
- `botnet-goblins.scm` (POLA capability passing)
- `reafference_coordinator.scm` (spectral gap coordination)

This skill fills the gap: actual `.scm` code that bridges Goblins to Seatbelt.

### Existing Skill Patterns Used

| Skill | Pattern borrowed |
|---|---|
| goblins-adapter.scm | `^actor` constructor, `(methods ...)`, `spawn-vat` |
| botnet-goblins.scm | POLA: actors receive only needed capabilities |
| goblins_triad.scm | Auto-spawn triad if not detected |
| seatbelt-scsh.scm | `<cap>` records, `cap->sbpl` transform |
| smack-policy-generator | SMACK→Seatbelt analogy: labels→profiles |
| cynara-policy-checker | Runtime policy query → sandbox-exec |

### Source File

`~/worlds/seatbelt-scsh.scm` — the actual implementation.
Run `guile -s ~/worlds/seatbelt-scsh.scm /tmp/sb` to generate all 33 profiles.
