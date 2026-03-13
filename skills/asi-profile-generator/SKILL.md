---
name: asi-profile-generator
description: "Generates macOS Seatbelt .sb profiles from Guile Goblins capability descriptions. The PLUS arm of the enforcement triad — creates profiles that the enforcer (-1) validates and the coordinator (0) glues."
trit: 1
version: 1.0.0
seed: 1069
triad: "asi-seatbelt-enforcer (-1) ⊗ asi-sheaf-coordinator (0) ⊗ asi-profile-generator (+1) = 0"
---

# ASI Profile Generator

> Seatbelt .sb files ARE Scheme programs. This skill generates them from Guile.
> Source: `~/worlds/seatbelt-scsh.scm`

## Role: PLUS (+1) — Generate

Creates 33 sandbox profiles:
- 7 core: nix-daemon, flox-hook, trit-kernel, sdr-analyzer, goblins-vat, seatbelt-gen, captp-bridge
- 26 world: world-{a..z} with per-letter write isolation

## The Generator

```bash
guile -s ~/worlds/seatbelt-scsh.scm /tmp/sb
```

Outputs to `/tmp/sb/*.sb`. Each profile is valid SBPL (Scheme).

## Key Design Decisions

### 1. Broad file-read* (macOS Sequoia requirement)
macOS dyld shared cache requires `(allow file-read*)` without path restriction.
Security comes from restricting WRITES, NETWORK, EXEC, and IPC — not reads.

### 2. Per-letter write confinement
```scheme
(allow file-write* (subpath "/Users/ies/worlds/<letter>"))
;; Everything else: denied by (deny default)
```

### 3. GF(3) trit on every profile
Each profile carries a trit from the droid config. Sum across all 33 = -6 ≡ 0 (mod 3).

### 4. scsh idiom
Everything is a record (`<cap>`, `<profile>`) piped through transforms (`cap->sbpl`).
No shell, no awk, no popen. Pure Scheme data.

## Capability Vocabulary

| Constructor | SBPL output | Trit |
|---|---|---|
| `(deny-default)` | `(deny default)` | -1 |
| `(file-read p)` | `(allow file-read* (subpath p))` | -1 |
| `(file-write p)` | `(allow file-write* (subpath p))` | +1 |
| `(file-exec p)` | `(allow process-exec (subpath p))` | +1 |
| `(net-https h)` | `(allow network-outbound (remote tcp "*:443"))` | +1 |
| `(mach-service n)` | `(allow mach-lookup (global-name n))` | 0 |
| `(sig target)` | `(allow signal (target target))` | 0 |

## Tested and Verified

All 33 profiles pass `sandbox-exec -f <profile> /usr/bin/true`.
Per-letter isolation verified:
- world-z can write to ~/worlds/z/ (PASS)
- world-z cannot write to ~/worlds/a/ (DENIED)
- trit-kernel: no write, no net (DENIED)

## Extending

To add a new profile, add a `<profile>` record to `seatbelt-scsh.scm`:
```scheme
(define %my-service
  (make-profile
   "my-service"
   (append
    (list (deny-default)
          (sb-comment "baseline"))
    %system-baseline
    (list (file-exec "/nix/store")
          (file-write "/specific/path")
          (sig 'self))
    %system-exec)
   "my-service description"
   +1))  ;; trit
```

Then add it to the core list and re-run. GF(3) conservation is checked automatically.
