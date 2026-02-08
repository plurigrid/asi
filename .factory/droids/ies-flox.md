---
name: ies-flox
description: FloxHub publication `bmorphism/ies` - a focused development environment
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# ies-flox

FloxHub publication `bmorphism/ies` - a focused development environment for Clojure, Julia, Python, and multimedia with Gay.jl/Gay.bb deterministic coloring integration.

## Interleaving with effective-topos

| Property | ies-flox | effective-topos |
|----------|----------|-----------------|
| Focus | Data/scripting | Systems/languages |
| Packages | 10 | 62 |
| Man pages | 59 | 606 |
| Key tools | babashka, julia, ffmpeg | guile, ghc, cargo |
| Coloring | Gay.bb (Clojure) | Gay.jl (Julia) |

### Connection Points
- **Clojure ↔ Guile**: Both Lisps, both support reader macros
- **Julia ↔ OCaml**: Both ML-influenced, both have ADTs
- **ffmpeg ↔ imagemagick**: Media processing pipelines
- **tailscale ↔ guile-goblins**: Distributed networking

---

## Quick Activation

```bash
# Activate
flox activate -d ~/ies

# Environment includes
echo $GAY_SEED      # 69
echo $GAY_PORT      # 42069
echo $GAY_INTERVAL  # 30
```

## Installed Packages (10)

| Package | Version | Man Pages | Description |
|---------|---------|-----------|-------------|
| babashka | 1.12.208 | bb(1) | Clojure scripting |
| clojure | 1.12.2.1565 | clj(1), clojure(1) | JVM Lisp |
| jdk | 21.0.8 | java(1) + 45 tools | OpenJDK |
| julia-bin | 1.11.7 | julia(1) | Technical computing |
| ffmpeg | 7.1.1 | ffmpeg(1) + 10 tools | Media processing |
| python312 | 3.12.11 | python3(1) | Python interpreter |
| coreutils | 9.8 | 100+ commands | GNU utilities |
| tailscale | 1.88.4 | tailscale(1) | Mesh VPN |
| enchant2 | 2.6.9 | enchant(1) | Spell checking |
| pkg-config | 0.29.2 | pkg-config(1) | Build configuration |

---

## Babashka (Clojure Scripting)

```clojure
#!/usr/bin/env bb

;; Fast Clojure scripting without JVM startup
;; Includes: http, json, csv, yaml, sql, shell, fs

(require '[babashka.http-client :as http])
(require '[cheshire.core :as json])

;; HTTP request
(-> (http/get "https://api.github.com/users/bmorphism")
    :body
    (json/parse-string true)
    :public_repos)

;; File operat