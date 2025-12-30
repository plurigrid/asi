---
name: babashka
description: Clojure scripting without JVM startup.
metadata:
  trit: 0
---

# babashka

Clojure scripting without JVM startup.

## Script

```clojure
#!/usr/bin/env bb
(require '[babashka.http-client :as http])
(require '[cheshire.core :as json])

(-> (http/get "https://api.github.com/users/bmorphism")
    :body
    (json/parse-string true)
    :public_repos)
```

## Tasks

```clojure
;; bb.edn
{:tasks
 {:build (shell "make")
  :test  (shell "make test")
  :repl  (babashka.nrepl.server/start-server! {:port 1667})}}
```

## Filesystem

```clojure
(require '[babashka.fs :as fs])
(fs/glob "." "**/*.clj")
(fs/copy "src" "dst")
```

## Process

```clojure
(require '[babashka.process :as p])
(-> (p/shell {:out :string} "ls -la") :out)
```

## Run

```bash
bb script.clj
bb -e '(+ 1 2)'
bb --nrepl-server
```


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
