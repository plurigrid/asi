---
name: babashka
description: Clojure scripting without JVM startup.
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
