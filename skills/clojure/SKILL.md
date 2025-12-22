# clojure

Clojure ecosystem = babashka + clj + lein + shadow-cljs.

## Atomic Skills

| Skill | Startup | Domain |
|-------|---------|--------|
| babashka | 10ms | Scripting |
| clj | 2s | JVM REPL |
| lein | 3s | Build tool |
| shadow-cljs | 5s | ClojureScript |

## Quick Start

```bash
# Scripting (fast)
bb -e '(+ 1 2 3)'

# JVM (full)
clj -M -m myapp.core

# Web (ClojureScript)
npx shadow-cljs watch app
```

## deps.edn

```clojure
{:deps {org.clojure/clojure {:mvn/version "1.12.0"}}
 :aliases {:dev {:extra-paths ["dev"]}
           :test {:extra-deps {lambdaisland/kaocha {:mvn/version "1.0"}}}}}
```

## bb.edn

```clojure
{:tasks {:build (shell "clj -T:build uber")
         :test (shell "clj -M:test")
         :repl (clojure "-M:dev -m nrepl.cmdline")}}
```
