---
name: asi-transient-agenda
description: Org-agenda-like transient views for ASI skill orchestration via nbb/squint + Emacs hydra
version: 0.1.0
---

# ASI Transient Agenda

**Trit**: +1 (PLUS - synthesis of views)
**Stack**: nbb (Node Babashka) + squint-cljs + Emacs transient/hydra
**Bridge**: emacsclient eval ↔ nbb REPL ↔ plurigrid repo state

## Overview

Org-agenda-style transient dispatcher for navigating 400+ plurigrid repositories,
active ASI skills (616+), and running MCP server state. Renders as Emacs transient
menus (hydra-compatible) with data computed by nbb/squint.

## Architecture

```
nbb/squint (ClojureScript)
  ├── repo-index.cljs     — gh API → repo metadata → DuckDB
  ├── skill-scanner.cljs  — skill directory → status/trit/triad
  └── agenda-render.cljs  — transient menu s-expressions → emacsclient
         │
         ▼
Emacs (transient.el / hydra.el)
  ├── asi-agenda-hydra     — top-level dispatcher
  ├── asi-repo-view        — repo browser with category filters
  └── asi-skill-view       — skill status dashboard
```

## Quick Start

```bash
# Generate agenda data
nbb asi-transient-agenda/repo-index.cljs

# Push transient menu to Emacs
nbb asi-transient-agenda/agenda-render.cljs | emacsclient --eval -

# Or use squint for lightweight JS output
npx squint-cljs compile asi-transient-agenda/agenda-render.cljs
node asi-transient-agenda/agenda-render.mjs
```

## Emacs Hydra Definition

```elisp
(defhydra asi-agenda (:color blue :hint nil)
  "
 ASI Agenda: %(asi-agenda--repo-count) repos | %(asi-agenda--skill-count) skills
 ─────────────────────────────────────────────
 _r_ repos   _s_ skills   _m_ MCP servers
 _t_ triads  _g_ GF(3)    _d_ DuckDB query
 _j_ Julia   _z_ Zig      _c_ Clojure
 _q_ quit
"
  ("r" asi-agenda-repos)
  ("s" asi-agenda-skills)
  ("m" asi-agenda-mcp)
  ("t" asi-agenda-triads)
  ("g" asi-agenda-gf3)
  ("d" asi-agenda-duckdb)
  ("j" asi-agenda-julia)
  ("z" asi-agenda-zig)
  ("c" asi-agenda-clojure)
  ("q" nil))
```

## nbb Repo Index

```clojure
(ns asi-transient-agenda.repo-index
  (:require ["child_process" :as cp]))

(defn gh-repos []
  (-> (cp/execSync "gh repo list plurigrid --limit 400 --json name,description,primaryLanguage,updatedAt"
                   #js {:encoding "utf-8"})
      js/JSON.parse
      (js->clj :keywordize-keys true)))

(defn by-language [repos]
  (group-by #(get-in % [:primaryLanguage :name] "none") repos))

(defn agenda-sexp [repos]
  (let [grouped (by-language repos)]
    (str "(asi-agenda--set-data '"
         (pr-str (into {} (map (fn [[k v]] [k (count v)]) grouped)))
         ")")))

(println (agenda-sexp (gh-repos)))
```

## Squint Variant

```clojure
;; agenda-render.cljs (squint dialect)
(ns asi-transient-agenda.agenda-render)

(defn render-transient [data]
  (let [sections (map (fn [[category items]]
                        (str "[\"" category "\" "
                             (apply str (map (fn [item]
                                              (str "(\"" (first (name (:name item))) "\" "
                                                   "\"" (:name item) "\" "
                                                   "asi-agenda-visit)"))
                                            items))
                             "]"))
                      data)]
    (str "(transient-define-prefix asi-repo-browser ()\n"
         "  \"Plurigrid Repository Browser\"\n"
         "  [" (apply str (interpose "\n   " sections)) "])")))
```

## Canonical Triads

```
emacs (-1) + asi-transient-agenda (+1) + babashka-clj (0) = 0
squint-runtime (0) + asi-transient-agenda (+1) + cider-clojure (-1) = 0
```

## Plurigrid Repo Categories

| Category | Count | Key Repos |
|----------|-------|-----------|
| Scheme/Goblins | ~6 | hoot, leprechauns, goblinshare, shepherd |
| Gay.jl Colors | ~7 | gay-rs, gay-go, gay-terminal, lazygay, lazybjj |
| Julia | ~4 | asi-skills, UnwiringDiagrams.jl, MolotovRibbentropKrylovKit.jl |
| Zig | ~2 | zig-syrup, ies |
| Rust | ~8 | clopen-hypergraphs, sprintathon, saopaulo, duck-kanban |
| Python | ~10 | asi, properon, froggo, oni, panda |
| Clojure | ~3 | agent-o-rama, madonna, agi-tools |
| TypeScript | ~4 | portal, llms-txt-hub, pepepedia |
