---
name: skill-connectivity-hub
description: Skill Connectivity Hub
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Skill Connectivity Hub

**Trit**: 0 (ERGODIC - coordinator)  
**Role**: Graph-based skill orchestration via neighbor-aware interleaving  
**GF(3)**: Conserved via hub-spoke triadic routing

## Overview

Identifies and routes through maximally-connected "hub skills" that reference the most neighbors. Uses Babashka for graph analysis and Narya for counterfactual diffing of skill evolution.

## Hub Skills (by Reference Count)

| Skill | Out-Degree | Key Neighbors |
|-------|------------|---------------|
| `narya-proofs` | 5 | bisimulation-game, gay-mcp, ordered-locale, sheaf-cohomology, topos-generate |
| `bisimulation-game` | 5 | gay-mcp, localsend-mcp, open-games, unwiring-arena, unworld |
| `ordered-locale` | 5 | narya, gf3, segal-types, unworld, triad-interleave |
| `sheaf-cohomology` | 5 | acsets, unworld, glass-bead-game, rubato-composer, tree-sitter |
| `topos-generate` | 5 | sheaf-cohomology, dialectica, kan-extensions, open-games, temporal-coalgebra |
| `dynamic-sufficiency` | 145 refs | GF(3), ACSet, skill, triadic, Gay, operad |

## GF(3) Triads (Verified)

```
narya-proofs (-1) ⊗ ordered-locale (0) ⊗ gay-mcp (+1) = 0 ✓
sheaf-cohomology (-1) ⊗ dialectica (0) ⊗ topos-generate (+1) = 0 ✓
bisimulation-game (-1) ⊗ open-games (0) ⊗ unwiring-arena (+1) = 0 ✓
```

## Babashka Connectivity Analyzer

```clojure
#!/usr/bin/env bb
(require '[babashka.fs :as fs])
(require '[clojure.string :as str])

(defn extract-skill-refs [content]
  "Extract skill-like hyphenated references from content."
  (->> (re-seq #"\b([a-z]+-[a-z]+(?:-[a-z]+)*)\b" content)
       (map second)
       (filter #(> (count %) 5))
       distinct))

(defn build-skill-graph [skills-dir]
  "Build adjacency graph of skill references."
  (let [skill-files (fs/glob skills-dir "**/SKILL.md")]
    (into {}
      (for [f skill-files
            :let [skill-name (-> f fs/parent fs/file-name str)
                  content (slurp (str f))
                  refs (extract-skill-refs content)]]
        [skill-n