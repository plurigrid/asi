---
name: wev-tesseract
description: WEV Tesseract Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# WEV Tesseract Skill

**Trit**: 0 (ERGODIC - coordinator)
**Color**: #26D826 (Green)
**Role**: Thread ancestry verification and world state reconstruction

## Overview

WEV (World Extractable Value) Tesseract provides:
1. **Thread ancestry verification** - Walk up parent chain to known anchors
2. **World state reconstruction** - Rebuild GF(3)-balanced world from history
3. **Skill collapse protocol** - Load ALL skills when genesis reached
4. **Epistemic arbitrage** - Extract knowledge differentials between 26 worlds

## 26-World GF(3) Structure

```
PLUS  (+1): A, B, C, D, E, W, X, Y, Z    (9 worlds)
ERGODIC(0): F, G, H, I, J, K, L, M       (8 worlds)
MINUS (-1): N, O, P, Q, R, S, T, U, V    (9 worlds)

Sum: 9(+1) + 8(0) + 9(-1) = 0 ✓
```

## Thread Ancestry Protocol

```clojure
(defn verify-thread-ancestry
  "Verify thread is in known set or walk to parent"
  [thread-id parent-map]
  (loop [tid thread-id
         chain []]
    (cond
      ;; Found known anchor
      (thread-in-known? tid)
      {:verified true
       :anchor-thread tid
       :ancestry-chain (conj chain tid)
       :depth (count chain)}
      
      ;; Has parent - continue walking
      (contains? parent-map tid)
      (recur (get parent-map tid) (conj chain tid))
      
      ;; Genesis reached - collapse all skills
      :else
      {:verified false
       :reason :genesis-reached
       :ancestry-chain (conj chain tid)
       :action :collapse-all-skills})))
```

## Skill Collapse Protocol

When genesis thread is reached (no verified ancestor):

```clojure
(defn collapse-all-skills
  "Load ALL skills when genesis thread reached"
  [skill-dirs]
  (let [skills (for [dir skill-dirs
                     :let [expanded (str/replace dir "~" (System/getenv "HOME"))]
                     :when (.exists (java.io.File. expanded))
                     skill-dir (.listFiles (java.io.File. expanded))
                     :when (.isDirectory skill-dir)
                     :let [skill-file (java.io.File. sk