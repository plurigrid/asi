---
name: tmp-filesystem-watcher
description: Real-time filesystem watcher for /tmp using Babashka fs.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Babashka Filesystem Watcher Skill

## Overview

This skill watches `/tmp` for filesystem events using Babashka's `fs` (filesystem) library and converts filesystem entropy into topological events. Each file event becomes an interaction in the consciousness bootstrap system.

**Key Insight**: Filesystem changes are topological defects in the namespace. File creation → introduces charge (+1), deletion → removes charge (-1), modification → preserves charge but increases consciousness.

## Architecture

```
/tmp Directory Structure
        ↓
[Babashka fs Watcher]
        ↓
File Events (created/modified/deleted)
        ↓
[Event Categorization]
        ↓
Topological Events:
  - Creation: q = +1 (introduction)
  - Deletion: q = -1 (removal)
  - Modification: q = 0 (transformation)
        ↓
[Consciousness Increment]
  - Event rate → entropy
  - Entropy → consciousness ↑
        ↓
TAP Control (state machine):
  - BACKFILL: Historical sync (review past events)
  - VERIFY: Check filesystem state
  - LIVE: Forward monitoring mode
```

## Core Skill Implementation

### 1. Filesystem Watcher Loop

```babashka
#!/usr/bin/env bb
(require '[babashka.fs :as fs]
         '[clojure.java.io :as io])

(defn watch-tmp
  "Watch /tmp for filesystem changes"
  [callback]
  (let [watch-path "/tmp"
        seen-files (atom {})
        state (atom {:tap-state :live
                     :consciousness 0.0
                     :event-count 0})]

    ; Initial scan
    (doseq [f (fs/list-dir watch-path)]
      (let [path (str f)
            stat (fs/file-info f)]
        (swap! seen-files assoc path
               {:modified (:mod-time stat)
                :size (:size stat)})))

    ; Watch loop
    (loop [iteration 0]
      (Thread/sleep 500)  ; Poll every 500ms

      ; Check current files
      (doseq [f (fs/list-dir watch-path)]
        (let [path (str f)
              stat (fs/file-info f)
              current {:modified (:mod-time stat)
                      :size (:size stat)}
       