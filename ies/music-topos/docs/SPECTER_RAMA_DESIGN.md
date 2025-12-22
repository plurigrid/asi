# Specter-Style Navigation with Rama-Style Local Caching

## Overview

This design combines:
1. **Specter's compiled-path navigators** - composable, high-performance data navigation
2. **Rama's PState local caching model** - local materialized views with fine-grained reactivity

Goal: Navigate the `~/worlds` tree structure with specter's elegance while caching results locally like Rama's PStates.

## Key Concepts from Each

### Specter Core Ideas
```clojure
;; Specter: Navigation as composition
(select [:worlds :pitch-space ALL :objects] world-tree)
(transform [:worlds :chord-space :metric] optimized-fn world-tree)

;; Compiled paths for performance (auto-memoized in 0.11+)
(def WORLD-OBJECTS (comp-paths :worlds :pitch-space :objects ALL))
```

### Rama PState Core Ideas
```java
// Rama: Local partitioned state with subindexing
s.pstate("$$worlds",
  PState.mapSchema(
    String.class,  // world-id
    PState.mapSchema(
      String.class,  // object-id
      Object.class).subindexed()));  // subindexed for O(1) access

// Local ops: no network round-trip
.localSelect("$$worlds", Path.key("pitch-space").all())
.localTransform("$$worlds", Path.key("chord-space").key(id).termVal(newChord))
```

## Design: SpecterCache for music-topos

### 1. Local Cache Structure (Rama-inspired)

```clojure
(ns music-topos.specter-cache
  (:require [com.rpl.specter :as sp :refer [select transform setval 
                                             ALL MAP-VALS FIRST LAST
                                             comp-paths]]
            [music-topos.cofree-comonad :as matter]))

;; The local cache mirrors Rama's PState concept:
;; - Partitioned by world-type
;; - Subindexed for efficient nested access
;; - Fine-grained reactive updates

(defonce ^:private cache-state 
  (atom {:worlds {}           ;; Map of world-id -> world-data
         :versions {}         ;; Map of path -> version-number (for cache invalidation)
         :subscriptions {}    ;; Map of path -> Set of callbacks (reactive)
         :indices {}}))       ;; Secondary indices for fast lookup

(defn- make-cache-key [path]
  (hash path))
```

### 2. Specter Navigators for Worlds

```clojure
;; Custom navigators for the musical world tree

(sp/defnav WORLD
  "Navigate to a specific world by id"
  [world-id]
  (select* [this structure next-fn]
    (next-fn (get-in structure [:worlds world-id])))
  (transform* [this structure next-fn]
    (update-in structure [:worlds world-id] next-fn)))

(sp/defnav OBJECTS
  "Navigate to objects in current world"
  []
  (select* [this structure next-fn]
    (mapcat next-fn (:objects structure)))
  (transform* [this structure next-fn]
    (update structure :objects #(into #{} (map next-fn %)))))

(sp/defnav METRIC
  "Navigate to the metric function"
  []
  (select* [this structure next-fn]
    (next-fn (:metric structure)))
  (transform* [this structure next-fn]
    (update structure :metric next-fn)))

;; Compiled paths for hot-path access (like Rama's subindexing)
(def PITCH-WORLD-OBJECTS 
  (comp-paths (WORLD "PitchSpace") OBJECTS))

(def CHORD-WORLD-OBJECTS
  (comp-paths (WORLD "ChordSpace") OBJECTS))

(def HARMONIC-FUNCTIONS
  (comp-paths (WORLD "HarmonicWorld") :objects ALL))
```

### 3. Local Select/Transform (Rama-style API)

```clojure
(defn local-select
  "Select from local cache. No network, O(1) for indexed paths.
   Mirrors Rama's localSelect - operates on current partition."
  [path]
  (let [cache @cache-state
        cache-key (make-cache-key path)
        cached (get-in cache [:indices cache-key])]
    (if cached
      ;; Cache hit: return immediately
      cached
      ;; Cache miss: compute and store
      (let [result (select path (:worlds cache))]
        (swap! cache-state assoc-in [:indices cache-key] result)
        result))))

(defn local-transform
  "Transform in local cache with fine-grained diff tracking.
   Mirrors Rama's localTransform - updates local partition."
  [path transform-fn]
  (let [old-val (local-select path)
        new-state (swap! cache-state 
                    (fn [state]
                      (-> state
                          (update :worlds #(transform path transform-fn %))
                          (update-in [:versions (make-cache-key path)] (fnil inc 0))
                          ;; Invalidate dependent indices
                          (update :indices dissoc (make-cache-key path)))))]
    ;; Compute diff for reactive subscribers (like Rama's KeyDiff)
    (let [new-val (select path (:worlds new-state))
          diff (compute-diff old-val new-val)]
      (notify-subscribers path diff new-val old-val)
      new-val)))

(defn local-select-one
  "Select exactly one value (like Rama's selectOne)"
  [path]
  (first (local-select path)))
```

### 4. Fine-Grained Reactivity (Rama's ProxyState)

```clojure
(defn proxy
  "Create a reactive proxy to a path. Updates automatically.
   Like Rama's PState.proxy() - receives fine-grained diffs."
  [path callback]
  (let [sub-id (gensym "proxy-")
        initial-value (local-select-one path)]
    ;; Register subscription
    (swap! cache-state update-in [:subscriptions (make-cache-key path)]
           (fnil conj #{}) {:id sub-id :callback callback})
    ;; Send initial value (like Rama's ResyncDiff)
    (callback initial-value {:type :resync} nil)
    ;; Return proxy handle
    {:id sub-id
     :path path
     :close (fn [] 
              (swap! cache-state update-in [:subscriptions (make-cache-key path)]
                     disj sub-id))}))

(defn- compute-diff [old-val new-val]
  "Compute Rama-style diff between values"
  (cond
    (nil? old-val) {:type :new-value :value new-val}
    (nil? new-val) {:type :removed}
    (map? old-val) 
      (let [changed-keys (for [k (set (concat (keys old-val) (keys new-val)))
                               :when (not= (get old-val k) (get new-val k))]
                           k)]
        {:type :key-diff :keys changed-keys})
    (set? old-val)
      {:type :set-diff 
       :added (clojure.set/difference new-val old-val)
       :removed (clojure.set/difference old-val new-val)}
    :else {:type :value-diff :old old-val :new new-val}))

(defn- notify-subscribers [path diff new-val old-val]
  "Push diffs to all subscribers of a path (like Rama reactive callbacks)"
  (doseq [{:keys [callback]} (get-in @cache-state [:subscriptions (make-cache-key path)])]
    (callback new-val diff old-val)))
```

### 5. Subindexing for O(1) Nested Access

```clojure
;; Rama's key insight: subindexed nested structures don't load parent
;; We simulate this with a flat index for deep paths

(defn enable-subindexing
  "Mark a path as subindexed for O(1) access to nested elements.
   Like Rama's .subindexed() on schema."
  [path]
  (swap! cache-state assoc-in [:subindexed (make-cache-key path)] true))

(defn subindexed-select
  "O(1) select for subindexed paths - goes directly to nested data."
  [base-path key-path]
  (let [full-path (concat base-path key-path)]
    (local-select-one full-path)))

;; Pre-index common paths at startup
(defn init-world-indices!
  "Initialize subindexing for world tree"
  []
  (enable-subindexing [(WORLD "PitchSpace") OBJECTS])
  (enable-subindexing [(WORLD "ChordSpace") OBJECTS])
  (enable-subindexing [(WORLD "HarmonicWorld") :objects]))
```

### 6. Integration with Cofree Comonad (Matter)

```clojure
(defn matter-with-cache
  "Extend MusicalMatter to use local cache for transforms.
   Pattern requests → Matter checks cache first."
  [base-matter]
  (let [cached-transforms 
        (memoize 
          (fn [transform-key target]
            (let [transform-fn (local-select-one 
                                 [(WORLD "TransformationWorld") 
                                  :transforms transform-key])]
              (when transform-fn (transform-fn target)))))]
    (assoc base-matter
      :transforms cached-transforms
      ;; Conditions check the reactive cache
      :conditions 
        {:in-tonic? 
         (fn [_] 
           (= :tonic (local-select-one 
                       [(WORLD "HarmonicWorld") :current-function])))
         :cadence-ready?
         (fn [_]
           (= :dominant (local-select-one
                          [(WORLD "HarmonicWorld") :current-function])))})))
```

### 7. Example Usage

```clojure
;; Initialize the worlds cache
(defn init-worlds! []
  (local-transform [:worlds] 
    (constantly
      {"PitchSpace" (MusicalWorlds/pitch-space-world)
       "ChordSpace" (MusicalWorlds/chord-space-world)
       "HarmonicWorld" (MusicalWorlds.HarmonicWorld/world)
       "TransformationWorld" (MusicalWorlds.TransformationWorld/world)})))

;; Query with specter syntax, rama-style local access
(local-select PITCH-WORLD-OBJECTS)
;; => #{#<PitchClass C> #<PitchClass E> #<PitchClass G>}

;; Transform with auto-reactivity
(local-transform [(WORLD "HarmonicWorld") :current-function]
  (constantly :dominant))
;; All subscribers notified with {:type :value-diff :old :tonic :new :dominant}

;; Set up reactive UI binding
(def harmonic-proxy 
  (proxy [(WORLD "HarmonicWorld") :current-function]
    (fn [new-val diff old-val]
      (println "Harmonic function changed:" old-val "->" new-val)
      (update-ui! new-val))))

;; Later: clean up
((:close harmonic-proxy))
```

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                    Specter-Cache Layer                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐      │
│  │ Specter      │    │ Local Cache  │    │ Reactive     │      │
│  │ Navigators   │───▶│ (Atom)       │◀───│ Proxies      │      │
│  │              │    │              │    │              │      │
│  │ WORLD        │    │ :worlds      │    │ Callbacks    │      │
│  │ OBJECTS      │    │ :versions    │    │ Diffs        │      │
│  │ METRIC       │    │ :indices     │    │              │      │
│  └──────────────┘    └──────────────┘    └──────────────┘      │
│         │                   │                   ▲               │
│         ▼                   ▼                   │               │
│  ┌────────────────────────────────────────────────────────┐    │
│  │              local-select / local-transform             │    │
│  │                 (Rama-style API)                        │    │
│  └────────────────────────────────────────────────────────┘    │
│                             │                                   │
└─────────────────────────────┼───────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────────┐
│                    Pattern Runs on Matter                       │
├─────────────────────────────────────────────────────────────────┤
│  Free Monad (Pattern)         │         Cofree Comonad (Matter) │
│  ┌────────────────────┐       │       ┌────────────────────┐   │
│  │ PlayNote           │       │       │ MusicalMatter      │   │
│  │ PlayChord          │──runs─┼──on──▶│ .transforms (cached)│  │
│  │ Transform          │       │       │ .conditions (cached)│  │
│  │ ...                │       │       │ ...                 │   │
│  └────────────────────┘       │       └────────────────────┘   │
└─────────────────────────────────────────────────────────────────┘
```

## Key Benefits

| Feature | Specter | Rama PState | Our Design |
|---------|---------|-------------|------------|
| Path composition | ✓ comp-paths | ✓ Path.key().all() | ✓ comp-paths + custom navs |
| Auto-compilation | ✓ since 0.11 | N/A | ✓ inherits from specter |
| Local O(1) access | - | ✓ localSelect | ✓ local-select + indices |
| Subindexing | - | ✓ .subindexed() | ✓ enable-subindexing |
| Fine-grained diffs | - | ✓ KeyDiff, SetDiff | ✓ compute-diff |
| Reactive proxies | - | ✓ PState.proxy() | ✓ proxy function |
| Immutable transforms | ✓ | ✓ | ✓ |

## Performance Considerations

1. **Hot paths get compiled navigators** (Specter's inline-caching)
2. **Subindexed paths skip parent traversal** (Rama's subindexing model)  
3. **Memoized transforms** reduce re-computation
4. **Fine-grained diffs** minimize reactive update cost
5. **Local-only ops** avoid any network/IO overhead

## Next Steps

1. Implement `music-topos.specter-cache` namespace
2. Add to `project.clj`: `[com.rpl/specter "1.1.4"]`
3. Migrate `lib/worlds.rb` to use cache layer
4. Connect to `music-topos.cofree-comonad` for Matter integration
