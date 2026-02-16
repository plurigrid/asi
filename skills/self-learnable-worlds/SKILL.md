---
name: self-learnable-worlds
description: "Worlds that learn their own structure via curiosity-driven exploration, compression progress, and autopoietic feedback loops."
version: 1.0.0
trit: 0
color: "#26D8D8"
source: plurigrid/asi
invariant: true
dependencies: [autopoiesis, curiosity-driven, world-hopping, unworld, duckdb-temporal-versioning]
---

# Self-Learnable Worlds

Worlds that learn their own structure. Agents discover patterns, compress them, and worlds evolve.

## Core Architecture

```
┌────────────────────────────────────────────────────────────────────┐
│                    SELF-LEARNABLE WORLD                            │
├────────────────────────────────────────────────────────────────────┤
│                                                                    │
│   ┌─────────────┐     ┌─────────────┐     ┌─────────────┐        │
│   │   OBSERVE   │────▶│   COMPRESS  │────▶│    LEARN    │        │
│   │   (state)   │     │  (patterns) │     │  (update)   │        │
│   └─────────────┘     └─────────────┘     └──────┬──────┘        │
│          ▲                                       │                │
│          │                                       ▼                │
│   ┌──────┴──────┐                        ┌─────────────┐         │
│   │   EXPLORE   │◀───────────────────────│   EVOLVE    │         │
│   │ (curiosity) │                        │  (world)    │         │
│   └─────────────┘                        └─────────────┘         │
│                                                                    │
│   GF(3) Conservation: observe(-1) + compress(0) + learn(+1) = 0  │
└────────────────────────────────────────────────────────────────────┘
```

## World State Schema

Each world has:

```clojure
(def WorldSchema
  {:id          :uuid
   :seed        :uint64           ; Deterministic genesis
   :epoch       :int              ; Derivational step (not time!)
   :state       :map              ; Current configuration
   :invariants  [:keyword]        ; What persists
   :learned     {:pattern :any}   ; Compressed patterns
   :curiosity   :float            ; Compression progress
   :children    [:world-id]       ; Derived worlds
   :parent      :world-id})       ; Genesis world
```

## Curiosity-Driven World Exploration

```python
class SelfLearnableWorld:
    """A world that learns its own structure via compression progress."""
    
    def __init__(self, seed: int, compressor: nn.Module):
        self.seed = seed
        self.epoch = 0
        self.state = self._derive_state()
        self.learned_patterns = {}
        self.compressor = compressor
        self.history = []
        
    def _derive_state(self) -> Dict:
        """Derive state deterministically from seed + epoch."""
        rng = SplitMix64(self.seed ^ self.epoch)
        return {
            'color': gay_color_at(self.seed, self.epoch),
            'structure': rng.next_bytes(32),
            'trit': rng.next_ternary(),
        }
    
    def observe(self) -> Tensor:
        """Observe current world state as tensor."""
        return self._encode_state(self.state)
    
    def compression_progress(self) -> float:
        """How much did we learn from this state?"""
        observation = self.observe()
        
        # Compression before learning
        len_before = self.compressor.description_length(observation)
        
        # Try to learn patterns
        patterns = self._extract_patterns(observation)
        self.compressor.update(patterns)
        
        # Compression after learning
        len_after = self.compressor.description_length(observation)
        
        progress = len_before - len_after
        return progress
    
    def curiosity_reward(self) -> float:
        """Intrinsic reward = compression progress."""
        progress = self.compression_progress()
        self.history.append({
            'epoch': self.epoch,
            'progress': progress,
            'patterns': len(self.learned_patterns)
        })
        return progress
    
    def evolve(self) -> 'SelfLearnableWorld':
        """
        Derive a new world state.
        
        Uses curiosity to guide evolution:
        - High curiosity → explore new structure
        - Low curiosity → exploit known patterns
        """
        reward = self.curiosity_reward()
        
        if reward > 0:
            # We learned something! Derive child world
            child_seed = self.seed ^ hash(self.learned_patterns)
            return SelfLearnableWorld(child_seed, self.compressor)
        else:
            # No progress, advance epoch
            self.epoch += 1
            self.state = self._derive_state()
            return self
    
    def hop_to(self, target_world: 'SelfLearnableWorld') -> List['SelfLearnableWorld']:
        """
        World-hop using triangle inequality.
        Transfer learned patterns along the path.
        """
        distance = self._world_distance(target_world)
        
        if distance <= self._max_hop_distance():
            # Direct hop with pattern transfer
            self._transfer_patterns(target_world)
            return [target_world]
        else:
            # Find intermediate worlds
            path = self._find_path(target_world)
            for i, world in enumerate(path[:-1]):
                world._transfer_patterns(path[i+1])
            return path
    
    def _transfer_patterns(self, target: 'SelfLearnableWorld'):
        """Transfer learned patterns to target world."""
        for name, pattern in self.learned_patterns.items():
            if self._pattern_applicable(pattern, target):
                target.learned_patterns[name] = pattern
                target.compressor.update(pattern)
```

## DuckDB World State Tracking

```sql
-- World evolution history
CREATE TABLE worlds (
    id UUID PRIMARY KEY,
    seed UBIGINT NOT NULL,
    epoch INT NOT NULL,
    parent_id UUID,
    state JSON,
    learned_patterns JSON,
    curiosity_score FLOAT,
    compression_length FLOAT,
    created_at TIMESTAMP DEFAULT current_timestamp,
    FOREIGN KEY (parent_id) REFERENCES worlds(id)
);

-- Learning events
CREATE TABLE world_learning (
    id INTEGER PRIMARY KEY,
    world_id UUID NOT NULL,
    epoch INT,
    pattern_name VARCHAR,
    compression_before FLOAT,
    compression_after FLOAT,
    progress FLOAT GENERATED ALWAYS AS (compression_before - compression_after),
    timestamp TIMESTAMP DEFAULT current_timestamp,
    FOREIGN KEY (world_id) REFERENCES worlds(id)
);

-- World-hop transfers
CREATE TABLE world_hops (
    id INTEGER PRIMARY KEY,
    from_world UUID,
    to_world UUID,
    distance FLOAT,
    patterns_transferred JSON,
    triangle_valid BOOLEAN,
    timestamp TIMESTAMP DEFAULT current_timestamp
);

-- Queries

-- Find worlds with highest learning progress
SELECT w.id, w.seed, SUM(wl.progress) as total_learning
FROM worlds w
JOIN world_learning wl ON w.id = wl.world_id
GROUP BY w.id
ORDER BY total_learning DESC
LIMIT 10;

-- Trace world evolution lineage
WITH RECURSIVE lineage AS (
    SELECT id, seed, epoch, parent_id, 0 as depth
    FROM worlds WHERE id = ?
    UNION ALL
    SELECT w.id, w.seed, w.epoch, w.parent_id, l.depth + 1
    FROM worlds w
    JOIN lineage l ON w.id = l.parent_id
)
SELECT * FROM lineage ORDER BY depth DESC;

-- GF(3) conservation check across world-hops
SELECT 
    wh.id,
    SUM(CAST(JSON_EXTRACT(wh.patterns_transferred, '$[*].trit') AS INT)) % 3 as gf3_sum
FROM world_hops wh
GROUP BY wh.id
HAVING gf3_sum != 0;  -- Violations
```

## nbb Scripts

### world-learn.cljs

```clojure
#!/usr/bin/env nbb
;; world-learn.cljs - Self-learnable world exploration
;; Usage: npx nbb world-learn.cljs <seed> [epochs]

(ns self-learnable-worlds.learn
  (:require ["child_process" :as cp]
            [clojure.string :as str]))

(def HOME (.-HOME (.-env js/process)))
(def DB-PATH (str HOME "/.autopoiesis/worlds.duckdb"))

(defn duck-exec [sql]
  (try
    (let [result (.execSync cp (str "duckdb " DB-PATH " -c \"" sql "\"")
                           #js {:encoding "utf8"})]
      {:success true :output result})
    (catch :default e
      {:success false :error (.-message e)})))

(defn splitmix64 [seed]
  "SplitMix64 step for deterministic derivation."
  (let [z (bit-xor seed (bit-shift-right seed 30))
        z (* z 0xBF58476D1CE4E5B9)
        z (bit-xor z (bit-shift-right z 27))
        z (* z 0x94D049BB133111EB)]
    (bit-xor z (bit-shift-right z 31))))

(defn derive-state [seed epoch]
  "Derive world state from seed + epoch."
  (let [combined (bit-xor seed epoch)
        derived (splitmix64 combined)
        trit (mod derived 3)]
    {:seed seed
     :epoch epoch
     :derived derived
     :trit (if (= trit 2) -1 trit)
     :hue (* (/ (bit-and derived 0xFFFF) 65536) 360)}))

(defn compression-estimate [state patterns]
  "Estimate compression progress."
  (let [state-bits (count (pr-str state))
        pattern-count (count patterns)
        compressed-bits (- state-bits (* pattern-count 8))]
    (max 0 compressed-bits)))

(defn learn-pattern [state]
  "Extract learnable pattern from state."
  {:trit (:trit state)
   :hue-range (int (/ (:hue state) 30))
   :signature (bit-and (:derived state) 0xFF)})

(defn evolve-world [seed epoch patterns]
  "Evolve world and track learning."
  (let [state (derive-state seed epoch)
        pattern (learn-pattern state)
        new-patterns (conj patterns pattern)
        
        len-before (compression-estimate state patterns)
        len-after (compression-estimate state new-patterns)
        progress (- len-before len-after)]
    
    {:state state
     :pattern pattern
     :patterns new-patterns
     :progress progress
     :curious? (pos? progress)}))

(defn run-learning-loop [genesis-seed epochs]
  (println "\n╔═══════════════════════════════════════════════════════════════╗")
  (println "║  SELF-LEARNABLE WORLD                                          ║")
  (println "╚═══════════════════════════════════════════════════════════════╝")
  (println (str "  Genesis seed: 0x" (.toString genesis-seed 16)))
  (println (str "  Epochs: " epochs))
  (println)
  
  (loop [epoch 0
         seed genesis-seed
         patterns []
         total-progress 0]
    (when (< epoch epochs)
      (let [{:keys [state pattern progress curious?]} 
            (evolve-world seed epoch patterns)
            
            trit-char (case (:trit state) -1 "-" 0 "0" 1 "+")]
        
        (println (str "  [" epoch "] seed=0x" (.toString seed 16) 
                     " trit=" trit-char
                     " hue=" (int (:hue state)) "°"
                     " progress=" (if (pos? progress) 
                                   (str "+" progress " ✓")
                                   (str progress))))
        
        (if curious?
          ;; Fork new world
          (let [child-seed (bit-xor seed (hash pattern))]
            (recur (inc epoch) child-seed (conj patterns pattern) (+ total-progress progress)))
          ;; Advance epoch
          (recur (inc epoch) seed patterns total-progress)))))
  
  (println "\n═══════════════════════════════════════════════════════════════")
  (println "  Learning complete"))

(defn -main [& args]
  (let [[seed-str epochs-str] args
        seed (if seed-str 
               (js/parseInt seed-str 16)
               0x42D)
        epochs (if epochs-str
                 (js/parseInt epochs-str)
                 10)]
    (run-learning-loop seed epochs)))

(apply -main *command-line-args*)
```

### world-hop-learn.cljs

```clojure
#!/usr/bin/env nbb
;; world-hop-learn.cljs - Transfer learning via world-hopping

(ns self-learnable-worlds.hop
  (:require [clojure.string :as str]))

(defn world-distance [w1 w2]
  "Calculate distance between worlds."
  (let [seed-dist (-> (bit-xor (:seed w1) (:seed w2))
                      .toString
                      (str/replace #"0" "")
                      count)
        epoch-dist (Math/abs (- (:epoch w1) (:epoch w2)))
        trit-dist (Math/abs (- (:trit w1) (:trit w2)))]
    (Math/sqrt (+ (* seed-dist seed-dist)
                  (* epoch-dist epoch-dist)
                  (* trit-dist 10 trit-dist 10)))))

(defn triangle-valid? [w1 w2 w3]
  "Check triangle inequality for hop path."
  (let [d12 (world-distance w1 w2)
        d23 (world-distance w2 w3)
        d13 (world-distance w1 w3)]
    (<= d13 (+ d12 d23))))

(defn transfer-patterns [from-world to-world]
  "Transfer learnable patterns between worlds."
  (let [applicable (filter #(compatible-trit? % to-world) 
                          (:patterns from-world))]
    (update to-world :patterns concat applicable)))

(defn compatible-trit? [pattern world]
  "Check if pattern trit is compatible with world."
  (let [combined (+ (:trit pattern) (:trit world))]
    (zero? (mod combined 3))))  ; GF(3) conservation

(defn hop-and-learn [source target intermediates]
  "Hop through intermediates, transferring patterns."
  (println "\n→ World-hop with pattern transfer")
  (println (str "  From: seed=0x" (.toString (:seed source) 16)))
  (println (str "  To: seed=0x" (.toString (:seed target) 16)))
  
  (let [path (concat [source] intermediates [target])]
    (doseq [[w1 w2] (partition 2 1 path)]
      (when (triangle-valid? source w1 w2)
        (println (str "  ✓ Hop valid: " (:seed w1) " → " (:seed w2)))
        (transfer-patterns w1 w2)))))
```

## Justfile Commands

```just
# Self-learnable worlds
world-learn seed="0x42D" epochs="10":
    npx nbb skills/self-learnable-worlds/world-learn.cljs {{seed}} {{epochs}}

world-hop from to:
    npx nbb skills/self-learnable-worlds/world-hop-learn.cljs {{from}} {{to}}

world-db-init:
    duckdb ~/.autopoiesis/worlds.duckdb -c "
    CREATE TABLE IF NOT EXISTS worlds (
        id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
        seed UBIGINT NOT NULL,
        epoch INT NOT NULL,
        parent_id UUID,
        state JSON,
        learned_patterns JSON,
        curiosity_score FLOAT,
        created_at TIMESTAMP DEFAULT current_timestamp
    );
    CREATE TABLE IF NOT EXISTS world_learning (
        id INTEGER PRIMARY KEY,
        world_id UUID,
        epoch INT,
        pattern_name VARCHAR,
        progress FLOAT,
        timestamp TIMESTAMP DEFAULT current_timestamp
    );"

world-db-query sql:
    duckdb ~/.autopoiesis/worlds.duckdb -c "{{sql}}"

world-lineage world_id:
    @echo "Tracing world lineage..."
    just world-db-query "WITH RECURSIVE lineage AS (
        SELECT id, seed, epoch, parent_id, 0 as depth FROM worlds WHERE id = '{{world_id}}'
        UNION ALL
        SELECT w.id, w.seed, w.epoch, w.parent_id, l.depth + 1
        FROM worlds w JOIN lineage l ON w.id = l.parent_id
    ) SELECT * FROM lineage ORDER BY depth DESC"

world-top-learners limit="10":
    just world-db-query "SELECT w.id, w.seed, SUM(wl.progress) as total
    FROM worlds w JOIN world_learning wl ON w.id = wl.world_id
    GROUP BY w.id ORDER BY total DESC LIMIT {{limit}}"
```

## Integration with Existing Skills

### Autopoiesis Integration

```clojure
;; Self-modify skill config based on world learning
(defn autopoietic-world-update! [world learning-result]
  (when (:curious? learning-result)
    ;; Update skill preferences based on what world learned
    (modify-prompt! :claude "world-context"
      (str "Current world: seed=0x" (.toString (:seed world) 16)
           ", learned " (count (:patterns learning-result)) " patterns"))))
```

### Gay.jl Color Integration

```julia
# Color worlds by their learning progress
using Gay

function color_world(seed::UInt64, curiosity::Float64)
    base_color = gay_color_at(seed, 1)
    # Saturate based on curiosity
    saturation = 0.5 + (curiosity * 0.5)
    return adjust_saturation(base_color, saturation)
end
```

### Bisimulation Verification

```ruby
# Verify temporal-world and derivational-world are bisimilar
class WorldBisimulation
  def check_equivalence(temporal_world, derivational_world)
    t_trace = temporal_world.evolution_trace
    d_trace = derivational_world.derivation_trace
    
    BisimulationGame.play(t_trace, d_trace)
  end
end
```

## Tripartite World Agents

| Agent | Trit | Role | World Function |
|-------|------|------|----------------|
| Claude | -1 | MINUS | Observe, compress, verify |
| Codex | 0 | ERGODIC | Execute, derive, balance |
| Cursor | +1 | PLUS | Explore, learn, generate |

Sum: -1 + 0 + 1 = 0 ✓

## Self-Learning Loop

```
┌─────────────────────────────────────────────────────────────────────┐
│                                                                     │
│   1. AGENT observes WORLD state                                    │
│                    ↓                                                │
│   2. AGENT compresses patterns (curiosity-driven)                  │
│                    ↓                                                │
│   3. WORLD evolves based on compression progress                   │
│                    ↓                                                │
│   4. AUTOPOIESIS tracks changes in DuckDB                          │
│                    ↓                                                │
│   5. WORLD-HOP transfers patterns to accessible worlds             │
│                    ↓                                                │
│   6. Return to 1 with evolved world                                │
│                                                                     │
│   GF(3) conserved at each step. Triangle inequality enforced.      │
└─────────────────────────────────────────────────────────────────────┘
```

## Key Properties

1. **Deterministic** — Same seed → same world evolution
2. **Learnable** — Worlds improve via compression progress
3. **Transferable** — Patterns hop between accessible worlds
4. **Auditable** — All learning tracked in DuckDB
5. **Conserved** — GF(3) balanced across agents

## Quick Start

```bash
# Initialize worlds database
just world-db-init

# Run learning loop
just world-learn 0x42D 20

# Query top learners
just world-top-learners

# Propagate skill to all agents
just propagate-skill self-learnable-worlds
```
