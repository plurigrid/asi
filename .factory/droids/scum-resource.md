---
name: scum-resource
description: SCUM Resource Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

## CRITICAL: NO DEMOS

Loading this skill for context ≠ executing demonstration code.
Do NOT run theatrical Babashka/shell commands to "show" the skill working.
Execute ONLY when the user explicitly requests action on real targets.

# SCUM Resource Skill

**System Consumption Utilization Monitor** - Libkind-style compositional resource management.

## SCUM Score Formula

```
SCUM(p) = α·MEM(p) + β·CPU(p) + γ·TIME(p) + δ·STALE(p)
```

Where:
- **MEM(p)**: Memory usage normalized to system total
- **CPU(p)**: CPU% averaged over sampling window
- **TIME(p)**: Total CPU time consumed (cumulative sin)
- **STALE(p)**: Time since last meaningful I/O (zombie indicator)

Default weights: α=0.4, β=0.2, γ=0.2, δ=0.2

## GF(3) Classification

| SCUM Score | Trit | Action | Color |
|------------|------|--------|-------|
| 0-33 | +1 | HEALTHY | Green |
| 34-66 | 0 | MONITOR | Yellow |
| 67-100 | -1 | TERMINATE | Red |

## Quick Commands

```bash
# Calculate SCUM scores for top processes
scum-score

# Kill processes above threshold
scum-kill 80

# Show resource allocation as ACSet
scum-acset

# Libkind-style resource rebalancing
scum-balance
```

## Babashka Implementation

```clojure
#!/usr/bin/env bb
(require '[babashka.process :refer [shell]])

(defn parse-top []
  (->> (shell {:out :string} "top" "-l" "1" "-stats" "pid,command,cpu,mem,time" "-o" "mem" "-n" "30")
       :out
       str/split-lines
       (drop 12)
       (map #(str/split % #"\s+"))
       (filter #(> (count %) 4))))

(defn calc-scum [{:keys [mem cpu time]}]
  (let [mem-score (* 0.4 (/ mem 100))
        cpu-score (* 0.2 (/ cpu 100))
        time-score (* 0.2 (min 1.0 (/ time 3600)))
        stale-score 0.0]  ; TODO: track I/O
    (int (* 100 (+ mem-score cpu-score time-score stale-score)))))

(defn scum-report []
  (println "PID\tSCUM\tMEM\tCPU\tCOMMAND")
  (println "---\t----\t---\t---\t-------")
  (doseq [[pid cmd cpu mem time] (parse-top)]
    (when-let [scum (calc-scum {:mem (parse-double mem)
              