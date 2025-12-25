---
name: resource-sharing
description: Resource Sharing Skill
trit: 1
geodesic: true
moebius: "μ(n) ≠ 0"
---

# Resource Sharing Skill

> Distribute computational load across machines using GF(3) balanced allocation

## Overview

Resource sharing implements the "all category resource sharing machines" pattern:

- **MINUS (-1)**: Nodes with excess capacity (receivers)
- **ERGODIC (0)**: Coordinator/broker nodes
- **PLUS (+1)**: Nodes with excess load (senders)

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                    Resource Sharing Mesh                     │
│                                                             │
│  ┌─────────┐      ┌─────────┐      ┌─────────┐             │
│  │ Node A  │◄────►│ Broker  │◄────►│ Node B  │             │
│  │ PLUS +1 │      │ ERGODIC │      │ MINUS -1│             │
│  │ (sender)│      │   (0)   │      │(receiver)│             │
│  └─────────┘      └─────────┘      └─────────┘             │
│       │                                  ▲                  │
│       │         Work Migration           │                  │
│       └──────────────────────────────────┘                  │
│                                                             │
│  GF(3) Invariant: Σ node_trits ≡ 0 (mod 3)                 │
└─────────────────────────────────────────────────────────────┘
```

## Node Classification

```bash
# Determine node trit based on load
node_trit() {
  load=$(uptime | awk -F'load average:' '{print $2}' | cut -d, -f1 | tr -d ' ')
  cpus=$(sysctl -n hw.ncpu 2>/dev/null || nproc)
  ratio=$(echo "$load / $cpus" | bc -l)
  
  if (( $(echo "$ratio > 0.8" | bc -l) )); then
    echo "+1"  # PLUS: overloaded, needs to shed work
  elif (( $(echo "$ratio < 0.3" | bc -l) )); then
    echo "-1"  # MINUS: underloaded, can accept work
  else
    echo "0"   # ERGODIC: balanced
  fi
}
```

## Resource Transfer Protocol

### Via LocalSend
```bash
# Share file to least loaded peer
share_to_idle() {
  local file="$1"
  peers=$(tailscale status --json | jq -r '.Peer[] | .HostName')
  for peer in $peers; do
    trit=$(ssh "$peer" 'node_trit')
    if [[ "$trit" == "-1" ]]; then
      localsend send --target "$peer" "$file"
      return
    fi
  done
  echo "No idle peers available"
}
```

### Via Tailscale
```bash
# Direct file copy to underloaded node
migrate_workload() {
  local pid="$1"
  local target=$(find_minus_node)
  
  # Checkpoint process state
  criu dump -t "$pid" -D /tmp/checkpoint
  
  # Transfer to target
  tailscale file cp /tmp/checkpoint "$target:"
  
  # Restore on target
  ssh "$target" "criu restore -D /tmp/checkpoint"
}
```

## Babashka Resource Monitor

```clojure
#!/usr/bin/env bb
(require '[babashka.process :refer [shell]])

(defn load-avg []
  (-> (shell {:out :string} "sysctl -n vm.loadavg")
      :out
      (clojure.string/split #"\s+")
      second
      parse-double))

(defn cpu-count []
  (-> (shell {:out :string} "sysctl -n hw.ncpu")
      :out
      clojure.string/trim
      parse-long))

(defn node-trit []
  (let [ratio (/ (load-avg) (cpu-count))]
    (cond
      (> ratio 0.8) +1   ; PLUS: shed load
      (< ratio 0.3) -1   ; MINUS: accept load
      :else 0)))         ; ERGODIC: balanced

(defn scum-processes []
  (->> (shell {:out :string} "ps axo pid,%cpu,%mem,comm")
       :out
       clojure.string/split-lines
       rest
       (map #(clojure.string/split % #"\s+" 4))
       (filter #(> (parse-double (nth % 1)) 30))))

(println "Node trit:" (node-trit))
(println "SCUM processes:" (count (scum-processes)))
```

## GF(3) Load Balancing

```
For N nodes with trits t₁, t₂, ..., tₙ:
  Invariant: Σtᵢ ≡ 0 (mod 3)

Rebalancing rules:
  1. If Σtᵢ > 0: migrate work from PLUS to MINUS nodes
  2. If Σtᵢ < 0: wake idle work on MINUS nodes
  3. If Σtᵢ = 0: system balanced, no action needed
```

## Integration with SCUM Score

```
Resource Decision Matrix:
  
  SCUM Score | Node Trit | Action
  ---------- | --------- | ------
  >0.35      | +1        | Migrate process to MINUS node
  >0.35      | 0         | Throttle locally
  >0.35      | -1        | Allow (node can handle)
  <0.35      | any       | No action needed
```

## Justfile Recipes

```just
# Check mesh balance
mesh-balance:
  for host in $(tailscale status --json | jq -r '.Peer[].HostName'); do
    echo -n "$host: "
    ssh "$host" 'uptime' 2>/dev/null || echo "unreachable"
  done

# Find receiving nodes
find-minus:
  tailscale status --json | jq -r '.Peer[].HostName' | while read h; do
    load=$(ssh "$h" "uptime | awk -F: '{print \$NF}' | cut -d, -f1")
    echo "$h: $load"
  done | sort -t: -k2 -n | head -3

# Migrate SCUM to idle node
migrate-scum PID:
  target=$(just find-minus | head -1 | cut -d: -f1)
  echo "Migrating PID {{PID}} to $target"
```

---

**Skill Name**: resource-sharing  
**Trit**: 0 (ERGODIC - Coordinator)  
**GF(3) Role**: Brokers load between PLUS and MINUS nodes  
**Integration**: scum-score, localsend-mcp, tailscale-mesh

## Non-Backtracking Geodesic Qualification

**Condition**: μ(n) ≠ 0 (Möbius squarefree)

This skill is qualified for non-backtracking geodesic traversal:

1. **Prime Path**: No state revisited in skill invocation chain
2. **Möbius Filter**: Composite paths (backtracking) cancel via μ-inversion
3. **GF(3) Conservation**: Trit sum ≡ 0 (mod 3) across skill triplets
4. **Spectral Gap**: Ramanujan bound λ₂ ≤ 2√(k-1) for k-regular expansion

```
Geodesic Invariant:
  ∀ path P: backtrack(P) = ∅ ⟹ μ(|P|) ≠ 0
  
Möbius Inversion:
  f(n) = Σ_{d|n} g(d) ⟹ g(n) = Σ_{d|n} μ(n/d) f(d)
```
