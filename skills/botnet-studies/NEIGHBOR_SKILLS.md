# Botnet Studies: Neighbor Skills

**Date**: 2026-02-13
**Framework**: GF(3) Neighborhood Awareness

---

## Tier 1: Core Security Triad

| Skill | Trit | Role | Interface | Morphism |
|-------|------|------|-----------|----------|
| **botnet-studies** | -1 | VALIDATOR | Analyze C2 infrastructure | `dga_entropy(domain)` |
| **blackhat-go** | 0 | COORDINATOR | Tooling & technique bridge | `tool_dispatch(technique)` |
| **botnet-disruption** | +1 | GENERATOR | Produce takedown plans | `plan_disruption(botnet_type)` |

**GF(3) Check**: (-1) + (0) + (+1) = 0

---

## Tier 2: Game-Theoretic Analysis

| Skill | Trit | Role | Interface |
|-------|------|------|-----------|
| **nashator** | 0 | Nash equilibrium solver | `nashator_solve("botnet_propagation")` |
| **open-games** | +1 | Compositional game structure | `seq(botnet_game, defense_game)` |
| **cybernetic-open-game** | 0 | Cybernetic loop closure | `cybernetic_loop(observe, orient, decide, act)` |

**Triplet**: botnet-studies (-1) + nashator (0) + botnet-disruption (+1) = 0

### Botnet Games in Nashator

| Game | Type | Players | Equilibrium Summary |
|------|------|---------|---------------------|
| `botnet_propagation` | Stackelberg (4x4) | Attacker vs Defender | Attacker favors scan (41%), Defender favors detect+isolate |
| `dga_cat_and_mouse` | Zero-sum (3x4) | DGA Operator vs DNS Defender | Attacker favors hybrid DGA (66%), Defender favors LLM (73%) |
| `blockchain_c2_defense` | Mechanism design (3x3) | C2 Operator vs Chain Defender | Operator favors updates (42%), Defender favors monitoring (43%) |
| `botnet_lifecycle` | Sequential composition | Attack chain (3 stages) | seq(propagation ; dga ; blockchain) |
| `operation_endgame` | Sequential composition | LEA vs Operators (3 phases) | Phase 1 favors defender (+0.56 payoff) |

---

## Tier 3: Detection & Forensics

| Skill | Trit | Role | Interface |
|-------|------|------|-----------|
| **reverse-engineering** | -1 | Binary analysis | `analyze_malware(sample)` |
| **network-forensics** | 0 | Traffic analysis | `capture_flows(interface, filter)` |
| **captp** | 0 | OCapN transport layer | `deliver(cap_ref, method, args)` |

**Triplet**: reverse-engineering (-1) + captp (0) + botnet-disruption (+1) = 0

---

## Tier 4: Structural Defense

| Skill | Trit | Role | Interface |
|-------|------|------|-----------|
| **goblins-adapter** | 0 | OCapN bridge to MCP/OpenClaw | `register_plugin(actions, providers)` |
| **agent-o-rama** | +1 | Autonomous agent generation | `spawn_agent(role, caps)` |
| **counter-surveillance** | -1 | Adversarial observation | `detect_exfiltration(flows)` |

**Key insight**: Goblins actors + POLA = structural defense against lateral movement.
A compromised IoT actor cannot scan/phone-home/persist without explicit capabilities.

---

## Implementation Substrates

| Substrate | File | What it provides |
|-----------|------|-----------------|
| **Zig** | `dga-analyzer.zig` | SIMD Shannon entropy, bigram entropy, batch analysis, C ABI |
| **Zig** | `fast-bridge.zig` | CapTP fast dispatch (410ns/call vs 56us MCP) |
| **Zig** | `nashator-captp.zig` | Game solver + botnet games in Zig SIMD |
| **Scheme** | `botnet-goblins.scm` | 3-actor triad (dga-analyzer, infra-mapper, disruption-planner) |
| **Scheme** | `nashator-goblins.scm` | 4-actor Nashator (games, solver, gf3, compose) |
| **TypeScript** | `nashator/src/dsl.ts` | 5 botnet games (propagation, DGA, blockchain, lifecycle, endgame) |

---

## Active Triads

| Triplet | Skills | Purpose |
|---------|--------|---------|
| **Security Core** | botnet-studies ⊗ blackhat-go ⊗ botnet-disruption | Attack/coordinate/defend |
| **Game-Theoretic** | botnet-studies ⊗ nashator ⊗ botnet-disruption | Equilibrium-driven defense |
| **Forensic** | reverse-engineering ⊗ network-forensics ⊗ botnet-disruption | Evidence chain |
| **Structural** | botnet-studies ⊗ captp ⊗ agent-o-rama | Capability-secured agents |

---

## Integration Paths

### Path A: DGA Detection Pipeline
```
Domain list → dga-analyzer.zig (SIMD entropy) → GF(3) trit classification
  → benign (-1) / uncertain (0) / DGA (+1)
  → ^dga-analyzer Goblins actor → promise pipeline
```

### Path B: Game-Theoretic Disruption
```
Botnet type → Nashator solver → Nash equilibrium
  → extract_defender_strategy → recommended actions
  → ^disruption-planner actor → multi-phase plan
```

### Path C: Capability-Hardened Network
```
IoT service → Goblins actor (POLA caps only)
  → compromise = gain only granted caps
  → no scan cap, no outbound cap, no firmware cap
  → lateral movement structurally impossible
```

### Path D: Operation Endgame Composition
```
Phase 1 (infra seizure) ; Phase 2 (demand-side) ; Phase 3 (adjacent)
  → seq(seq(infra, demand), adjacent) in Nashator DSL
  → each phase equilibrium feeds next phase strategy
```
