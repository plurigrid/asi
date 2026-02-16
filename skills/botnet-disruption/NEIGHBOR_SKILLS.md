# Botnet Disruption: Neighbor Skills

**Date**: 2026-02-13
**Framework**: GF(3) Neighborhood Awareness

---

## Tier 1: Core Security Triad

| Skill | Trit | Role | Interface | Morphism |
|-------|------|------|-----------|----------|
| **botnet-studies** | -1 | VALIDATOR | Architecture taxonomy, DGA analysis | `extractFeatures(domain)` |
| **blackhat-go** | 0 | COORDINATOR | Go tooling for network ops | `tool_dispatch(technique)` |
| **botnet-disruption** | +1 | GENERATOR | Takedown plans, sinkholing, legal | `plan_disruption(botnet_type)` |

**GF(3) Check**: (-1) + (0) + (+1) = 0

---

## Tier 2: Equilibrium-Driven Disruption

| Skill | Trit | Role | Interface |
|-------|------|------|-----------|
| **nashator** | 0 | Nash solver for attack/defense games | `nashator_solve(game)` |
| **open-games** | +1 | Compositional game framework | `seq(phase1, phase2)` |
| **eip1559-game** | +1 | Mechanism design patterns | `base_fee_game(validators, users)` |

### Nash Equilibria for Disruption Planning

| Game | Defender Optimal | Attacker Weakness | Payoff |
|------|-----------------|-------------------|--------|
| **Botnet Propagation** | detect (30%) + isolate (31%) | scan over-reliance | Mixed |
| **DGA Cat-and-Mouse** | LLM detection (73%) | hybrid DGA still 66% | Arms race |
| **Blockchain C2** | chain monitoring (43%) | gas fee traceability | Defender edge |
| **Op Endgame Phase 1** | sinkhole (43%) | migration overhead | +0.56 defender |
| **Op Endgame Phase 2** | charge (44%) | persona-identity link | Slight attacker edge |
| **Op Endgame Phase 3** | charge (39%) + defer (61%) | denial ineffective | Need intel |

**Key finding**: LLM-based DGA detection dominates all other methods (73% weight in equilibrium).
Blockchain C2 monitoring is the strongest single defender strategy across all games.

---

## Tier 3: Infrastructure & Forensics

| Skill | Trit | Role | Interface |
|-------|------|------|-----------|
| **reverse-engineering** | -1 | Malware binary analysis | `disassemble(binary)` |
| **network-forensics** | 0 | Traffic capture & analysis | `pcap_analyze(capture)` |
| **captp** | 0 | OCapN wire protocol | `deliver(ref, method, args)` |

**Triplet**: reverse-engineering (-1) + network-forensics (0) + botnet-disruption (+1) = 0

---

## Tier 4: Legal & Coordination

| Skill | Trit | Role | Interface |
|-------|------|------|-----------|
| **counter-surveillance** | -1 | Adversary tracking | `monitor(indicators)` |
| **goblins-adapter** | 0 | Capability bridge | `register_plugin(disruption_tools)` |
| **agent-o-rama** | +1 | Autonomous agent orchestration | `spawn(disruption_agent, caps)` |

---

## Implementation Substrates

| Substrate | File | What it provides |
|-----------|------|-----------------|
| **Zig** | `dga-analyzer.zig` | Batch DGA entropy (10K domains/100us), C ABI |
| **Zig** | `nashator-captp.zig` | SIMD fictitious play solver, botnet game payoffs |
| **Zig** | `fast-bridge.zig` | CapTP dispatch (135x faster than MCP) |
| **Scheme** | `botnet-goblins.scm` | ^disruption-planner actor, multi-phase planning |
| **TypeScript** | `nashator/src/dsl.ts` | operationEndgame(), botnetLifecycle() |

---

## Active Triads

| Triplet | Skills | Purpose |
|---------|--------|---------|
| **Security Core** | botnet-studies ⊗ blackhat-go ⊗ botnet-disruption | Study/tool/disrupt |
| **Forensic Chain** | reverse-engineering ⊗ network-forensics ⊗ botnet-disruption | Evidence→action |
| **Game-Theoretic** | counter-surveillance ⊗ nashator ⊗ botnet-disruption | Observe→equilibrium→act |
| **Capability Defense** | botnet-studies ⊗ captp ⊗ botnet-disruption | Analyze→transport→disrupt |

---

## Disruption Workflow (4-Phase)

### Phase 0: Intelligence → botnet-studies (-1)
```
DGA analysis (dga-analyzer.zig) → domain classification
Passive DNS + honeypot → C2 protocol capture
MISP → aggregate threat intel
```

### Phase 1: Mapping → blackhat-go (0) / network-forensics (0)
```
^infra-mapper actor → DNS + Whois + BGP + CT logs
Promise pipeline: 4 queries, 1 RTT via CapTP
Infrastructure reuse detection → shared hosting pivots
```

### Phase 2: Strategy → nashator (0)
```
Select game model (propagation / DGA / blockchain / endgame)
Solve Nash equilibrium → defender optimal mixed strategy
Extract actionable recommendations
```

### Phase 3: Action → botnet-disruption (+1)
```
^disruption-planner actor → multi-phase plan
DNS sinkhole + server seizure + BGP null-route
Post-disruption: victim notify, DB analysis, persona linking
```

**GF(3) through pipeline**: (-1) + (0) + (0) + (+1) = 0
