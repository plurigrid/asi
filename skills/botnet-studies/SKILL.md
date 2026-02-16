---
name: botnet-studies
description: Botnet architecture taxonomy, detection techniques, and defensive analysis. Covers C2 topologies, DGA analysis, fast-flux detection, P2P overlay mapping, blockchain C2, and ML-based traffic fingerprinting. Defensive research for understanding and countering distributed malicious infrastructure.
version: 1.0.0
metadata:
  trit: -1
  color: "#E03030"
---

# Botnet Studies: Defensive Architecture Analysis

**Status**: Active
**Trit**: -1 (VALIDATOR — analyzes and constrains adversarial infrastructure)
**Context**: Defensive security research, CTF, authorized pentesting, academic study

---

## Architecture Taxonomy

### Topologies

| Topology | Resilience | Disruption Difficulty | Key Weakness |
|----------|-----------|----------------------|-------------|
| **Centralized C2** | Low | Low (sinkhole/seize) | Single point of failure |
| **Fast-flux** | Medium | Medium (DNS rotation) | TTL analysis reveals pattern |
| **P2P overlay** | High | High (graph fragmentation) | High-degree node removal |
| **Hybrid** (C2 + P2P fallback) | High | High | Must disrupt both layers |
| **Blockchain C2** | Very High | Very High (immutable state) | On-chain pattern analysis |

### Modern Families (2025-2026)

| Family | Topology | Vector | Distinguishing Feature |
|--------|----------|--------|----------------------|
| Mirai variants (Gayfemboy, Jackskid, LZRD) | Centralized/Hybrid | IoT default creds, zero-days | Rust cross-compilation, 40K+ daily bots |
| Kimwolf | Centralized | Corporate/gov networks, Android TV | Dynamic C2 shifting |
| Aisuru | Centralized | IoT mass compromise | Record DDoS volume, real-time load shifting |
| Tsundere | Blockchain C2 | Game installer masquerade | Ethereum smart contract stores C2 URLs |
| Badbox 2.0 | Centralized | Pre-installed Android malware | 10M devices as residential proxies |
| Emotet | Centralized | Phishing → loader chain | Periodic resurrection post-takedown |

### Blockchain C2 (Emerging Threat)

```
Operator → 0 ETH tx → Smart Contract (state update: new C2 URL)
                              ↓
Bot → public RPC → read contract state → connect to new C2
```

Immutable. Cannot be seized. Traditional sinkholing fails.
Counter: on-chain pattern analysis, RPC endpoint monitoring, contract interaction fingerprinting.

---

## Detection Techniques

### DGA Analysis

Domain Generation Algorithms produce pseudo-random domains (thousands/day).
Only botmaster knows the seed → can pre-register the right ones.

| Method | Approach | Strengths |
|--------|----------|-----------|
| Feature engineering | Entropy, n-gram freq, consonant/vowel ratio → RF/XGBoost | Interpretable, fast |
| BiLSTM + CNN + Attention | Character-level sequence classification | No manual features |
| LLM fine-tuning (SFT) | GPT on domain character sequences | Low false positive rate |
| LLM in-context learning | Few-shot DGA family adaptation | Zero retrain for new families |
| GPT embedding + CNN | Dense vector representation → CNN classifier | Combines semantic + structural |

**Zig SIMD opportunity**: Domain entropy computation across batch of 10K domains.
Shannon entropy of character distribution — embarrassingly parallel, pure arithmetic.

### Fast-Flux Detection

| Signal | Normal DNS | Fast-Flux |
|--------|-----------|-----------|
| TTL | 3600-86400s | 0-300s |
| A-record count per query | 1-4 | 10-100+ over time |
| ASN diversity | 1-2 | 10-50+ |
| Geographic spread | 1-2 countries | 20+ countries |

### Traffic Fingerprinting

- Flow-level: packet size distribution, inter-arrival times
- Payload: encrypted channel fingerprints (JA3/JA4 TLS fingerprinting)
- Behavioral: connection patterns, beacon intervals, sleep jitter

### Honeypot/Honeynet

- Adaptive deception systems (federated honeypots)
- IoT-specific honeynets (Cowrie SSH, Dionaea SMB, Conpot SCADA)
- ML classifiers on honeypot log features

---

## Analysis Tools

| Tool | Role | Integration |
|------|------|-------------|
| **CAPE Sandbox** | Dynamic malware analysis (successor to Cuckoo) | Auto-unpack, config extract |
| **MISP** | Threat intelligence sharing (IOCs) | API for automated IOC ingestion |
| **TheHive** | Incident response case management | Integrates MISP + Cortex |
| **Cortex** | Observable analysis engine | 100+ analyzers (geoloc, reputation, sandbox) |
| **Zeek** | Network metadata extraction | Passive DNS, protocol logs, DGA detection |
| **Suricata** | IDS/IPS deep packet inspection | Real-time botnet traffic signatures |
| **Wazuh** | SIEM/EDR | Host-based detection, log correlation |

SOC stack: Wazuh + TheHive + Cortex + MISP + Zeek/Suricata + CAPE

---

## Game-Theoretic Framing

### Botnet as Open Game

```
     Attacker                    Defender
   ┌──────────┐              ┌──────────────┐
   │ Infect   │──payoffs──→  │ Detect       │
   │ C2 Comm  │              │ Sinkhole     │
   │ Exfil    │              │ Patch        │
   │ Monetize │              │ Takedown     │
   └──────────┘              └──────────────┘

Sequential composition: Infect ; C2 ; Payload ; Exfil
Monoidal product: Phishing ⊗ IoT_exploit ⊗ Supply_chain

Bayesian open games: incomplete information (which hosts compromised?)
Coplay function: defender backward analysis of attacker incentives
```

### Equilibrium Models

| Model | Structure | Application |
|-------|-----------|-------------|
| **Stackelberg** | Leader-follower (defender commits first) | Resource allocation across network segments |
| **FlipIt** | Stealth control-flipping | MTD timing decisions |
| **Colonel Blotto** | Simultaneous multi-target allocation | Monitoring budget distribution |
| **SIS epidemic** | Susceptible-Infected-Susceptible | Propagation dynamics + intervention |

### Nashator Integration

```scheme
;; Botnet attack-defense as open game via Nashator
(define botnet-game
  (DSL.game "botnet_attack_defense"
    (list (DSL.player "Attacker" +1 4)   ; 4 strategies: infect/c2/exfil/persist
          (DSL.player "Defender" -1 4))   ; 4 strategies: detect/sinkhole/patch/takedown
    ;; Payoff matrix from empirical data
    botnet-payoffs))

;; Compose with capability defense game
(define defended-game
  (DSL.seq botnet-game capability-defense-game))
```

---

## Capability-Based Defense (OCapN)

### Why Botnets Succeed

```
Ambient authority: process runs as user → inherits ALL user permissions
Compromise one process → lateral movement to everything user can access
```

### Why Capabilities Prevent This

```
Structural authority: process holds ONLY explicitly granted references
Compromise one process → attacker gets only those specific capabilities
No network scan cap → cannot discover other hosts
No outbound socket cap → cannot phone home to C2
No firmware write cap → cannot persist
```

### Goblins Actor as Hardened Endpoint

```scheme
(define (^iot-service bcom http-port-cap log-cap)
  "IoT service with ONLY the capabilities it needs.
   Cannot scan network. Cannot write firmware. Cannot phone home."
  (methods
    [(handle-request req)
     ;; Can only use http-port-cap and log-cap
     ;; Even if compromised, attacker gains nothing beyond these
     ($ log-cap write (format "request: ~a" req))
     (serve-response http-port-cap req)]))
```

---

## GF(3) Triads

```
reverse-engineering (-1) ⊗ blackhat-go (0) ⊗ botnet-disruption (+1) = 0 ✓
botnet-studies (-1) ⊗ network-forensics (0) ⊗ botnet-disruption (+1) = 0 ✓
botnet-studies (-1) ⊗ captp (0) ⊗ agent-o-rama (+1) = 0 ✓
counter-surveillance (-1) ⊗ botnet-studies (-1) ⊗ nashator (0) → needs +2 = two generators
```

---

## References

- IEEE S&P 2025: "Game Theory in Distributed Systems Security" (arXiv:2309.01281)
- Disclosing.Observer 2026: 22.3M domains sinkholed in 2025
- Operation Endgame: Phases 1-3 (May 2024 → Nov 2025)
- Tsundere botnet: Ethereum smart contract C2
- CAPE Sandbox: capev2.readthedocs.io
- Spritely Institute: "Heart of Spritely" whitepaper
