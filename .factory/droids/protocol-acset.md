---
name: protocol-acset
description: Model decentralized protocols as attributed C-sets for compositional analysis, interoperability design, and protocol evolution. Apply categorical mathematics to P2P infrastructure.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Protocol ACSet: Compositional P2P Protocol Design

Model **decentralized and P2P protocols** as **attributed C-sets** (categorical data structures) to enable compositional analysis, verify interoperability, and design protocol evolution narratives.

## Core Insight

Rather than viewing protocols as isolated systems, **Protocol ACSet** treats them as compositional objects in a category where:
- **Objects** = Protocols (IPFS, Iroh, Matrix, Nostr, etc.)
- **Morphisms** = Protocol bridges and adapters
- **Attributes** = Protocol properties (transport, encryption, topology)
- **Composition** = How protocols stack and interoperate

## What is an Attributed C-Set?

An **Attributed C-set** is a graph structure with:
- **Vertices** (objects) and **edges** (relationships)
- **Attributes** (data attached to vertices/edges)
- **Functorial structure** (composition preserving operations)

Example: IPFS as an ACSet

```
objects:
  - Object(name="ipfs", type="content-distribution", transport="tcp/quic")

morphisms:
  - Morphism(from="ipfs-node", to="ipfs-peer", label="connect")
  - Morphism(from="content-hash", to="blob", label="address")

attributes:
  - (ipfs): [encryption="aes", topology="dht", consensus="none"]
  - (ipfs→peer): [latency=50ms, bandwidth=100mbps]
```

## Protocol Categories (Objects)

Every protocol maps to one or more **protocol categories**:

```
ProtocolACSet = {
  objects: {
    transport,          // TCP, QUIC, UDP, WebRTC
    security,           // TLS, Noise, WireGuard
    topology,           // P2P, federated, hybrid
    identity,           // Public keys, DIDs, domains
    data_model,         // Append-only, CRDT, graph
    discovery,          // DHT, mDNS, relay, centralized
    incentive           // Proof-of-work, Filecoin, none
  }
}
```

## Key Protocols as ACSet Objects

### Transport Layer

```
TRANSPORT = {
  objects: [TCP, QUIC, UDP, WebSocket, WebRTC],
  morphisms: {
    TCP.upgrade_to(QUIC),      // 0-RTT, connection migration
    UDP.extend