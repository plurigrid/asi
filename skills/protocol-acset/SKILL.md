---
name: protocol-acset
description: Model decentralized protocols as attributed C-sets for compositional analysis, interoperability design, and protocol evolution. Apply categorical mathematics to P2P infrastructure.
category: development
author: bmorphism
license: MIT
metadata:
  trit: 0
  source: custom
  tags: [acset, protocols, category-theory, p2p, composition, interoperability]
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
    UDP.extend_to(QUIC),       // Congestion control, ordering
    WebSocket.fallback_to(TCP) // Browser compatibility
  },
  attributes: {
    latency: latency,
    connection_setup: rtt_count,
    encryption_native: bool
  }
}
```

### Security Layer

```
SECURITY = {
  objects: [TLS, Noise, WireGuard, Signal_Double_Ratchet],
  morphisms: {
    Noise.adapt_to(libp2p),    // Generic handshake
    WireGuard.operate_at(layer2),  // VPN vs app layer
    Signal.strengthen_with(perfect_forward_secrecy)
  },
  attributes: {
    forward_secrecy: bool,
    post_quantum_resistant: bool,
    overhead_bytes: int
  }
}
```

### Topology Layer

```
TOPOLOGY = {
  objects: [P2P_Direct, Federated, Relay_Based, Hybrid],
  morphisms: {
    P2P_Direct.fallback_to(Relay),  // Firewall bypass
    Federated.include_P2P_option,   // FEP-1024 pattern
    Relay.optimize_with_DHT         // Peer discovery
  },
  attributes: {
    centralization_risk: 0..1,
    scalability: metric,
    latency_vs_centralization: tradeoff
  }
}
```

### Identity Layer

```
IDENTITY = {
  objects: [PublicKey, DID, Domain, Account],
  morphisms: {
    PublicKey.trustless(),         // No registration
    DID.composable_with(VerificationMethod),
    Domain.delegate_to(Protocol),  // FQDN ownership
    Account.require_centralized_server()
  },
  attributes: {
    portability: bool,
    user_controlled: bool,
    recovery_possible: bool
  }
}
```

### Data Model Layer

```
DATA_MODEL = {
  objects: [AppendOnly, CRDT, GraphDB, RDF, MerkleDAG],
  morphisms: {
    AppendOnly.compose_with(CRDT),     // Git + concurrent edits
    CRDT.guarantee(CommutativeMonoid), // Math foundation
    MerkleDAG.content_address(),       // IPFS pattern
    GraphDB.query_with(SPARQL)
  },
  attributes: {
    eventual_consistency: bool,
    conflict_resolution: strategy,
    query_capability: query_language
  }
}
```

## Composition Laws

Protocols compose along **morphisms** following categorical laws:

### Associativity (Functorial Composition)

```
(IPFS → IPNS → ENS) = IPFS → (IPNS → ENS)
```

Both paths represent content resolution chains—they should give the same result.

### Identity (No-op Morphism)

```
Protocol ⊗ Identity = Protocol
```

Example: A protocol using transparent relays should function identically.

### Yoneda Lemma (Composition Universality)

A protocol's properties are determined by how it relates to all other protocols:

```
IPFS_properties = ∀P: morphisms(P → IPFS) × morphisms(IPFS → P)
```

If two protocols have identical composition patterns with all others, they're equivalent.

## Real Protocols as ACSet Instances

### IPFS (Content Distribution)

```julia
# ACSet Definition
@acset_type IPFSProtocol <: AbstractACSet begin
  (Node, Content, Peer)
  node_has_content::EdgeVertexDouble
  node_connects_peer::EdgeVertexDouble
  hash_of::EdgeVertex
end

# Instance
ipfs = IPFSProtocol()
add_node!(ipfs, name="node-1", storage=1_000_000)
add_content!(ipfs, hash="baf...", size=50_000)
add_morphism!(ipfs, :node_has_content, 1, 1)  # Node stores content
```

### Iroh (P2P Transport + Blobs)

```julia
@acset_type IrohProtocol <: AbstractACSet begin
  (Endpoint, Peer, Blob, Document)
  endpoint_dials::EdgeVertex
  peer_stores_blob::EdgeVertex
  document_syncs::EdgeVertex
  has_relay_fallback::EdgeAttribute
end

iroh = IrohProtocol()
add_endpoint!(iroh, node_id="node-abc", relay_enabled=true)
add_peer!(iroh, peer_id="peer-xyz")
add_blob!(iroh, hash="quic-native")
add_morphism!(iroh, :endpoint_dials, 1, 1)  # Hole punching
```

### Matrix (Federated Messaging)

```julia
@acset_type MatrixProtocol <: AbstractACSet begin
  (HomeServer, User, Room, Message)
  user_on_server::EdgeVertex
  message_in_room::EdgeVertex
  server_federates::EdgeVertex
  e2e_encrypted::EdgeAttribute
end

matrix = MatrixProtocol()
add_server!(matrix, domain="matrix.org", e2e=true)
add_user!(matrix, id="@alice:matrix.org")
add_morphism!(matrix, :server_federates, homeserver_alice, homeserver_bob)
```

## Protocol Bridges (Morphisms)

Connect incompatible protocols through adapters:

### Bridge: IPFS → ActivityPub (FEP-1024 Pattern)

```julia
function ipfs_to_activitypub_bridge(ipfs::IPFSProtocol, ap::ActivityPubProtocol)
  # Map IPFS hash to ActivityPub URL
  bridge = ACSetMorphism()

  for content in ipfs.contents
    url = "ap://link?ipfs=$(content.hash)"
    add_morphism!(bridge, :ipfs_content_to_ap_url, content, url)
  end

  return bridge
end
```

### Bridge: Nostr → Matrix (Relay Adaptation)

```julia
function nostr_to_matrix_bridge(nostr::NostrProtocol, matrix::MatrixProtocol)
  # Nostr uses relays, Matrix uses homeservers
  # Adapt relay infrastructure to room subscriptions

  bridge = ACSetMorphism()

  for relay in nostr.relays
    room = add_room!(matrix, name="relay-$(relay.url)")
    add_morphism!(bridge, :relay_to_room, relay, room)
  end

  return bridge
end
```

## Composing Multiple Protocols (Stacking)

**Protocol stacking**: Use ActivityPub + IPFS + Hypercore simultaneously

```julia
# Define the stack
protocol_stack = [
  ActivityPub(),  # Social/federation layer
  IPFS(),        # Content distribution layer
  Hypercore()    # Offline-first data layer
]

# Create composition morphisms
for i in 1:length(protocol_stack)-1
  compose!(protocol_stack[i], protocol_stack[i+1])
  # Each layer morphs through adapters
end

# Result: Hybrid protocol with benefits of all three
```

**Properties preserved through composition**:
- ✅ Decentralization (ActivityPub)
- ✅ Permanent links (IPFS)
- ✅ Offline-first sync (Hypercore)

## Verification: Interoperability Testing

Use ACSet structure to verify protocols can compose without conflicts:

```julia
function can_interoperate(p1::Protocol, p2::Protocol)
  # Check functor compatibility
  return (
    compatible_transport(p1, p2) &&
    compatible_security(p1, p2) &&
    compatible_topology(p1, p2) &&
    compatible_identity(p1, p2) &&
    morphisms_are_natural(p1, p2)
  )
end

# Example
can_interoperate(Nostr(), Matrix())  # true (both message-based)
can_interoperate(IPFS(), Nostr())    # false (content vs events)
can_interoperate(IPFS(), ActivityPub())  # true (FEP-1024)
```

## Protocol Evolution Narratives (Bumpus Sheaves)

Apply **Bumpus sheaves on time categories** to understand protocol evolution:

```
Time ──────────────────────────────
  t=2010: Bitcoin (proof-of-work)
    ↓ (evolves with new features)
  t=2014: Ethereum (smart contracts)
    ↓ (layer 2 solutions emerge)
  t=2019: IPFS (content distribution)
    ↓ (bridges to social networks)
  t=2024: ActivityPub + IPFS (hybrid)
    ↓ (emerging toward full P2P)
  t=2025: Multi-protocol stacks
```

Each **time interval** in this narrative is a **categorical sheaf** that captures the state of all protocols at that moment and their mutual morphisms.

## GF(3) Balance in Protocols

Assign **GF(3) trits** to classify protocol design philosophy:

| Protocol | Type | Trit | Role |
|----------|------|------|------|
| IPFS | Content distrib | +1 | PLUS (generative, permanent) |
| Matrix | Messaging | 0 | ERGODIC (balanced, federated) |
| Secure Scuttlebutt | Social | −1 | MINUS (observational, offline-first) |
| Nostr | Social relays | 0 | ERGODIC (balanced observation/participation) |
| Iroh | Transport | +1 | PLUS (enables new P2P applications) |

**Conservation law**: Sum of trits in a protocol stack = 0 (mod 3)

**Example composition**: `IPFS(+1) ⊗ Matrix(0) ⊗ SSB(−1) = 0 ✓`

## Building Applications with Protocol ACSet

### Step 1: Model Your Application

```julia
app_acset = ProtocolStackACSet(
  layers=[
    Protocol(:data, :crdt, :hypercore),
    Protocol(:identity, :public_key, :portable),
    Protocol(:discovery, :dht, :p2p),
    Protocol(:transport, :quic, :encrypted)
  ]
)
```

### Step 2: Verify Composition

```julia
verify_composition(app_acset)  # Checks trit balance, morphism compatibility
```

### Step 3: Implement Stack

```julia
# Map ACSet to code
for protocol in app_acset.layers
  import_protocol(protocol)
  bind_to_framework(protocol)
end

app = build_from_acset(app_acset)
```

## Use Cases

| Use Case | Protocol Stack |
|----------|----------------|
| **Decentralized Social** | ActivityPub + IPFS + Hypercore |
| **Offline-First Collab** | CRDT (Yjs) + Hypercore + Holepunch |
| **Content Archive** | IPFS + IPNS + Filecoin |
| **Private Messaging** | Signal (E2E) + Matrix (Federation) + Tor (Privacy) |
| **File Sync** | Syncthing (P2P) + IPFS (Distribution) + Ceph (Backup) |
| **Data Sovereignty App** | Iroh (Transport) + IPFS (Storage) + DIDs (Identity) |

## Mathematical Foundations

### Functorial Laws

Protocols respect **functorial composition**:

```
Protocols → Categories
  F: Protocol → Category
  G: Category → Properties

G(F(IPFS)) = Properties(IPFS)
G(F(Matrix)) = Properties(Matrix)
```

### Natural Transformations

When protocols bridge, they form **natural transformations**:

```
IPFS ──bridge──> ActivityPub
  │                  │
  v (F)              v (G)
Properties    →    Properties
```

The bridge is "natural" if it preserves all protocol properties without loss.

## Resources for Deep Dive

- **Category Theory**: MacLane, "Categories for the Working Mathematician"
- **Sheaves on Time Categories**: Bumpus, et al. papers
- **ACSet Theory**: Evan Patterson's work at Topos Institute
- **Protocol Design**: IETF specifications, protocol RFCs

## Conclusion

**Protocol ACSet** enables:

- ✅ **Formal composition** of protocols without ad-hoc integration
- ✅ **Verification** that protocols can safely interoperate
- ✅ **Evolution narratives** showing protocol families over time
- ✅ **Optimal stacking** guided by categorical mathematics
- ✅ **Data sovereignty** through principled system design

Rather than asking "which protocol should I use?", ask "what properties do I need, and how do I compose protocols to achieve them?"




## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Annotated Data
- **anndata** [○] via bicomodule
  - Hub for annotated matrices

### Bibliography References

- `general`: 734 citations in bib.duckdb

## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: ⊗
Kan Role: Adj
Color: #26D826
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

This ensures compositional coherence in the Cat# equipment structure.
