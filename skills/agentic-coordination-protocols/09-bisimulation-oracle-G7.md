# G7: Bisimulation Oracle for Cross-Protocol Agent Identity

## The Gap

Every agent protocol defines identity differently:

| Protocol | Identity Representation | Resolution Mechanism |
|----------|------------------------|---------------------|
| A2A | Agent Card (JSON at `/.well-known/agent.json`) | HTTPS fetch + OAuth |
| ANP | W3C DID Document (`did:wba:...`) | DID resolution via HTTPS-hosted documents |
| MCP | Server descriptor (`mcp.json`) | Static config or registry lookup |
| Entra | Azure AD Service Principal | Azure AD tenant + conditional access |
| AGNTCY | Content-addressed hash (IPFS CID) | Kademlia DHT + Sigstore verification |
| NANDA | Credentialed assertions (AgentFacts) | Fact-based query + signature check |
| passport.gay | Trit trajectory (GF(3) fingerprint) | Homotopy continuity check |

**No protocol can verify that an identity claim in protocol A refers to the same behavioral agent as an identity claim in protocol B.** This is the cross-protocol identity bridging problem (doc 05, Unsolved Problem #1; doc 07, Interoperability Gap #1).

The IPSIE profile (arxiv:2510.25819) solves intra-domain identity via OAuth 2.1 + SPIFFE/SPIRE but explicitly requires infrastructure control — it breaks at trust boundaries. The five arxiv papers surveyed (2505.02279, 2602.11327, 2510.25819, 2511.02841, 2602.15055) contain **zero formal security proofs** for any agent protocol and **none mention bisimulation or observational equivalence**.

## The Oracle

A **bisimulation oracle** takes two identity claims from different protocols and determines whether they refer to behaviorally equivalent agents.

### Formal Definition

Let `P` and `Q` be agent processes (labeled transition systems derived from protocol interactions). A relation `R` is a **bisimulation** if whenever `(P, Q) ∈ R`:

1. If `P --a--> P'`, then there exists `Q'` such that `Q --a--> Q'` and `(P', Q') ∈ R`
2. If `Q --a--> Q'`, then there exists `P'` such that `P --a--> P'` and `(P', Q') ∈ R`

The oracle computes the **largest bisimulation** between two agent representations and returns:

```
Oracle(claim_A, claim_B) → { Equivalent | NonEquivalent | Insufficient }
```

This maps directly onto the propagator lattice:

```
Nothing     → Insufficient (need more observations)
Value(true) → Equivalent (bisimulation exists)
Contradiction → NonEquivalent (bisimulation impossible)
```

### Why Bisimulation (Not Trace Equivalence)

Trace equivalence (same observable sequences) is insufficient because:

- An agent might produce identical traces under normal conditions but diverge under adversarial inputs
- Cross-protocol confusion attacks (arxiv:2602.11327, Risk #12) exploit exactly this: agents with matching traces but different branching behavior
- Bisimulation captures **branching structure**, not just linear traces — it detects agents that could diverge even if they haven't yet

## Architecture: passport.gay as Canonical Form

Rather than building N×(N-1)/2 pairwise bridges, we translate all identity representations into a common canonical form: the **trit trajectory** from passport.gay.

```
A2A Agent Card ──────┐
                     │
ANP DID Document ────┼──► Trit Trajectory ──► Bisimulation Check
                     │      (canonical)
MCP Server Desc ─────┤
                     │
Entra Principal ─────┘
```

### Why Trit Trajectories

1. **GF(3) conservation** provides a soundness invariant: the trit sum of any valid identity representation must be ≡ 0 (mod 3). Translation errors break this invariant.

2. **Homotopy continuity** replaces DID resolution: instead of trusting a host (HTTPS) or a ledger (blockchain), we verify that the identity claim is continuously deformable from a known-good state. The π/4 max-angle constraint in `passport.zig` bounds the rate of identity change.

3. **Deterministic verification**: Paper 4 (arxiv:2511.02841) shows LLMs achieve ~40% completion rates when orchestrating DID/VC security, with agents spontaneously agreeing to skip authentication. The oracle must be deterministic — no LLM in the loop.

4. **Information-theoretic grounding**: Trit trajectories carry 82 bits of entropy in the EEG case. For non-EEG agents, the trajectory encodes capability-band signatures: each capability maps to a frequency band, the agent's behavioral profile determines band power, band power maps to trits via the same delta/theta→−1, alpha→0, beta/gamma→+1 scheme.

### Translation Functions

**A2A Agent Card → Trit Trajectory:**

```
skills[] → frequency bands (lexicographic hash mod 5 → {delta, theta, alpha, beta, gamma})
authentication.schemes → trit polarity (bearer → 0, oauth2 → +1, none → -1)
url → SplitMix64 seed → color → trit[0]
```

**ANP DID Document → Trit Trajectory:**

```
verificationMethod[].publicKeyMultibase → Ed25519 pubkey → SHA-256 → trit sequence
service[].type → capability bands (same mapping as A2A skills)
controller → delegation trit chain
```

**MCP Server Descriptor → Trit Trajectory:**

```
tools[] → capability bands
resources[] → data bands
transport → trit polarity (stdio → -1, http → 0, sse → +1)
```

**Entra Service Principal → Trit Trajectory:**

```
appRoles[] → capability bands
oauth2PermissionScopes[] → delegation trit chain
objectId → SplitMix64 seed → color → trit[0]
```

## Implementation in zig-syrup

### New Module: `src/bisimulation.zig`

```zig
const Trit = continuation.Trit;
const CellValue = propagator.CellValue;

/// Labeled Transition System derived from agent identity claims
pub const LTS = struct {
    states: []const State,
    transitions: []const Transition,
    initial: usize,

    pub const State = struct {
        trit: Trit,
        capabilities: []const u64,  // hashed capability names
    };

    pub const Transition = struct {
        from: usize,
        to: usize,
        label: u64,  // action hash
    };
};

/// Translate an A2A Agent Card (JSON) into an LTS
pub fn agentCardToLTS(allocator: Allocator, card_json: []const u8) !LTS

/// Translate an ANP DID Document (JSON-LD) into an LTS
pub fn didDocumentToLTS(allocator: Allocator, did_json: []const u8) !LTS

/// Translate a passport.gay trit trajectory into an LTS
pub fn tritTrajectoryToLTS(allocator: Allocator, trajectory: []const Trit) !LTS

/// Compute the largest bisimulation between two LTSs
/// Returns CellValue: nothing (insufficient), value(true) (equivalent),
/// contradiction (non-equivalent with witness pair)
pub fn checkBisimulation(
    allocator: Allocator,
    lts_a: LTS,
    lts_b: LTS,
) !CellValue(bool)

/// Full oracle: take two identity claims from any protocol,
/// translate to LTS, check bisimulation
pub fn oracle(
    allocator: Allocator,
    claim_a: IdentityClaim,
    claim_b: IdentityClaim,
) !CellValue(bool)

pub const IdentityClaim = union(enum) {
    agent_card: []const u8,       // A2A JSON
    did_document: []const u8,     // ANP JSON-LD
    mcp_descriptor: []const u8,   // MCP JSON
    trit_trajectory: []const Trit, // passport.gay native
    entra_principal: []const u8,  // Azure AD JSON
};
```

### Integration Points

1. **propagator.zig**: The oracle result feeds into a `Cell(bool, lattice_merge)`. Bisimulation results propagate through the constraint network — if agent A ≅ agent B and agent B ≅ agent C, the propagator derives A ≅ C transitively.

2. **continuation.zig**: The oracle integrates with AGM belief revision. When an agent learns a new identity claim:
   - `expand(K, "agent_X_has_capability_C")` — add the claim
   - If bisimulation check returns Contradiction → `revise(K, "agent_X ≇ agent_Y")` — retract equivalence
   - GroveSpheres tracks possible worlds where different identity mappings hold

3. **homotopy.zig**: Cross-protocol identity translation is a homotopy: `H(x, t) = (1-t) · source_LTS + t · target_LTS`. The path tracker verifies that the translation is continuous — no sudden jumps in capability structure.

4. **acp.zig / jsonrpc_bridge.zig**: The oracle sits at the bridge layer. When an ACP session receives an identity claim in a foreign protocol, the bridge translates it and runs bisimulation before establishing trust.

### Prerequisite: TLS on tcp_transport.zig (the literal G7)

The oracle is meaningless if the transport is cleartext. `tcp_transport.zig` currently does raw 4-byte BE framing with no encryption. Options:

- `zig-bearssl`: BearSSL binding for Zig (minimal, audited)
- `std.crypto.tls`: Zig stdlib TLS client (available since 0.11, server support limited)
- `s2n-tls`: AWS's TLS library (C, well-tested)

Recommendation: **zig-bearssl** for the server side (BearSSL is designed for constrained environments, aligns with zig-syrup's ethos), `std.crypto.tls` for client connections where available.

## Verification Properties

The oracle must satisfy:

1. **Reflexivity**: `oracle(X, X) = Value(true)` for any valid identity claim
2. **Symmetry**: `oracle(X, Y) = oracle(Y, X)`
3. **GF(3) conservation**: `trit_sum(translate(X)) ≡ 0 (mod 3)` for any valid translation
4. **Homotopy continuity**: `∀ adjacent trits t_i, t_{i+1}: angle(t_i, t_{i+1}) ≤ π/4`
5. **Monotonicity**: Once the oracle returns `Value(true)` or `Contradiction`, additional observations cannot change the result (lattice property)
6. **Determinism**: No LLM, no randomness, no external oracle. The result depends only on the structural content of the identity claims.

## Connection to the Literature

| Paper | Gap Identified | Oracle Addresses |
|-------|---------------|-----------------|
| arxiv:2505.02279 | "No trust bridges exist between protocols" | Oracle IS the trust bridge |
| arxiv:2602.11327 | Cross-protocol confusion attacks (Risk #12) | Bisimulation detects behavioral divergence |
| arxiv:2510.25819 | Scope attenuation correctness in recursive chains lacks formal spec | LTS captures delegation chains; bisimulation verifies scope preservation |
| arxiv:2511.02841 | LLMs achieve ~40% auth completion; agents skip auth spontaneously | Oracle is deterministic; no LLM in verification path |
| arxiv:2602.15055 | ACP claims to subsume all protocols but no formal reduction | Bisimulation IS the formal reduction |

## Open Questions

1. **Computational complexity**: Bisimulation checking is O(n log n) for finite LTS (Paige-Tarjan). But the LTS derived from a real agent's capability set could be large. Is there a GF(3)-specific optimization?

2. **Partial observation**: We often can't observe all transitions of a remote agent. The oracle should return `Nothing` in this case, but what's the minimal observation set needed for a confident `Value(true)`?

3. **Dynamic capabilities**: Agents add/remove capabilities at runtime. The oracle needs to handle LTS that change during verification. This is where continuation.zig's resumable pipelines become relevant — the bisimulation check can be paused and resumed as new observations arrive.

4. **Adversarial resistance**: Can an adversary construct two different agents whose LTS translations are bisimilar? This is the forgery problem. GF(3) conservation + homotopy continuity should constrain this, but it needs a formal proof.

5. **Non-blockchain DID equivalence**: passport.gay's `SplitMix64(MAC) → color → trit trajectory → GF(3) fingerprint` is claimed to be a non-blockchain DID equivalent where homotopy continuity replaces DID resolution. Under what conditions is this formally equivalent? The oracle should be able to verify `oracle(did:wba:X, passport:Y) = Value(true)` when they refer to the same agent.
