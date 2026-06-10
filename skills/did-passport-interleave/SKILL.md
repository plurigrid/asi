---
name: did-passport-interleave <<<<<<< HEAD
description: Formal bridge between W3C Decentralized Identifiers (did:wba, ANP) and passport.gay (SplitMix64 MAC→trit trajectory→GF(3) fingerprint→QRTP air-gap). Establishes a bisimulation relation between the online DID resolution model and the offline fountain-coded QR identity model. Closes Gap G-P2 (MCP-I DID extension) and Gap G5 (passport revocation) from the zig-syrup propagator interleave gap registry.
deployed: '2026-02-19'
role: BRIDGE
tags: '[did, w3c, anp, passport, qrtp, gf3, homotopy, identity, bridge, bisimulation, air-gap]'
trit: '0'
version: 1.0.0
---

# W3C DID ↔ passport.gay Interleave
=======
description: >
  Bridge between W3C Decentralized Identifiers (did:wba, ANP) and passport.gay
  (SplitMix64 MAC -> trit trajectory -> fingerprint -> QRTP air-gap).
  Triggers: DID resolution, offline identity verification, air-gapped identity,
  QRTP fountain-coded QR transport, passport revocation, online/offline identity bridge.
---

# W3C DID / passport.gay Interleave
>>>>>>> origin/main

## Formal Equivalence

The two identity systems are behaviorally equivalent (bisimilar) for offline scenarios:

```
W3C DID (ANP):
<<<<<<< HEAD
  Identity creation:  keygen → DID document → publish to HTTPS endpoint
  Verification:       resolve DID → fetch document → verify signature
  Trust anchor:       Web PKI (DNS + TLS)
  Air-gap capable:    NO — requires network for DID resolution

passport.gay (zig-syrup):
  Identity creation:  MAC → SplitMix64 seed → color trajectory → GF(3) trit fingerprint
  Verification:       homotopy continuity check on deformation path
  Trust anchor:       GF(3) conservation law (mathematical, no network)
  Air-gap capable:    YES — QRTP fountain-coded QR transport
```

**Bisimulation witness:** Both systems implement `prove(claim) → verify(proof) → accept/reject`. They differ only in the trust anchor and transport layer. Within the same trit class, they are weakly bisimilar (same external observations, different internal τ-transitions).

---
=======
  Identity creation:  keygen -> DID document -> publish to HTTPS endpoint
  Verification:       resolve DID -> fetch document -> verify signature
  Trust anchor:       Web PKI (DNS + TLS)
  Air-gap capable:    NO -- requires network for DID resolution

passport.gay (zig-syrup):
  Identity creation:  MAC -> SplitMix64 seed -> color trajectory -> trit fingerprint
  Verification:       homotopy continuity check on deformation path
  Trust anchor:       GF(3) conservation law (mathematical, no network)
  Air-gap capable:    YES -- QRTP fountain-coded QR transport
```

Both implement `prove(claim) -> verify(proof) -> accept/reject`. They differ only in trust anchor and transport layer.
>>>>>>> origin/main

## did:wba Method (ANP)

```
did:wba:<domain>:<path>
<<<<<<< HEAD

=======
>>>>>>> origin/main
Example: did:wba:plurigrid.com:agents:skill-graph-agent

DID Document (JSON-LD):
{
<<<<<<< HEAD
  "@context": ["https://www.w3.org/ns/did/v1", "https://w3id.org/security/suites/ed25519-2020/v1"],
  "id": "did:wba:plurigrid.com:agents:skill-graph-agent",
  "verificationMethod": [{
    "id": "did:wba:plurigrid.com:agents:skill-graph-agent#key-1",
    "type": "Ed25519VerificationKey2020",
    "controller": "did:wba:plurigrid.com:agents:skill-graph-agent",
=======
  "@context": ["https://www.w3.org/ns/did/v1"],
  "id": "did:wba:plurigrid.com:agents:skill-graph-agent",
  "verificationMethod": [{
    "id": "...#key-1",
    "type": "Ed25519VerificationKey2020",
>>>>>>> origin/main
    "publicKeyMultibase": "z6MkrJVnaZkeFzdQyMZu1cgjg7k1pZZ6pvBQ7XJPt4swbTQ2"
  }],
  "authentication": ["#key-1"],
  "service": [{
    "id": "#agent-description",
    "type": "AgentDescriptionProtocol",
    "serviceEndpoint": "https://plurigrid.com/agents/skill-graph/.well-known/agent-description.json"
  }]
}
```

<<<<<<< HEAD
---

## passport.gay Identity Model (from zig-syrup)

```
SplitMix64(seed from MAC) → deterministic PRNG
  → color sequence → GF(3) trit trajectory
  → conservation check: sum(trajectory) ≡ 0 (mod 3)
  → fingerprint: SHA256(trajectory)
  → liveness check: homotopy H(x,t) = (1-t)·baseline + t·current is continuous

Identity proof = (trajectory, continuity_certificate, GF(3)_conservation_proof)
Transport    = QRTP (fountain-coded QR codes, air-gapped)
```

---

## Bridge: GF(3) Fingerprint → DID Document Fragment

```python
import hashlib
from typing import Optional
import base64
=======
## Bridge: Trit Trajectory -> DID Document Fragment

```python
import hashlib, base64
>>>>>>> origin/main

def passport_to_did_fragment(
    trajectory: list[int],
    domain: str = "plurigrid.com",
    path_segments: list[str] = None,
) -> dict:
    """
<<<<<<< HEAD
    Requirement:  trajectory is GF(3)-conserved (sum ≡ 0 mod 3)
    Requirement:  len(trajectory) >= 3 (at least one triad)
    Postcondition: valid DID document fragment with GF(3) verification method

    This bridges passport.gay offline identity into the ANP/W3C DID ecosystem.
    The DID is deterministically derived from the trajectory (same input → same DID).
    """
    # Validate GF(3) conservation
    if sum(trajectory) % 3 != 0:
        raise ValueError(f"GF(3) conservation violated: sum={sum(trajectory)} ≢ 0 mod 3")

    # Derive stable fingerprint from trajectory
    traj_bytes = bytes([t % 256 for t in trajectory])  # handle -1 → 255
    fingerprint = hashlib.sha256(traj_bytes).digest()
    fingerprint_hex = fingerprint.hex()
    fingerprint_multibase = "z" + base64.b58encode(fingerprint).decode()  # base58btc

    # Construct DID
    path = ":".join(path_segments or ["agents", fingerprint_hex[:16]])
    did = f"did:wba:{domain}:{path}"

    return {
        "@context": [
            "https://www.w3.org/ns/did/v1",
            "https://w3id.org/security/suites/ed25519-2020/v1",
            "https://plurigrid.com/ns/gf3-identity/v1"  # GF(3) context extension
        ],
        "id": did,
        "verificationMethod": [{
            "id": f"{did}#gf3-key-1",
            "type": "GF3TritTrajectoryVerificationKey2020",  # new key type
            "controller": did,
            "publicKeyMultibase": fingerprint_multibase,
            "gf3_trajectory": trajectory,
            "gf3_conservation": sum(trajectory) % 3,  # must be 0
=======
    Requirement:  trajectory is GF(3)-conserved (sum = 0 mod 3)
    Requirement:  len(trajectory) >= 3
    Postcondition: valid DID document fragment with trajectory verification method
    """
    if sum(trajectory) % 3 != 0:
        raise ValueError(f"GF(3) conservation violated: sum={sum(trajectory)}")

    traj_bytes = bytes([t % 256 for t in trajectory])
    fingerprint = hashlib.sha256(traj_bytes).digest()
    fingerprint_multibase = "z" + base64.b58encode(fingerprint).decode()

    path = ":".join(path_segments or ["agents", fingerprint.hex()[:16]])
    did = f"did:wba:{domain}:{path}"

    return {
        "@context": ["https://www.w3.org/ns/did/v1"],
        "id": did,
        "verificationMethod": [{
            "id": f"{did}#gf3-key-1",
            "type": "GF3TritTrajectoryVerificationKey2020",
            "controller": did,
            "publicKeyMultibase": fingerprint_multibase,
            "gf3_trajectory": trajectory,
>>>>>>> origin/main
            "trajectory_length": len(trajectory),
        }],
        "authentication": [f"{did}#gf3-key-1"],
        "service": [{
            "id": f"{did}#qrtp-transport",
            "type": "QRTransportProtocol",
<<<<<<< HEAD
            "serviceEndpoint": "qrtp://air-gap",  # offline transport indicator
            "fountainCode": "LT",  # Luby Transform
            "errorCorrectionCapacity": 0.95,
        }]
    }


def did_to_passport_fragment(did_document: dict) -> Optional[dict]:
    """
    Reverse bridge: extract GF(3) trit trajectory from a DID document.

    Requirement:  DID document has a GF3TritTrajectoryVerificationKey2020 method
    Postcondition: returns trajectory if found, None if standard Ed25519 DID
    """
=======
            "serviceEndpoint": "qrtp://air-gap",
            "fountainCode": "LT",
        }]
    }

def did_to_passport_fragment(did_document: dict) -> dict | None:
    """Extract trit trajectory from a DID document, if present."""
>>>>>>> origin/main
    for method in did_document.get("verificationMethod", []):
        if method.get("type") == "GF3TritTrajectoryVerificationKey2020":
            trajectory = method.get("gf3_trajectory")
            if trajectory and sum(trajectory) % 3 == 0:
                return {
                    "trajectory": trajectory,
                    "fingerprint": method.get("publicKeyMultibase"),
                    "conservation_verified": True,
<<<<<<< HEAD
                    "liveness_required": True,  # must verify via homotopy continuity
                }
    return None  # Standard DID, no GF(3) fingerprint
```

---

=======
                }
    return None
```

>>>>>>> origin/main
## Verification Protocol

### Online Verification (W3C DID / ANP mode)

```python
def verify_online(did: str, challenge: bytes) -> tuple[bool, dict]:
    """
<<<<<<< HEAD
    Requirement:  DID resolver accessible (HTTPS connectivity)
    Postcondition: (True, did_document) | (False, error_dict)

    Standard W3C DID verification:
    1. Resolve DID → fetch DID document from HTTPS endpoint
    2. Extract public key from verificationMethod
    3. Verify challenge signature against public key
    """
    resolver = DIDResolver()
    doc = resolver.resolve(did)  # requires network
    key_material = doc["verificationMethod"][0]
    # Signature verification (Ed25519 or GF3TritTrajectory)
=======
    Requirement:  DID resolver accessible (HTTPS)
    Postcondition: (True, did_document) | (False, error_dict)
    """
    resolver = DIDResolver()
    doc = resolver.resolve(did)
    key_material = doc["verificationMethod"][0]
>>>>>>> origin/main
    is_valid = verify_signature(challenge, key_material)
    return (is_valid, doc)
```

### Offline Verification (passport.gay / QRTP mode)

```python
def verify_offline(qrtp_frames: list[bytes], challenge: bytes) -> tuple[bool, dict]:
    """
    Requirement:  qrtp_frames are fountain-coded QR code frames
<<<<<<< HEAD
    Requirement:  at least 5% overhead in received frames for error correction
    Postcondition: (True, passport_doc) | (False, error_dict)
    --- NO NETWORK REQUIRED ---

    Air-gapped verification:
    1. Decode QRTP frames → reconstruct identity proof
    2. Extract trit trajectory + homotopy certificate
    3. Verify GF(3) conservation (mathematical, no network)
    4. Verify homotopy continuity (liveness check, no network)
    5. Verify challenge response against GF(3) fingerprint
    """
    # Fountain decoding (LT code)
    passport_doc = decode_qrtp(qrtp_frames)

    trajectory = passport_doc["trajectory"]
    certificate = passport_doc["homotopy_certificate"]

    # Step 1: GF(3) conservation (mathematical invariant)
    if sum(trajectory) % 3 != 0:
        return (False, {"error": "GF(3) conservation violated"})

    # Step 2: Homotopy continuity (liveness)
    if not verify_homotopy_continuity(certificate):
        return (False, {"error": "Liveness check failed: deformation not continuous"})

    # Step 3: Challenge response
    fingerprint = hashlib.sha256(bytes(t % 256 for t in trajectory)).digest()
    expected_response = hashlib.sha256(fingerprint + challenge).digest()
    if passport_doc.get("challenge_response") != expected_response:
=======
    Postcondition: (True, passport_doc) | (False, error_dict)
    NO NETWORK REQUIRED.
    """
    passport_doc = decode_qrtp(qrtp_frames)
    trajectory = passport_doc["trajectory"]
    certificate = passport_doc["homotopy_certificate"]

    if sum(trajectory) % 3 != 0:
        return (False, {"error": "GF(3) conservation violated"})

    if not verify_homotopy_continuity(certificate):
        return (False, {"error": "Liveness check failed"})

    fingerprint = hashlib.sha256(bytes(t % 256 for t in trajectory)).digest()
    expected = hashlib.sha256(fingerprint + challenge).digest()
    if passport_doc.get("challenge_response") != expected:
>>>>>>> origin/main
        return (False, {"error": "Challenge response mismatch"})

    return (True, passport_doc)
```

<<<<<<< HEAD
---

## Bisimulation Proof: Online ≅ Offline

```
LTS_online  = (States_online,  Actions, →_online,  s₀_online)
LTS_offline = (States_offline, Actions, →_offline, s₀_offline)

Actions shared: {prove, verify, accept, reject}

Bisimulation R:
  (request_online, request_offline) ∈ R
  (verified_online, verified_offline) ∈ R
  (rejected_online, rejected_offline) ∈ R

Transitions:
  online:  request →_online{verify_did} → verified  | rejected
  offline: request →_offline{decode_qrtp; check_gf3; check_homotopy} → verified | rejected

Weak bisimulation (τ-transitions hidden):
  The internal steps (DID resolution vs. QRTP decoding) are τ-transitions.
  External observations: both produce (verified, identity_proof) or (rejected, reason).
  ∴ online ~_weak offline within the same GF(3) trit class.

GF(3)-colored bisimulation:
  ONLY within same trit class (both must have trit = -1, 0, or +1).
  Cross-trit: not-bisimilar by definition.
```

---

## Revocation (Closing Gap G5)

```python
# Gap G5 from zig-syrup-propagator-interleave:
# "No revocation mechanism for compromised identities"
# Candidate: anoma-intents, aptos-gf3-society

=======
## Revocation

```python
>>>>>>> origin/main
def revoke_passport_identity(
    trajectory: list[int],
    reason: str,
    revocation_registry: str = "did:wba:plurigrid.com:revocation",
) -> dict:
    """
<<<<<<< HEAD
    Requirement:  revocation_registry is an Anoma intent (or Aptos GF3 society record)
    Postcondition: trajectory fingerprint added to revocation list; propagated via QRTP

    Revocation without network (for air-gapped scenarios):
    - Post signed revocation notice to Anoma intent pool
    - QRTP broadcast of revocation QR code (fountain-coded)
    - Verifiers check revocation list during offline verification

    Revocation with network (for DID scenarios):
    - Update DID document: add "revoked" status assertion
    - Propagate via DID resolution (verifiers fetch updated doc)
    """
=======
    Closes Gap G5: "No revocation mechanism for compromised identities".
    Supports both online (Anoma intent) and offline (QRTP broadcast) revocation.
    """
    import time
>>>>>>> origin/main
    fingerprint = hashlib.sha256(bytes(t % 256 for t in trajectory)).hexdigest()
    revocation_entry = {
        "fingerprint": fingerprint,
        "reason": reason,
        "timestamp_ms": int(time.time() * 1000),
<<<<<<< HEAD
        "gf3_conservation": sum(trajectory) % 3,
    }
    # Broadcast via Anoma intent (online) + QRTP (offline)
    return {
        "anoma_intent": post_revocation_intent(revocation_entry),
        "qrtp_frames": encode_qrtp(revocation_entry),  # can be presented as QR code
        "did_update": f"{revocation_registry}#{fingerprint}",
    }
```

---

## Related Skills

- `zig-syrup-propagator-interleave` — QRTP, passport.gay, homotopy liveness
- `agent-protocol-interleave` — full agent protocol ecosystem bridge
- `bisimulation-oracle` — formal proof of online ≅ offline bisimulation
- `merkle-proof-validation` — alternative offline proof transport (Merkle vs. fountain)
- `anoma-intents` — revocation via Anoma intent pool
- `aptos-gf3-society` — revocation via Aptos GF(3) society contract
- `gf3-trit-oracle` — trit classification prerequisite for GF(3)-colored bisimulation
- `splitmix-ternary` — SplitMix64 → trit trajectory generation
- `gay-monte-carlo` — GF(3)-colored sampling for trajectory generation
=======
    }
    return {
        "anoma_intent": post_revocation_intent(revocation_entry),
        "qrtp_frames": encode_qrtp(revocation_entry),
        "did_update": f"{revocation_registry}#{fingerprint}",
    }
```
>>>>>>> origin/main
