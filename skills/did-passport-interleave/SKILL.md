---
name: did-passport-interleave
description: >
  Bridge between W3C Decentralized Identifiers (did:wba, ANP) and passport.gay
  (SplitMix64 MAC -> trit trajectory -> fingerprint -> QRTP air-gap).
  Triggers: DID resolution, offline identity verification, air-gapped identity,
  QRTP fountain-coded QR transport, passport revocation, online/offline identity bridge.
---

# W3C DID / passport.gay Interleave

## Formal Equivalence

The two identity systems are behaviorally equivalent (bisimilar) for offline scenarios:

```
W3C DID (ANP):
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

## did:wba Method (ANP)

```
did:wba:<domain>:<path>
Example: did:wba:plurigrid.com:agents:skill-graph-agent

DID Document (JSON-LD):
{
  "@context": ["https://www.w3.org/ns/did/v1"],
  "id": "did:wba:plurigrid.com:agents:skill-graph-agent",
  "verificationMethod": [{
    "id": "...#key-1",
    "type": "Ed25519VerificationKey2020",
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

## Bridge: Trit Trajectory -> DID Document Fragment

```python
import hashlib, base64

def passport_to_did_fragment(
    trajectory: list[int],
    domain: str = "plurigrid.com",
    path_segments: list[str] = None,
) -> dict:
    """
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
            "trajectory_length": len(trajectory),
        }],
        "authentication": [f"{did}#gf3-key-1"],
        "service": [{
            "id": f"{did}#qrtp-transport",
            "type": "QRTransportProtocol",
            "serviceEndpoint": "qrtp://air-gap",
            "fountainCode": "LT",
        }]
    }

def did_to_passport_fragment(did_document: dict) -> dict | None:
    """Extract trit trajectory from a DID document, if present."""
    for method in did_document.get("verificationMethod", []):
        if method.get("type") == "GF3TritTrajectoryVerificationKey2020":
            trajectory = method.get("gf3_trajectory")
            if trajectory and sum(trajectory) % 3 == 0:
                return {
                    "trajectory": trajectory,
                    "fingerprint": method.get("publicKeyMultibase"),
                    "conservation_verified": True,
                }
    return None
```

## Verification Protocol

### Online Verification (W3C DID / ANP mode)

```python
def verify_online(did: str, challenge: bytes) -> tuple[bool, dict]:
    """
    Requirement:  DID resolver accessible (HTTPS)
    Postcondition: (True, did_document) | (False, error_dict)
    """
    resolver = DIDResolver()
    doc = resolver.resolve(did)
    key_material = doc["verificationMethod"][0]
    is_valid = verify_signature(challenge, key_material)
    return (is_valid, doc)
```

### Offline Verification (passport.gay / QRTP mode)

```python
def verify_offline(qrtp_frames: list[bytes], challenge: bytes) -> tuple[bool, dict]:
    """
    Requirement:  qrtp_frames are fountain-coded QR code frames
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
        return (False, {"error": "Challenge response mismatch"})

    return (True, passport_doc)
```

## Revocation

```python
def revoke_passport_identity(
    trajectory: list[int],
    reason: str,
    revocation_registry: str = "did:wba:plurigrid.com:revocation",
) -> dict:
    """
    Closes Gap G5: "No revocation mechanism for compromised identities".
    Supports both online (Anoma intent) and offline (QRTP broadcast) revocation.
    """
    import time
    fingerprint = hashlib.sha256(bytes(t % 256 for t in trajectory)).hexdigest()
    revocation_entry = {
        "fingerprint": fingerprint,
        "reason": reason,
        "timestamp_ms": int(time.time() * 1000),
    }
    return {
        "anoma_intent": post_revocation_intent(revocation_entry),
        "qrtp_frames": encode_qrtp(revocation_entry),
        "did_update": f"{revocation_registry}#{fingerprint}",
    }
```
