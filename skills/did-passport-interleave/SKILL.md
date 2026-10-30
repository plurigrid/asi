---
name: did-passport-interleave
description: >
  Bridge DID verification and passport.gay offline QRTP transport while keeping
  behavioral equivalence, cryptographic identity, issuer claims, and delegated
  capability authority separate. Use for online/offline identity verification,
  trit trajectory binding, air-gapped presentations, and revocation design.
deployed: '2026-02-19'
role: BRIDGE
tags: '[did, w3c, anp, passport, qrtp, gf3, identity, bridge, air-gap]'
trit: '0'
version: 1.0.0
---

# W3C DID / passport.gay Interleave

## Status and boundaries

Treat this as a bridge design and verification contract. This directory contains
no DID resolver, signature verifier, QRTP codec, or revocation implementation.
Do not report Gap G-P2 (MCP-I DID extension) or Gap G5 (passport revocation) as
closed by this document. Validate concrete implementations separately.

Retain the deterministic SplitMix64 → color → trit trajectory model as public
application metadata and QRTP as transport. Neither is a cryptographic trust
anchor. A MAC-derived seed (including a device MAC address), deterministic PRNG,
GF(3) sum, trajectory hash, or continuous deformation supplies no secret signing
key and authenticates no issuer. Continuity alone is not evidence of liveness.

Keep these judgments separate in every verification result:

| Judgment | Required evidence | What it does not establish |
|----------|-------------------|----------------------------|
| Structural consistency | Canonical trits and the declared GF(3) invariant | Identity, issuer authenticity, authority, or liveness |
| Behavioral equivalence | Explicit transition systems, observations, relation, and transition obligations | Same subject, key controller, or permissions |
| Cryptographic authentication | Trusted DID/key binding and valid proof of key control for this fresh challenge and audience | Truth of issuer claims or permission to act |
| Authenticated issuer claim | Valid issuer proof, permitted assertion key, subject binding, and verifier trust policy | Truth beyond that policy or delegated capability authority |
| Delegated capability authority | Valid grant/delegation chain from an accepted authority, scope, audience, constraints, expiry, and status checks | Unrelated rights or unrestricted access |

Follow the distinction among `authentication`, `assertionMethod`,
`capabilityInvocation`, and `capabilityDelegation` in
[W3C DID Core §5.3](https://www.w3.org/TR/did-core/#verification-relationships).
Listing a key under a relationship does not itself issue a capability grant.
A valid signature attributes a statement to a key; trust policy determines
whether that issuer is accepted for the particular claim.

## Bind public trajectory metadata to cryptographic identity

1. Validate each trit as an integer in {-1, 0, +1}; reject booleans, other values,
   and trajectories shorter than three. Check sum modulo 3 if required by the
   declared trajectory profile. Do not coerce arbitrary integers modulo 256.
2. Define a versioned canonical encoding and fingerprint. Preserve trajectory
   order. A fingerprint identifies those bytes, not a person or a key controller.
3. Bind the profile, fingerprint, subject DID, issuer, intended use, and validity
   interval in an issuer-signed claim using a supported proof suite. Verify that
   the key is authorized for assertion and the issuer is accepted for this use.
4. For authentication, separately verify the subject's challenge response using
   a method authorized for `authentication`. Bind the presentation, nonce,
   audience, and protocol domain to the signed bytes to prevent substitution.
5. For an action, separately verify the applicable capability grant and chain.
   Require attenuation at each delegation and enforce resource/action constraints.

Keep the trajectory in application claim data. Do not put its digest into
`publicKeyMultibase`, invent `GF3TritTrajectoryVerificationKey2020`, or add a
trajectory to `authentication`. The former example's `base64.b58encode` is not a
Python standard-library function; changing encodings would still not make a
fingerprint a verification key. Do not derive a private key from public metadata.

A candidate URI such as `did:wba:plurigrid.com:agents:skill-graph-agent` must be
created and resolved under the selected method's actual rules. Hashing a
trajectory into a path does not register a DID or prove control of that domain.
Do not generalize did:wba HTTPS resolution assumptions to every DID method.

## Online and offline verification contract

Use the same proof and authorization policy across both transports. Return
separate structural, authentication, issuer-claim, and authorization outcomes,
with evidence provenance and status freshness. If required evidence is missing,
return unknown/reject for that decision; never promote a structural pass to an
authenticated or authorized result.

### Online

- Resolve the subject and issuer DIDs using trusted method-specific resolution.
  Check identifier/document binding, key purpose, rotation, expiry, and status.
  Do not blindly use the first `verificationMethod` in the document.
- Verify the actual signatures over canonical, domain-separated messages with
  the selected supported suite. Require a verifier-generated nonce, intended
  audience, expiry, and replay prevention. HTTPS delivery alone does not verify
  a presentation signature or authorize an action.
- Check issuer trust for each claim and capability authority for each action.
  Bind claimed trajectory metadata to the signed subject and presentation.

### Offline / QRTP

- Decode with bounded sizes and resource limits. Fountain coding/error correction
  reconstructs bytes; it does not authenticate their origin. Verify signatures
  after reconstruction and reject malformed or substituted payloads.
- Obtain trusted key/DID bindings independently: provisioned trust material or
  authenticated, versioned cached documents/status snapshots. A public key supplied
  in the same untrusted QR payload is not an independent trust anchor.
- Apply the same key-purpose, issuer, signature, subject, audience, and capability
  checks as online. Use an interactive fresh challenge where authentication needs
  proof of current key control. Static signed credentials alone are replayable.
- Maintain nonce/replay state and a trusted time or equivalent freshness policy.
  A locally computed `SHA256(public_fingerprint || challenge)` is forgeable by
  anyone who sees the fingerprint and is not a signature or proof of possession.
- Report the age/version of cached revocation and key state. An offline verifier
  cannot establish revocations newer than its last authenticated update without
  additional information. Reject/defer when the configured freshness bound is
  exceeded; do not silently claim current online-equivalent assurance.

## Behavioral equivalence: proof target, not a result

A shared `prove → verify → accept/reject` interface and matching trit classes do
not establish bisimulation. Define the states, labeled transitions, initial
relation, observable decisions, and threat/freshness assumptions first.

A possible restricted relation pairs online and offline states using the same
trusted key bindings, policy, signed claims, delegation chain, nonce state, and
status snapshot. Prove that each observable transition on either side can be
matched by the other, with related successor states. Hide transport steps only
when they do not change security-relevant observations. Include rejection,
unknown, replay, expired credentials, key rotation, and stale-status paths.

Counterexample to unconditional equivalence: revoke a key after the offline
snapshot. A current online verifier rejects while an offline verifier may accept
under a still-valid cached-status policy. A GF(3) equality does not repair this
observational difference. Trit coloring can index a relation; it cannot prove it.

## Revocation and key rotation (Gap G5 remains open)

Specify a signed, versioned status format with issuer/key binding, subject or
credential/grant identifier, sequence/epoch, issuance time, and validity limit.
Authenticate the revoker's authority and prevent rollback to an older snapshot.
A trajectory fingerprint alone is not enough to identify the affected grant.

Anoma intents, Aptos records, DID updates, and QRTP broadcasts are candidate
publication/transport mechanisms. Returning a dictionary or broadcasting a QR
code does not implement authenticated revocation. Verifiers must validate and
apply the update, persist monotonic status, and enforce a freshness policy.
Define emergency key compromise and offline recovery behavior before deployment.

## Validation targets for an implementation

| Case | Required outcome |
|------|------------------|
| Conserved trajectory with no signature | Structural pass only; no authentication or authority |
| Attacker recomputes hash response to a fresh challenge | Authentication rejected |
| Valid subject signature, untrusted issuer | Subject authentication may pass; issuer claim rejected/unknown |
| Trusted issuer claim, no capability grant | Claim may pass; requested action denied |
| Valid grant, wrong resource/audience or widened delegation | Requested action denied |
| Replay or modified trajectory/presentation | Authentication rejected |
| Valid offline proofs and fresh authenticated snapshot | Evaluate the same policy within the stated freshness bound |
| Missing/stale/revoked key or status evidence | Reject/defer the affected decision; preserve reason and provenance |

These are proof/test obligations, not claims that cryptographic integration tests
already exist. Run them against the actual resolver, proof suite, QRTP codec,
status store, and capability evaluator before claiming the bridge is implemented.

## Related Skills

- `zig-syrup-propagator-interleave` — passport and QRTP design context
- `agent-protocol-interleave` — agent protocol bridge context
- `bisimulation-oracle` — candidate behavioral proof workflow
- `merkle-proof-validation` — authenticated inclusion evidence
- `anoma-intents`, `aptos-gf3-society` — candidate status publication mechanisms
- `gf3-trit-oracle`, `splitmix-ternary` — structural trit classification/generation

Related documents may contain unresolved conflicts. They do not override this
contract's separation of consistency, identity, claims, and authority.
