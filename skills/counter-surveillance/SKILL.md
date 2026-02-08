---
name: counter-surveillance
description: Assess and harden operational security (OPSEC) posture for applications, communications, and infrastructure. Identifies surveillance exposure, metadata leakage, and tracking vectors. Use when auditing privacy-sensitive applications, reviewing OPSEC for threat models involving state-level adversaries, or hardening communications infrastructure.
---

# Counter-Surveillance Security Skill

Trail of Bits-style defensive security assessment focused on surveillance resistance,
metadata minimization, and operational security hardening.

## When to Use

- Auditing privacy-sensitive applications
- Reviewing journalist/activist threat models
- Hardening communications platforms
- Assessing metadata leakage in protocols and applications
- Evaluating anonymous communication systems
- Reviewing data retention and logging policies
- Assessing exposure to lawful intercept and legal compulsion

## Threat Model Tiers

Structure analysis by adversary capability. Each tier subsumes the capabilities of all lower tiers.

| Tier | Adversary | Capabilities |
|------|-----------|-------------|
| **1** | Passive network observer | ISP, coffee shop WiFi, upstream AS. Sees DNS, IP flows, unencrypted traffic. |
| **2** | Active network attacker | MITM, DNS manipulation, BGP hijack, certificate compromise via rogue CA. |
| **3** | Platform-level adversary | Cloud provider, app store, OS vendor. Access to plaintext data at rest, push notification content, software update channel. |
| **4** | State-level | Lawful intercept (CALEA), FISA orders, national security letters with gag orders, IMSI catchers (Stingray), device exploit vendors (NSO Group). |
| **5** | Global passive adversary | Traffic analysis across jurisdictions, correlation attacks on anonymity networks, upstream cable taps (UPSTREAM/PRISM-class). |

Always define the threat tier before beginning an audit. Controls adequate for Tier 1 are meaningless against Tier 4.

## Surveillance Surface Taxonomy

### Network Metadata
- DNS queries (reveal browsing intent even with HTTPS)
- TLS SNI field (reveals destination hostname in plaintext pre-ECH)
- Connection timing and duration patterns
- Packet sizes and inter-arrival times (traffic fingerprinting)
- IP address correlation across sessions

### Application Metadata
- Push notification payloads (visible to Apple/Google)
- App store analytics and telemetry
- Crash reports containing device state
- Update check frequency and timing
- OAuth token exchanges revealing service usage

### Device Fingerprinting
- Browser fingerprint (canvas, WebGL, fonts, screen resolution)
- Hardware identifiers (IMEI, MAC address, serial numbers)
- Sensor data (accelerometer, gyroscope uniqueness)
- Installed font and plugin enumeration
- TLS client fingerprint (JA3/JA4)

### Location Tracking
- GPS and GNSS precise positioning
- Cell tower triangulation (passive, no user consent needed)
- WiFi positioning (BSSID databases)
- Bluetooth beacons and BLE scanning
- IP geolocation databases

### Communications Metadata
- Who-talks-to-whom social graph (contact chaining)
- Timing and frequency of communication
- Message size and duration patterns
- Group membership inference
- Presence and online status indicators

### Financial Tracking
- Payment processor transaction logs
- Blockchain analysis and address clustering
- Loyalty program purchase correlation
- ATM and POS location tracking
- Subscription service usage patterns

## Audit Methodology

1. **Map data flows** — Diagram all metadata emission points from client to server to third party. Include DNS resolvers, CDNs, analytics, crash reporting, and push notification services.

2. **Assess encryption coverage** — Evaluate protection for data in transit (TLS 1.3, certificate pinning), at rest (full-disk encryption, per-record encryption), and in use (enclaves, MPC, FHE where applicable).

3. **Evaluate authentication without identification** — Can users authenticate to the service without revealing real-world identity? Review account creation flow, recovery mechanisms, and payment requirements.

4. **Review logging and data retention** — What identifiers are logged server-side? For how long? Under what legal jurisdiction? Can logs be compelled via subpoena, NSL, or FISA order?

5. **Test traffic analysis resistance** — Are encrypted messages padded to uniform size? Is timing randomized? Is cover traffic generated? Can an observer distinguish message types by size or pattern?

6. **Assess supply chain integrity** — Are builds reproducible? Are dependencies pinned and audited? Is the signing key air-gapped? Can users verify binary-to-source correspondence?

7. **Review jurisdiction and legal compulsion exposure** — Map server locations, corporate domicile, and applicable legal frameworks. Identify single points of legal compulsion (one subpoena reveals all user data).

## Code Review Patterns

Look for these anti-patterns in privacy-sensitive codebases:

```
# FINDING: Unnecessary logging of user identifiers
logger.info(f"Request from user {user_id} at {ip_address}")
# FIX: Log only what is operationally necessary; use rotating pseudonyms

# FINDING: Unpadded encrypted messages reveal content type
encrypted = encrypt(message)
# FIX: Pad all messages to fixed size buckets before encryption
encrypted = encrypt(pad_to_bucket(message))

# FINDING: Timestamps with unnecessary precision
created_at = datetime.utcnow()  # microsecond precision
# FIX: Round to reduce temporal fingerprinting
created_at = datetime.utcnow().replace(minute=0, second=0, microsecond=0)

# FINDING: Device identifiers transmitted to server
analytics.send(device_id=get_hardware_id())
# FIX: Use unlinkable session tokens; never transmit hardware IDs

# FINDING: DNS queries leaking browsing intent
requests.get("https://sensitive-site.org/resource")
# FIX: Enforce DNS-over-HTTPS/TLS; consider Tor for DNS resolution

# FINDING: Push notification content visible to platform provider
send_push(user, title="New message from Alice")
# FIX: Send empty/tombstone push; fetch content via E2E encrypted channel

# FINDING: Certificate pinning absent or bypassable
session = requests.Session()  # no pin validation
# FIX: Pin leaf or intermediate cert; detect and alert on pin failure
```

## Hardening Checklist

- [ ] **Network anonymity** — Tor/onion routing for metadata-resistant connectivity
- [ ] **E2E encrypted messaging** — Signal protocol or equivalent with forward secrecy
- [ ] **Metadata-resistant protocols** — Sealed Sender, Private Information Retrieval, oblivious HTTP
- [ ] **Encrypted DNS** — DNS-over-HTTPS or DNS-over-TLS with trusted resolver; ECH for SNI
- [ ] **Reproducible builds** — Deterministic compilation; users can verify binary matches source
- [ ] **Air-gapped signing** — Software release signing keys on offline hardware
- [ ] **Memory-safe crypto** — Rust, Go, or formally verified C for cryptographic implementations
- [ ] **Minimal logging** — Log only what is operationally essential; auto-expire within days
- [ ] **Jurisdiction diversity** — Distribute infrastructure across non-cooperating legal jurisdictions
- [ ] **Warrant canary** — Publish regular signed statements of non-compromise; absence signals compulsion
- [ ] **Anonymous account creation** — No phone number, no email, no payment required
- [ ] **Forward secrecy** — Compromise of long-term keys does not reveal past communications

## Related Skills

- `static-security-analyzer` — Automated code scanning for security vulnerabilities
- `webapp-testing` — Web application penetration testing methodology
- `secure-workflow-guide` — Secure development lifecycle and CI/CD hardening
