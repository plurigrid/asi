---
name: rf-signal-analysis
description: Analyze wireless and radio frequency security in applications, protocols, and hardware. Covers WiFi, Bluetooth/BLE, RFID/NFC, Zigbee, LoRa, cellular, and SDR-based analysis. Use when auditing IoT devices, wireless protocols, access control systems, or any RF-enabled infrastructure.
---

## When to Use

- IoT devices with wireless connectivity (WiFi, BLE, Zigbee, LoRa, cellular)
- Wireless protocol implementations and custom RF protocols
- Physical access control systems (RFID badges, NFC readers, garage doors)
- Bluetooth peripherals (keyboards, locks, medical devices, fitness trackers)
- WiFi infrastructure (access points, captive portals, enterprise WPA)
- Cellular and baseband components (modems, SIM provisioning, SMS gateways)
- Any RF-emitting device or system (sub-GHz remotes, key fobs, TPMS sensors)
- Embedded firmware that handles wireless communication stacks

## Protocol Attack Surface

### WiFi (802.11)
| Vector | Description |
|--------|-------------|
| WPA2 PSK | PMKID capture, 4-way handshake capture, offline dictionary attack |
| WPA3/SAE | Dragonblood side-channel and downgrade attacks |
| WPA2-Enterprise | EAP identity theft, evil twin with RADIUS impersonation |
| Captive Portals | MAC spoofing, DNS tunneling, portal bypass |
| Deauthentication | Client disconnection, DoS, forced reconnection to rogue AP |
| Evil Twin | Rogue AP with matching SSID, credential harvesting |
| KRACK | Key reinstallation attacks on 4-way handshake nonce reuse |
| PMKID | Clientless attack against AP, hashcat-crackable |

### Bluetooth / BLE
| Vector | Description |
|--------|-------------|
| Pairing Vulnerabilities | Just Works passkey bypass, MITM during pairing |
| GATT Enumeration | Service/characteristic discovery, read/write unprotected attrs |
| Relay/Replay Attacks | Proximity relay (e.g., car unlock), captured GATT writes |
| KNOB Attack | Key negotiation entropy reduction to 1 byte |
| BIAS Attack | Impersonation via role switching during secure connection |
| BLE Sniffing | Advertisement channel capture, connection following |
| MAC Randomization Bypass | Tracking via advertising data fingerprinting |

### RFID / NFC
| Vector | Description |
|--------|-------------|
| Badge Cloning | EM4100/HID 125kHz long-range read and duplicate |
| Mifare Classic | Nested attack, hardnested, darkside key recovery |
| HID iClass | Standard key looper, elite key diversification attacks |
| DESFire | Side-channel key recovery on older implementations |
| Replay Attacks | Captured credential replay on access controllers |
| NFC MITM | Relay between card and reader (NFCGate) |
| Skimming | Long-range unauthorized credential reads |

### Zigbee / Z-Wave
| Vector | Description |
|--------|-------------|
| Default Trust Center Key | Well-known ZigBee HA key (5A 69 67...) |
| Touchlink Commissioning | Factory reset and re-pair to attacker network |
| Key Sniffing | OTA key transport capture during join |
| Z-Wave S0 Downgrade | Force insecure inclusion, capture network key |
| Z-Wave S2 | DSK interception during inclusion ceremony |

### LoRa / LoRaWAN
| Vector | Description |
|--------|-------------|
| ABP vs OTAA | ABP uses static session keys, vulnerable to key reuse |
| Frame Counter Reset | Device reset replays previously seen frames |
| Session Key Reuse | ABP keys persist across sessions, enable decryption |
| Join-Accept Replay | Replay captured OTAA join responses |
| Bit-Flipping | Unencrypted FPort/FOpts manipulation |

### Cellular
| Vector | Description |
|--------|-------------|
| IMSI Catching | Fake base station, device identity capture (Stingray) |
| SS7 Exploitation | Location tracking, SMS interception, call redirect |
| SIM Swap | Social engineering carrier to transfer number |
| Baseband Attacks | RCE via malformed RRC/NAS messages |
| 2G Downgrade | Force device to GSM, no mutual authentication |
| VoLTE | SIP/RTP interception on LTE voice channels |

### Sub-GHz (ISM Band)
| Vector | Description |
|--------|-------------|
| Garage Doors | Fixed code capture and replay (300-433 MHz) |
| Car Key Fobs | RollJam (jam + capture rolling code), relay attack |
| TPMS Sensors | Spoofed tire pressure to trigger warnings (315/433 MHz) |
| ISM Band Jamming | Broadband noise on 315/433/868/915 MHz |
| ASK/OOK Replay | Simple modulation schemes trivially replayed |

## Tool Reference

### SDR Hardware & Software
| Tool | Purpose |
|------|---------|
| HackRF One | TX/RX 1 MHz–6 GHz, 20 MHz bandwidth |
| RTL-SDR | RX-only dongle, 24–1766 MHz, low cost recon |
| YARD Stick One | Sub-GHz TX/RX (< 1 GHz), ISM band attacks |
| GNU Radio | Signal processing flowgraph framework |
| Universal Radio Hacker | Protocol analysis, demod, decoding, fuzzing |
| SDR++ / GQRX | Real-time spectrum visualization |

### WiFi Tools
| Tool | Purpose |
|------|---------|
| aircrack-ng suite | Monitor mode, capture, deauth, crack WPA |
| bettercap | MITM framework, WiFi deauth, evil twin |
| hostapd-mana | Rogue AP with EAP credential capture |
| hcxdumptool | PMKID and handshake capture (clientless) |
| hcxtools | Convert captures to hashcat/JTR format |
| wifite2 | Automated WiFi audit wrapper |

### Bluetooth Tools
| Tool | Purpose |
|------|---------|
| Ubertooth One | BLE and classic BT sniffing (2.4 GHz) |
| btlejack | BLE connection hijacking and sniffing |
| gatttool / bluetoothctl | GATT service enumeration and interaction |
| nRF Connect (app/desktop) | BLE scanning, GATT browser, DFU testing |
| Bettercap BLE module | BLE enumeration and write injection |
| CrackLE | Crack BLE Legacy Pairing (Just Works/passkey) |

### RFID Tools
| Tool | Purpose |
|------|---------|
| Proxmark3 (RDV4) | Multi-frequency RFID read/write/emulate/sniff |
| Flipper Zero | Sub-GHz, RFID, NFC, IR, iButton swiss army knife |
| libnfc | Open-source NFC library and utilities |
| mfoc / mfcuk | Mifare Classic offline/unknown key cracking |
| ACR122U | USB NFC reader for desktop analysis |

### Signal Analysis
| Tool | Purpose |
|------|---------|
| Wireshark | 802.11, BLE, Zigbee protocol decode |
| inspectrum | Spectrogram analysis and signal measurement |
| baudline | Real-time FFT signal analysis |
| SigDigger | Qt-based signal analyzer with inspectrum-like features |
| rtl_433 | Decode OOK/FSK protocols from ISM band devices |

## Audit Methodology

### Phase 1: RF Reconnaissance
- Perform broadband spectrum sweep (SDR + GQRX/SDR++)
- Identify active frequencies, modulations, duty cycles
- Catalog all wireless interfaces on target devices
- Map wireless network topology and access points
- Document regulatory bands in use and transmission power

### Phase 2: Protocol Enumeration
- Identify protocols on discovered frequencies (WiFi, BLE, Zigbee, proprietary)
- Enumerate advertised services (GATT, SSIDs, PAN IDs, device names)
- Fingerprint firmware versions and chipset identifiers
- Map protocol state machines and message sequences
- Identify supported security modes and negotiation behavior

### Phase 3: Authentication Analysis
- Test pairing and association mechanisms for weaknesses
- Attempt default/well-known key access (Zigbee HA key, HID iClass standard)
- Evaluate key derivation and entropy (PRNG seeding, key length negotiation)
- Test credential storage on device (flash dump, JTAG/SWD extraction)
- Assess mutual authentication requirements (or lack thereof)

### Phase 4: Traffic Analysis
- Capture and decode protocol traffic (Wireshark, URH, rtl_433)
- Identify cleartext or weakly encrypted data transmissions
- Analyze session management (frame counters, sequence numbers, nonces)
- Look for information leakage in metadata, headers, or advertisements
- Correlate traffic patterns with device behavior

### Phase 5: Injection & Manipulation
- Replay captured frames and assess acceptance (replay protection)
- Inject crafted packets to test input validation
- Attempt protocol downgrade attacks (WPA3→WPA2, S2→S0, BLE SC→Legacy)
- Fuzz protocol parsers with malformed frames
- Test jamming resilience and failover behavior

### Phase 6: Persistence & Lateral Movement
- Assess post-compromise persistence on wireless devices (firmware implants)
- Test pivot from wireless to wired network segments
- Evaluate OTA update mechanisms for hijacking potential
- Check for mesh network propagation of compromised keys
- Document trust relationships between wireless components

## Code Review Patterns

When reviewing source code for RF/wireless implementations, flag:

- **Hardcoded Keys**: Encryption keys, PINs, or network credentials in source/firmware
- **Weak Randomness**: Use of `rand()`, `millis()`, or predictable seeds for nonces/keys
- **Missing Replay Protection**: No frame counter, sequence number, or timestamp validation
- **Cleartext Transmission**: Sensitive data sent without encryption over RF
- **Weak Key Derivation**: Short keys, no KDF, or insufficient PBKDF2/scrypt rounds
- **Missing Mutual Authentication**: Device trusts any peer without verifying identity
- **No Firmware Signature Verification**: OTA updates accepted without code signing
- **Static Session Keys**: ABP-style fixed keys that survive device reboot
- **Insufficient Key Rotation**: Long-lived symmetric keys without renegotiation
- **Debug Interfaces Left Open**: JTAG/SWD/UART enabled in production firmware

## Related Skills

- `reverse-engineering` — Firmware extraction, binary analysis, protocol RE
- `entry-point-analyzer` — Identify attack entry points across system boundaries
- `iot-device-provisioning` — Secure device onboarding and credential management
