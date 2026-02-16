# Network Intelligence - 2026-02-08

## Discovered Devices

### Bambu Lab 3D Printer
- **IP:** 192.168.0.85
- **MAC:** 30:ed:a0:1f:76:d4 (Espressif Inc)
- **Serial:** 01P00C543001592
- **Ports:**
  - 3000/tcp - JSON API (a5a5 binary header protocol)
  - 990/tcp - TLS/FTPS (BBL CA cert)
  - 6000/tcp - unknown (silent)
- **Protocol:** Bambu Lab proprietary, requires auth
- **Cert Chain:** CN=BBL CA, O=BBL Technologies Co., Ltd, C=CN

### Known Network
- 192.168.0.1 - Router (6c:63:f8 Netgear?)
- 192.168.0.107 - Unknown (randomized MAC 6a:e4:46)
- 192.168.0.92 - Ubiquiti
- 192.168.0.133 - Ubiquiti
- 192.168.0.165 - Apple device

### Arcade1Up Cabinet
- Status: NOT YET IDENTIFIED
- Expected: Allwinner ARM SoC, locked WiFi, no open ports
- Possible candidates: 192.168.0.107 or new device

## Next Steps
- Promiscuous capture for traffic patterns
- Look for Arcade1Up cloud traffic (leaderboards)

## Promiscuous Capture Results

### 192.168.0.107 (Heavy Talker)
- **Identity:** Likely your Mac (talking to Anthropic/Claude + Vercel)
- **Destinations:**
  - 160.79.104.10 - Anthropic, PBC (Claude API)
  - 64.239.123.1 - Vercel, Inc
  - 64.239.109.1 - Vercel, Inc
  - 172.66.150.162 - Cloudflare
  - 142.250.x.x - Google

### New Devices Discovered
- **192.168.0.29** - MAC 32:b9:aa:1e:1e:27 (randomized) - NBNS/MDNS active
- **192.168.0.194** - MAC ae:5c:2f:fc:79:a0 (randomized) - MDNS active

### Arcade1Up Still Missing
- No obvious game/leaderboard traffic seen
- Cabinet may not be on WiFi or using different SSID

### 192.168.0.29 - IDENTIFIED
- **Identity:** Apple device (AirTunes/AirPlay)
- **Port 5000:** AirTunes/890.79.5
- **Response:** HTTP 403 Forbidden (AirPlay auth required)
- **NOT Arcade1Up**

## Conclusion
Arcade1Up cabinet either:
1. Not connected to WiFi
2. On different SSID/VLAN
3. WiFi disabled in settings

Devices found on 192.168.0.x:
- .1 = Router
- .29 = Apple (AirPlay)
- .85 = Bambu Lab 3D Printer  
- .92, .133 = Ubiquiti
- .107 = Mac (this session)
- .163 = Unknown
- .165 = Apple

## Geofence Intelligence (Exa Research)

### Waymo One Autonomous Taxi
- **FCC Grantee Code:** 2AZKT
- **FCC IDs:** 2AZKT71099000WIFI, 2AZKT710-60000W, 2AZKT710-99000W  
- **OUI Prefixes:** Uses Google Inc OUIs (95+ registered prefixes)
- **WiFi:** Offers free passenger WiFi (SSID not publicly disclosed)
- **Connectivity:** 4G/5G cellular, not dependent on continuous connection
- **Vehicle:** Jaguar I-PACE based platform

### Google OUI Prefixes (sample)
```
F4:F5:D8, 00:1A:11, 00:F6:20, 08:9E:08, 08:B4:B1, 0C:C4:13
14:22:3B, 14:C1:4E, 1C:53:F9, 1C:F2:9A, 20:1F:3B, 20:DF:B9
... (95 total prefixes in geofence_proof.bb)
```

### Tesla OUI Prefixes
```
4C:FC:AA, 54:9F:13, 98:ED:5C, DC:44:27, E8:99:C4, EC:F4:51, B4:4B:D6
```

### Detection Strategy
1. Scan WiFi for "Waymo"/"waymo" SSID patterns
2. Match ARP/WiFi MACs against Google OUI list
3. Look for _googlecast._tcp mDNS services
4. Counterfactual: exit vehicle, verify network disappears

### Sources
- IEEE OUI Registry via netify.ai
- FCC filings: fcc.report/company/Waymo-L-L-C
- Reuters/CNET reporting on Waymo WiFi (2019)

## Bambu Lab Protocol Reverse Engineering

### Protocol Structure (Port 3000)
```
[2 bytes] Magic:   0xa5a5
[1 byte]  Type:    0xa1=login, 0xa2=push, 0xa3=control  
[1 byte]  Padding: 0x00
[n bytes] JSON payload
[2 bytes] Trailer: 0xa7a7 (optional)
```

### Discovered Ports
| Port | Service | Notes |
|------|---------|-------|
| 990  | FTPS | TLS cert CN=serial, Issuer=BBL CA |
| 3000 | JSON API | Binary header + JSON, requires auth |
| 6000 | Unknown | Silent |
| 8883 | MQTT-TLS | Cloud connectivity |

### Error Codes
- 83968023: "Incompleted json" - malformed request

### Tools Created
- `scripts/recon/main.go` - Network scanner (blackhat-go Ch.2,27,33)
- `scripts/recon/bambu_proto.go` - Protocol dissector
- `scripts/geofence_proof.bb` - Location proofs
- `scripts/network_counterfactual.bb` - Device identification
