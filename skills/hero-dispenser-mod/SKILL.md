---
name: hero-dispenser-mod
description: Hero Health smart pill dispenser after-market firmware mod with scrambled medication indexing, Aptos Hamming swarm contract integration, and nurse approval email automation. Use when working on medication dispensing, Hero device hacking, supply chain tracking, or pill dispenser reverse engineering.
version: 0.1.0
trit: -1
color: "#E59798"
tags: [hero, dispenser, medication, reverse-engineering, aptos, hamming, iot]
---

# Hero Dispenser After-Market Firmware Mod

## Hardware Profile (Model 100, v3.0 Dec 2024)

Hero is a WiFi-connected smart pill dispenser:
- **Connectivity**: 2.4GHz WiFi (802.11 b/g/n), cloud-dependent
- **Actuators**: X/Z steppers, turntable stepper, vacuum pump with rubber tip
- **Sensors**: Door sensor, carriage position
- **Display**: LCD with directional arrows
- **Capacity**: 10 medication cups, up to 90-day supply per cup
- **Regulatory**: FDA Class I, HIPAA-compliant cloud

## Reverse Engineering Entry Points

**FCC ID: 2AN4DM115** — Internal photos, RF test reports available.
- [Internal Photos PDF](https://fccid.io/2AN4DM115/Internal-Photos/Internal-Photos-3838798.pdf) — PCB layout, antenna, test points visible
- [RF Test Report](https://fcc.report/FCC-ID/2an4dm115/3838802.pdf) — 2402-2480 MHz confirmed
- MCU/WiFi module chip markings NOT annotated — need manual high-res inspection
- No public firmware dumps, debug pinouts, or teardowns exist
- Device firmware update path exists (OTA via Settings menu)

**Community efforts** (Arduino Forum Dec 2024, Home Assistant Feb 2024):
- Device is **cloud-locked** to Hero subscription ($44.99/mo or $449.90/yr)
- ESP8266 NodeMCU stepper control confirmed working (4-wire, D1-D4)
- Full board redesign stalled due to complexity
- No WiFi sniffing results published

**Attack surface (3 tiers)**:
1. **Software**: mitmproxy on app↔cloud API, decompile Hero iOS app (id1352848484), build custom scheduling layer on top
2. **Hardware**: Inspect FCC internal photos for chip IDs, locate UART/SWD test points, attempt serial console
3. **Replacement**: ESP32 board replacement with direct stepper + vacuum control, custom web UI

**Hero Public API**: https://developer.herohealth.net/apis/public-api/openapi (REST, x-api-key auth, webhooks)
**FDA MAUDE report**: https://www.accessdata.fda.gov/scripts/cdrh/cfdocs/cfmaude/detail.cfm?mdrfoi__id=16276816

## Scramble Index Architecture

Full derangement mapping (no medication uses its own initial letter):

| Slot | Medication | Natural | GF(3) | Schedule |
|------|-----------|---------|-------|----------|
| q | Vyvanse | v | -1 | morning |
| x | Magnesium | m | 0 | evening |
| y | Zinc | z | +1 | morning |
| k | Ginkgo | g | -1 | morning |
| u | Caffeine | c | 0 | morning |

**Conservation**: Q(-1) + X(0) + Y(+1) + K(-1) + U(0) = **-1** = H world trit

## Categorical Scales

The dispenser operates as a dynamical system across 6 scales:

1. **Arena (Play/Coplay)**: Positions = slots, Directions = {dispense, refill, adjust, alert}
2. **Open Game**: Forward = predict supply depletion, Backward = nurse approval utility
3. **Polynomial Functor**: State-dependent interface (controlled slots restricted until approved)
4. **GF(3) Conservation**: Trit sum must equal world H trit (-1)
5. **Hamming(7,4)**: Chain 1 (Witness-Bridge: h,w,b), voice: Junior
6. **Concrete**: Slot configs, email automation, Aptos contract

## Email Architecture

- **Hero registration**: `mantissa+hero-h@plurigrid.com`
- **Nurse approval TO**: `mantissa@gmail.com` (primary), `ies@plurigrid.com` (backup)
- **Automation FROM**: `mantissa@plurigrid.com` (Gmail MCP)
- **Monitoring**: Gmail MCP search queries for `to:mantissa+hero-h@plurigrid.com`

## Key Files

All in `/Users/alice/worlds/h/`:
- `hero_dispenser.json` - Config with scramble index
- `hero_scramble.py` - CLI: `table | lookup <letter> | set <letter> <mg> | add <name>`
- `hero_arena.py` - Categorical diagnostic across all 6 scales
- `hero_dispenser_service.py` - Flox service daemon
- `hero_email_monitor.py` - Gmail MCP integration
- `nurse_approval.py` - Nurse approval workflow
- `nurse_config.json` - Email routing config
- `nurse_requests.json` - Pending approval queue

## CLI Commands

```bash
# Show scramble table
python3 hero_scramble.py table

# Set dosage for a slot
python3 hero_scramble.py set x 400

# Add new medication (auto-picks deranged letter)
python3 hero_scramble.py add "Melatonin"

# Full categorical diagnostic
python3 hero_arena.py

# Check email integration status
python3 hero_email_monitor.py status

# Process nurse approvals
python3 nurse_approval.py pending
python3 nurse_approval.py approve 0
```

## Aptos Integration

- Contract module: `hamming_swarm::hero_dispenser`
- Network: testnet
- On-chain: scramble hash, dispense events, encrypted supply levels, nurse approvals

## Adding New Medications

When adding a medication, the system:
1. Picks a letter maximally distant from both H and the med's natural initial
2. Ensures full derangement (no med maps to own letter)
3. Recomputes GF(3) conservation
4. If controlled substance: queues nurse approval email automatically
