---
name: puffco-proxy
description: "Puffco Proxy modular concentrate vaporizer: state machine session management, heat profiles, LED indicators, maintenance. Includes Babashka CLI and Graphviz DOT output."
trit: 0
---

# Puffco Proxy

Modular concentrate vaporizer. State machine for session management.

## Hardware

- **Device**: Puffco Proxy (modular pipe + removable 3D chamber)
- **Chamber**: 3D ceramic, 3-prong alignment to base
- **Glass**: Modular borosilicate pipe attachment
- **Charging**: USB-C, ~90 min full charge, ~15 sessions/charge
- **App**: Puffco Connect (Bluetooth, custom boost profiles)

## Heat Settings

| Color | Temp °F | Label | Character |
|-------|---------|-------|-----------|
| 🔵 Blue | ~490 | LOW | High flavor, low vapor |
| 🟢 Green | ~510 | MED | Balanced (daily driver) |
| 🔴 Red | ~530 | HIGH | Strong vapor, good flavor |
| ⚪ White | ~565 | PEAK | Maximum extraction |

## Button Language

| Action | Effect |
|--------|--------|
| Hold 3s | Power on / off |
| 1x click | Cycle heat setting (blue→green→red→white→blue) |
| 2x click | Initiate heat cycle / Boost mode (during session) |
| 3x click | Battery check (green 60-100%, yellow 30-59%, red 0-29%) |

## LED Indicators

| Pattern | Meaning |
|---------|---------|
| Pulsing color | Heating in progress |
| Solid color + vibrate 3x | Ready to draw |
| 3 white flashes | Chamber misaligned — reseat |
| Solid red 5s | Overheating — cool down |
| Pulsing green (charging) | Charge in progress |
| Light off (charging) | Fully charged |

## State Machine

12 states, defined in `worlds/g/puffco_proxy_state_machine.py`:

```
OFF → IDLE → HEATING → READY → SESSION → COOLING → IDLE
                                  ↓
                                BOOST → COOLING
```

Setup path: `IDLE → BATTERY_CHECK`, `IDLE → HEAT_SELECT`, `IDLE ↔ CHAMBER_ERROR`

## CLI

```bash
# Full session walkthrough
bb worlds/g/puffco_proxy.bb session

# Session with boost
bb worlds/g/puffco_proxy.bb boost

# Best practices
bb worlds/g/puffco_proxy.bb tips

# Heat settings
bb worlds/g/puffco_proxy.bb heat

# Graphviz DOT output
bb worlds/g/puffco_proxy.bb dot

# Interactive REPL
bb worlds/g/puffco_proxy.bb
```

## Best Practices

### Loading
- Cold load only — never load while chamber is hot
- Place concentrate along chamber WALLS, not bottom center
- Rice-grain sized amount — overpacking causes leakage into base
- Seat carb cap snug before heating

### Drawing
- Hold device UPRIGHT / VERTICAL
- Inhale gently — slow steady draw maximizes vapor
- Start at Green, adjust from there

### Cleaning (critical for longevity)
- **Every session**: swab chamber with dry cotton while warm
- **Weekly**: soak chamber + glass in 90%+ isopropyl 20-30 min
- **Base**: swab contact points only, never flood with liquid
- Air dry all components completely before reassembly

### Safety
- Max 4 consecutive heat cycles before mandatory cooldown
- Solid red 5s = overheating protection engaged
- 3 white flashes = reseat chamber (3-prong alignment)

## World
- Letter: G
- Location: `worlds/g/puffco_proxy.bb`
