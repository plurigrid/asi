---
name: ikea-varmblixt-smart-lamp
description: |
  IKEA VARMBLIXT smart donut lamp (Matter over Thread). Use when pairing,
  factory resetting, troubleshooting, configuring, or integrating the VARMBLIXT
  with Apple Home, Google Home, Amazon Alexa, SmartThings, Home Assistant, or
  other Matter ecosystems. Covers BILRESA remote, wall mounting, color quirks.
---

# IKEA VARMBLIXT Smart Lamp

Sabine Marcelis design. Donut-shaped LED table/wall lamp with Matter over Thread.
Article numbers: 80613524 (US), 90623160 (UK/EU). Price: $99.99.

## Specs

| Spec | Value |
|------|-------|
| Power | 3.4W |
| Lumens | ~120-180 lm (accent only) |
| CRI | 90 |
| Lifespan | ~25,000 hours |
| Diameter | 12" / 30 cm |
| Height | 5" |
| Cord | 6'3" |
| Weight | ~5 lbs |
| Protocol | Matter over Thread |
| Shell | Matte frosted glass |
| Body | ABS plastic, steel mounting plate |

## In the Box

- VARMBLIXT lamp
- BILRESA 2-button remote (pre-paired, needs 2x AAA)
- Wall mounting plate + hardware
- Matter QR code (on lamp underside AND box)

## Physical Controls

**Power button**: next to the power cable on the base. Hard on/off toggle.

**Glass shell release**: push-button clip on base pops off top glass for wall mounting.

## BILRESA Remote (included, pre-paired)

Two buttons, no labels. Larger divot = up/brighter.

- **Tap**: toggle on/off
- **Hold**: brighten / dim
- **Double-tap**: cycle preset colors (smooth blending)

## Pairing

### First power-on (automatic)

1. Plug in, turn on. Lamp enters **15-minute pairing window** automatically.
2. Scan **Matter QR code** (lamp underside or box) with your ecosystem app.
3. Done in under 1 minute typically.

**The lamp must be ON and powered when you scan.** Do not turn it off to scan.

### Pairing window expired

Turn lamp off then on again. New 15-minute window opens.

### Factory reset

Turn the lamp **off and on 6 times** at a steady rhythm:

- ~1 second on, ~1 second off
- Leave ON after the 6th cycle
- Lamp **flashes/pulses** to confirm
- All previous Matter bindings cleared
- New 15-minute pairing window opens

If 6 cycles doesn't trigger: try slower (~2s each). Must be real power cuts, not a smart switch.

### Re-pair BILRESA remote (hubless)

Press BILRESA system button **4 times** within 5-30 cm of lamp. Lamp pulses then blinks twice = paired.

## Compatible Ecosystems

No DIRIGERA hub required. All need a **Thread Border Router**:

| Ecosystem | Border Router examples |
|-----------|----------------------|
| Apple Home | HomePod mini, Apple TV 4K 2nd gen+ |
| Google Home | Nest Hub 2nd gen, Nest WiFi Pro |
| Amazon Alexa | Echo 4th gen+ |
| SmartThings | Thread-capable hub |
| Home Assistant | SkyConnect, ZBT-1/2, any OTBR |
| Homey | With Matter support |
| IKEA DIRIGERA | Works but not required |

### Apple Home specific

1. Factory reset lamp if previously attempted pairing
2. Lamp ON and in pairing window
3. Apple Home app > **+** > **Add Accessory**
4. Scan QR code on **lamp underside** (box print quality often bad)
5. Keep phone **near HomePod** during pairing (BLE handshake)
6. HomePod must be on latest software
7. Phone must be on same WiFi as HomePod

### Home Assistant specific

- Enable IPv6: Settings > System > Network > IPv6 > Automatic
- HA and border router on same network
- Pair directly to HA, not through Apple Home first
- ZBT-1 more reliable than other OTBR options

## Critical Quirk: Remote vs Matter

**Pairing to Matter unpairs the BILRESA remote.** You cannot use both.

- Remote back: factory reset lamp, re-pair remote
- Remote WITH smart home: pair remote separately to Matter hub, associate via hub app
- This is by design

## Color Behavior

**Remote only**: double-tap cycles colors with smooth blending. Pleasant.

**Matter/app**: color changes are **abrupt**, no transitions. Known limitation.

**Adaptive Lighting** (Matter): auto-shifts white temp through the day.

**Min brightness**: color still faintly visible — glass looks tinted.

## Wall Mounting

1. Push glass release, remove shell
2. Mount base plate to wall with screws
3. Reattach glass shell
4. Route cable (6'3")

## Troubleshooting

### Won't pair

1. Physical power button must be ON
2. Factory reset: 6x power cycles, leave on, wait for flash
3. Move within **50 cm** of border router
4. Enable **IPv6** on router
5. Unplug **all other Thread border routers** temporarily
6. Use QR on lamp, not box

### Offline in app

- Check physical power
- Restart border router
- Restart hub

### Mottled light

Normal with other light sources present. Most uniform in dark room at full brightness.

## What Not To Do

- Don't expect room lighting — this is 120 lm accent light
- Don't use a smart switch for factory reset — must be real power cuts
- Don't try BILRESA remote + Matter simultaneously
- Don't drop it — the glass breaks

## Smart vs Original VARMBLIXT

| | Smart | Original |
|--|-------|----------|
| Glass | Matte frosted | Glossy caramel |
| Light | Color spectrum | Warm only |
| Smart | Matter/Thread | None |
| Remote | BILRESA included | None |
| Price | $99.99 | $99.99 |

Original's caramel warmth cannot be replicated by the smart version.

## Sources

- [IKEA US product page](https://www.ikea.com/us/en/p/80613524/)
- [IKEA Smart Lighting Support](https://www.ikea.com/nl/en/customer-service/product-support/smart-lighting/smart-lighting-support-pubd8491250/)
- [Gizmodo review Mar 2026](https://gizmodo.com/ikea-varmblixt-smart-lamp-fills-a-donut-hole-in-my-life-2000735546)
- [AppleHome Authority review Mar 2026](https://www.applehomeauthority.com/ikea-smart-varmblixt-review/)
- [HA Community thread](https://community.home-assistant.io/t/unable-to-pair-ikea-matter-devices-to-ha/976399)
