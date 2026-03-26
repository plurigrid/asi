---
name: "Kinesis Advantage360 Pro (KB360 Pro)"
description: "Official Kinesis Advantage360 Professional (ZMK / Clique) keyboard usage: layers, Bluetooth profiles, Mod shortcuts, Clique programming, ergonomics, troubleshooting, and document URLs from kinesis-ergo.com/support/kb360pro. Use when configuring, pairing, resetting firmware, or answering questions about this split ergonomic keyboard."
---

# Kinesis Advantage360 Pro (KB360 Pro)

Primary hub (manuals, FAQs, tickets): https://kinesis-ergo.com/support/kb360pro/

Models: **KB360-PRO-*** and **KB365-PRO-*** (Professional series). Firmware: **ZMK** (Apache 2.0). Programming: **Kinesis Clique** (browser) or GitHub/ZMK for advanced users.

## Official documents (direct PDFs)

| Document | URL |
|----------|-----|
| Quick Start Guide (v1.30.25, Clique) | https://kinesis-ergo.com/wp-content/uploads/Advantage-360-Professional-QSG-v1-30-25-CLIQUE-digitalt.pdf |
| User’s Manual (ZMK, v2.5.25, Clique) | https://kinesis-ergo.com/wp-content/uploads/Advantage360-ZMK-KB360-PRO-Users-Manual-v2-5-25-Clique.pdf |
| Firmware update instructions | https://kinesis-ergo.com/wp-content/uploads/Advantage360-Professional-Firmware-Update-Instructions-9.5.24-KB360-PRO.pdf |
| Settings reset instructions | https://kinesis-ergo.com/wp-content/uploads/Advantage360-Professional-Settings-Reset-Instructions-11.22.23-KB360-PRO-GBR.pdf |

Downloads (factory defaults / reset files): https://kinesis-ergo.com/download/adv360-pro-factory-default-v2-9-25/ and https://kinesis-ergo.com/download/adv360-settings-reset-files-clique/

Clique UI: https://clique.kinesis-ergo.com — Help: https://kinesis-ergo.com/clique-help — YouTube: Kinesis official channel (tutorials).

## Hardware facts

- **Left module = primary** (talks to PC). **Right module only links to the left**; it cannot be the sole USB data path to the computer.
- **Power switches** (each module): ON = slide **away** from the adjacent charging port; OFF = toward the port.
- **Bridge connector**: optional; **not** for supporting the keyboard’s weight.
- **Tenting**: three heights; start low and adjust. **Separation/rotation**: shoulder-width and outward rotation for neutral wrists.
- **30-second sleep** per module after inactivity; next keypress wakes. Active **Profile** is whatever was active at last sleep.
- **Included**: keyboard, 2× USB-C→A cables + adapters, bridge connector, extra keycaps, keycap puller.

## Layers (default)

| Layer | Layer LED | How to access |
|-------|-----------|----------------|
| Base 0 | Off | Default typing; legends on top of keycap |
| kp 1 | White | **Tap** `kp` (left) to **toggle**; keypad legends lower-right on keycap |
| fn 2 | Blue | **Hold** either `fn` (pinky) — momentary; F1–F12; legends lower-left |
| Mod 3 | Green | **Hold** `Mod` — battery, profiles, backlight, Clique unlock, etc. |

## Mod-layer shortcuts (from Quick Start)

- **Bluetooth profiles 1–5**: `Mod` + `1` … `Mod` + `5`
- **Battery status**: `Mod` + `O` (hold for status via indicator LEDs)
- **Backlight up/down**: `Mod` + `Up` / `Mod` + `Down`
- **Backlight on/off**: `Mod` + `Enter`
- **RGB / indicator LEDs on/off**: `Mod` + `Space`
- **Bluetooth clear (active profile)**: `Mod` + **Windows key** (per QSG; label may show as Windows)
- **Wired use**: with left module USB-connected, keystrokes go to that machine via USB regardless of Profile; Kinesis recommends **Profile 5** (`Mod` + `5`) for wired mode to stop the Profile LED flashing.
- **Single USB port**: power right module from its battery if only one host USB port; do not charge right-only from a wall adapter in a way that violates manual warnings.

**Profile LED colors**: 1 White, 2 Blue, 3 Red, 4 Green, 5 Off. Flash **fast** = pairing ready; **slow** = paired device out of range; **solid** = connected.

## Wireless vs USB

- Optimized for **Bluetooth**; **USB** supported for stability or when batteries die.
- Left and right still communicate **wirelessly** with each other; BT radio is not fully disabled in “wired” use.
- Pair as **“Adv360 Pro”** in the OS BT menu when Profile LED flashes white rapidly for that profile.

## Battery & charging

- **Battery**: 1500 mAh Li-ion per module, 3+ year lifespan.
- **Charge source**: PC USB-A port **only**. **Wall chargers, power bricks, and monitor USB ports are prohibited** — can damage battery, void warranty, render keyboard unsafe.
- **Charge time**: 6–8 hours full charge per module.
- **Cable**: included USB-C → USB-A.
- **Left module drains faster** (handles BT host connection).
- When plugged in via USB, the module runs off USB power (not battery).
- Charge only when necessary to maximize battery lifespan.

### Battery status check (`Mod` + `O`)

Hold `Mod` + `O` and read the indicator LEDs:

| LED Color | Charge Level |
|-----------|-------------|
| Green | > 80% (full/healthy) |
| Yellow | 51–79% |
| Orange | 21–50% |
| Red | < 20% (charge soon) |

**Note**: battery status may not work on Windows 11.

## LED color map & Gay.jl GF(3) analysis

The KB360 Pro uses 3 independent LED color systems. Each maps partially onto the GF(3) trit model from [Gay.jl](https://github.com/zubyul/Gay.jl) (`trit_from_hue`):

### Trit-to-hue reference (Gay.jl `three_match.jl`)

| Hue range | Trit | Category |
|-----------|------|----------|
| 0–60 or 300–360 | PLUS (+1) | Warm: red, orange, magenta |
| 60–180 | ERGODIC (0) | Cool: yellow, green, cyan |
| 180–300 | MINUS (−1) | Cold: blue, purple |

### Battery LEDs → GF(3)

| LED | Hue (approx) | Trit | Meaning |
|-----|-------------|------|---------|
| Green | ~120° | ERGODIC (0) | Healthy |
| Yellow | ~60° | ERGODIC (0) | Moderate |
| Orange | ~30° | PLUS (+1) | Low |
| Red | ~0° | PLUS (+1) | Critical |

**Observation**: battery uses only 2 of 3 trits (ERGODIC → PLUS). No MINUS state — there is no "cold" battery indicator. The hue gradient (120° → 0°) moves from cool to warm monotonically, which aligns with thermal/urgency semantics.

### Profile LEDs → GF(3)

| Profile | LED Color | Hue | Trit |
|---------|-----------|-----|------|
| 1 | White | achromatic | — (no trit) |
| 2 | Blue | ~240° | MINUS (−1) |
| 3 | Red | ~0° | PLUS (+1) |
| 4 | Green | ~120° | ERGODIC (0) |
| 5 | Off | — | — (vacancy) |

**Observation**: profiles 2–4 form a **complete GF(3) triad**: MINUS + ERGODIC + PLUS = 0. White and Off are achromatic/vacant — they sit outside the hue wheel entirely (Blume-Capel spin-0 vacancy).

### Layer LEDs → GF(3)

| Layer | LED Color | Hue | Trit |
|-------|-----------|-----|------|
| Base 0 | Off | — | vacancy |
| kp 1 | White | achromatic | — |
| fn 2 | Blue | ~240° | MINUS (−1) |
| Mod 3 | Green | ~120° | ERGODIC (0) |

**Observation**: only 2 of 4 layers carry chromatic trit information. The active layers (fn, Mod) are MINUS and ERGODIC — no PLUS layer exists in the default config. A custom ZMK layer with a warm-hued LED would close the triad.

### Color bandwidth considerations

Gay.jl achieves 7.4 billion colors/sec on M3 (8 threads) with SPI guarantees via KernelAbstractions. The KB360's WS2812 LEDs (3 per module, SPI3 at P0.20) operate at 800 Kbps per LED — orders of magnitude below Gay.jl's throughput. The bottleneck is the WS2812 protocol (24-bit GRB, 1.25 μs/bit), not color computation.

For gamut mapping: the WS2812 is sRGB-only (no P3/Rec.2020). Gay.jl's `clamp_to_gamut(color, GaySRGBGamut())` is the correct projection for any computed color destined for these LEDs. The `LearnableOkhsl` perceptual model can optimize for WS2812's limited gamut while maintaining perceptual uniformity.

## Hardware internals (ZMK board definitions)

Source: `KinesisCorporation/Adv360-Pro-ZMK` V3.0 branch, `config/boards/arm/adv360/`.

- **SoC**: Nordic nRF52840 QIAA (ARM Cortex-M4F, 64MHz, 1MB Flash, 256KB SRAM) per module
- **Key matrix**: 5 rows × 10 cols per module, `col2row` diodes. Combined: 20 cols × 5 rows (right uses `col-offset=10`)
- **Left GPIOs**: rows P1.11/P1.15/P0.03/P1.14/P1.12; cols P0.25/P0.11/P0.02/P0.28-31/P1.09/P0.12/P0.07
- **Right GPIOs**: rows P0.19/P0.05/P0.31/P0.30/P0.29; cols P0.12/P1.09/P0.07/P1.11/P1.10/P1.13/P1.15/P0.03/P0.02/P0.28
- **LEDs**: 3× WS2812 per module via SPI3 MOSI P0.20 (24-bit GRB, 800Kbps). sRGB gamut only. 16.7M colors per LED, ~4.7×10²¹ combined states (firmware locks to ~7 named colors)
- **Backlight**: PWM0 at P0.17 (white only, brightness control)
- **Battery**: voltage divider (100kΩ/100kΩ) → ADC Ch2
- **External power gate**: GPIO P0.13
- **Flash layout**: SoftDevice 152KB → ZMK app 792KB → NVS 32KB → UF2 bootloader 48KB
- **PCB**: flex PCB in keywells, soldered switches (not hot-swap), 5 screws per half (no glue), battery on disconnect header

## KMonad string diagram model

The key processing pipeline modeled as morphisms in a symmetric monoidal category (rendered via DisCoPy). See `kb360pro-kmonad-strings.py` for source.

### Wire types (objects)

| Type | Meaning |
|------|---------|
| `Key` | Raw matrix scan event (row, col) |
| `Event` | Press/Release with timestamp |
| `Layer` | Layer state (0–3), threads through as persistent state |
| `HID` | USB HID keycode |
| `USB` / `BLE` | Output report (wired / wireless) |
| `LED` | WS2812 RGB command |
| `Profile` | BT profile (1–5) |

### Full pipeline (string diagram)

```
Key ⊗ Layer
 │         │
[matrix_scan] │         +1 (GENERATE)
 │         │
Event    Layer
 │─────────│
[layer_lookup]          0 (TRANSPORT)
 │─────────│
HID      Layer
 │─────────│
[Mod_shortcuts]         0 (TRANSPORT)
 │     │       │
HID   Layer   LED
 │     │───────│
[HID_emit] [WS2812]    −1 (VERIFY)
 │    │      │
USB  BLE    LED
```

GF(3) conservation: `+1 + 0 + 0 + (−1) = 0 mod 3` ✓

### KMonad concept mapping

| KMonad | String diagram | Categorical operation |
|--------|---------------|----------------------|
| `defsrc` | Input wires (`Key`) | Domain of morphism |
| `deflayer` | Box `Event → HID` | Morphism per layer |
| Layer stack | `Layer` wire threading through | Traced state wire |
| `tap-hold 200` | Box `Event → HID ⊗ Layer` | Coproduct (tap xor hold) |
| Split keyboard | `(Left ⊗ Right) >> BLE_merge` | Tensor then merge |
| `around` (modifier wrap) | Sequential composition `>>` | Morphism composition |
| `multi-tap` | Box with branching | Coproduct fan-out |
| Profile switch | `Mod+N >> (BT_connect ⊗ Profile_LED)` | Composition + tensor |

### Concatenative (Forth) view

KMonad processes keys like a stack machine:

```
push(event) → lookup(layer) → emit(hid)
Key @ Layer → Key @ Event @ Layer → Key @ HID → Key @ USB
```

Each stage is a word operating on the implicit stack. Composition = concatenation.

## Troubleshooting (quick)

1. Power-cycle: disconnect/off **both** modules → on/connect **left**, wait ~5s → then **right**.
2. Right module **all three LEDs flashing red**: right searching for left — power-cycle; check batteries (`Mod` + `O`).
3. Order of operations: prefer **left first / left last** when connecting or disconnecting to avoid right searching alone.
4. Stale BT: forget **Adv360 Pro** on the computer **and** run keyboard **Bluetooth clear** for that profile, then re-pair.

## Site data (automation)

- **No public GraphQL** on `kinesis-ergo.com` (WordPress exposes **REST**: `https://kinesis-ergo.com/wp-json/`). The KB360 support **page** (`slug`: `kb360pro`) often has **empty `content.rendered`** in REST because rendering uses a **custom template**; treat the **live HTML** and **PDFs** as source of truth.
- Efficient pull: `curl` the support URL and grep `href=.*\.pdf`, or fetch PDFs directly from the table above.

## Limitations

- This skill summarizes manufacturer docs; for conflicts, **official PDFs and support page** win.
- Do not paste full manuals into chat; **link** the PDFs or extract short excerpts locally (e.g. `markitdown`, `pypdf`).
