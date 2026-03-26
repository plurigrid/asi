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
