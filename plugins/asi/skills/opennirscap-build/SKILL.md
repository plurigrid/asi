---
name: opennirscap-build
description: Build an OpenNIRScap 24-channel fNIRS brain cap from open-source hardware — Altium conversion, BOM sourcing, PCB fab, assembly, firmware flash
---

# OpenNIRScap Build

Open-source 24-channel fNIRS wearable brain cap. Kim et al. 2025, University of Toronto.

## Source

- Repo: https://github.com/tonykim07/fNIRS
- Paper: https://arxiv.org/abs/2505.20509
- License: BSD-3-Clause
- Hardware: Altium Designer files (PcbDoc, SchDoc)
- Firmware: STM32 C (STM32L476RET6)
- Software: Python Flask-SocketIO GUI

## Architecture

- 24 detector modules (VBPW34S photodiode + AD8618 TIA, 25mm circular PCB)
- 8 dual-wavelength source emitters (VSMD66694: 660nm + 940nm)
- 1 ECU (STM32L476 + 8x TMUX1104 analog MUX + PCA9685 PWM, 112x112mm PCB)
- 35mm source-detector separation (cortical depth sensitivity)
- 1 kHz effective sampling, 52.3 dB SNR, 12-bit ADC
- USB isolated (ADUM4160), LiPo powered (1100mAh, >5hr)

## Blocker: Altium to Gerber Conversion

Repo has Altium .PcbDoc source files, no exported gerbers or CSV BOMs.

### PCBs to convert

| Project | File | Description |
|---------|------|-------------|
| fNIRS_sensor_module | SensorModulePCB.PcbDoc | 25mm circular, combined emitter+detector |
| fNIRS_ECU | fNIRS_PCB.PcbDoc | 112x112mm main control board |
| DetectorOptode | DetectorOptode.PcbDoc | Detector-only variant |
| SourceOptode | SourceOptode.PcbDoc | Source-only variant |
| STLINK_Breakout | STLINK_Breakout.PcbDoc | Programming adapter |

### Conversion approaches (in order of preference)

1. **KiCad 8 built-in importer** — File > Import > Altium .PcbDoc. Best fidelity. Needs KiCad installed.
2. **altium2kicad** (Perl, 933 stars) — `perl convertpcb.pl file.PcbDoc`. Repo: thesourcerer8/altium2kicad. Needs `unpack.pl` first.
3. **Altium 365 Viewer** (free web) — View online, manual export. No CLI.
4. **GitHub Issue** — Ask authors to export gerbers. Repo is active (last push 2026-03).

### Attempted and failed

- `altium-cli` (Rust, akiselev) — broken workspace deps, won't build
- `pyaltium` — crashes on Python 3.14 (missing dateutil dep)
- `altium2kicad` unpack.pl worked but convertpcb.pl couldn't find unpacked files

### Next step

Install KiCad 8 (`brew install --cask kicad` or `nix shell nixpkgs#kicad`), import PcbDoc, export gerbers + BOM + CPL from KiCad.

## BOM — Semiconductors (DigiKey)

| Part | MPN | Qty | DigiKey URL |
|------|-----|-----|-------------|
| Photodiode | VBPW34S | 24 | https://www.digikey.com/en/products/detail/vishay-semiconductor-opto-division/VBPW34S/4073399 |
| Quad op-amp | AD8618ARUZ | 12 | https://www.digikey.com/en/products/detail/analog-devices-inc/AD8618ARUZ/1993937 |
| Dual LED 660/940nm | VSMD66694 | 8 | https://www.digikey.com/en/products/detail/vishay-semiconductor-opto-division/VSMD66694/7681025 |
| N-ch MOSFET | BSD840NH6327XTSA1 | 16 | https://www.digikey.com/en/products/detail/infineon-technologies/BSD840NH6327XTSA1/5409567 |
| MCU | STM32L476RET6 | 1 | https://www.digikey.com/en/products/detail/stmicroelectronics/STM32L476RET6/5177041 |
| Analog MUX | TMUX1104DBVR | 8 | https://www.digikey.com/en/products/detail/texas-instruments/TMUX1104DBVR/9685876 |
| PWM/IO | PCA9685PW,118 | 3 | https://www.digikey.com/en/products/detail/nxp-usa-inc/PCA9685PW-118/2034325 |
| USB isolator | ADUM4160BRWZ | 1 | https://www.digikey.com/en/products/detail/analog-devices-inc/ADUM4160BRWZ/1861340 |

## BOM — Passives (0603 SMD, from schematic)

Core known values (exact values need Altium schematic export):
- 60.4k 1% x24 (TIA feedback)
- 200pF x24 (TIA bandwidth, fc~13kHz)
- 100nF x60 (bypass, 2 per board + ECU)
- 4.7k x4 (I2C pullups)
- LED current limit resistors x16

## BOM — Amazon

| Item | URL |
|------|-----|
| 3.7V 1100mAh LiPo JST | https://www.amazon.com/Qimoo-Battery-Rechargeable-Connector-Electronic/dp/B0CNLNGBT4 |
| ST-LINK V2 programmer | https://www.amazon.com/ST-Link-Programming-Emulator-Downloader-Random/dp/B08YZ4K3Z5 |
| 8-pin ribbon cable IDC | https://www.amazon.com/DMiotech-Ribbon-Digital-Cameras-Computers/dp/B0CJYV768J |
| PLA filament 1.75mm | https://www.amazon.com/ELEGOO-PLA-Filament-1-75mm-Printers/dp/B0C14PXRZH |
| Velcro strips | https://www.amazon.com/VELCRO-Brand-Sticky-Fasteners-Perfect/dp/B00006IC2L |
| 3M Micropore tape | https://www.amazon.com/Micropore-Medical-Dispenser-Friendly-NonSterile/dp/B00PZ2F1Q6 |
| Neoprene headband | https://www.amazon.com/Headband-Neoprene-Hairband-Non-Slip-Snorkeling/dp/B0FB8Y968R |

## BOM — PCBs (JLCPCB, after gerber export)

- 24x sensor module (25mm circular)
- 1x ECU (112x112mm, 4-layer)
- 1x STLINK breakout

## Cost Summary

| Category | Cost |
|----------|------|
| Semiconductors | ~$130 |
| Passives | ~$15 |
| PCBs | ~$13 |
| Amazon | ~$150 |
| **Total** | **~$310-420** |

## Assembly

1. Export gerbers from KiCad (after Altium import)
2. Order PCBs from JLCPCB
3. Order DigiKey + Amazon parts
4. Solder sensor modules (24x, SMD 0603 + photodiode + LED)
5. Solder ECU (QFP-64 MCU, SOT-23 MUXes, TSSOP PWM)
6. Wire cable harnesses (8 groups of 3 sensors)
7. 3D print sensor capsules (STL from repo or design in OpenSCAD)
8. Flash firmware via SWD (ST-LINK)
9. Connect USB, run Python GUI
10. Calibrate on forehead, verify heart rate waveform first

## bci.horse Integration

- Tree: bcf-0036 in plurigrid/horse
- Inventory ID: planned, not yet ordered
- Role: walk-up fNIRS fleet ($419/unit vs $50k NIRSport 2)
- Calibrate against Artinis Brite Lite (if purchased)

## Firmware

Located in `firmware/STM32/fNIRS/`. STM32CubeIDE project.
- MCU: STM32L476RET6, ARM Cortex-M4 80MHz
- ADC: 12-bit, DMA, 5kHz raw sampling, multiplexed to 1kHz effective
- USB: CDC serial via ADUM4160 isolator
- PWM: PCA9685 drives LED sources, alternating 660/940nm
- SD: SDMMC logging

## Software

Located in `software/`. Python 3.
- Flask-SocketIO backend for real-time streaming
- Web GUI: Plotly.js + BrainNet Viewer 3D brain mesh
- Modified Beer-Lambert Law processing (NIRSimple library)
- Bandpass 0.01-0.5 Hz for cortical hemodynamics
- Correlation-based signal improvement for HbO/HbR

## Related Skills

- `forester` — bci.horse forest publishing (bcf-0036 is this device's tree)
- `reverse-engineering` — MCP servers for Ghidra/radare2/IDA if binary analysis needed
- `binary-triage` — systematic binary survey workflow
- `performing-firmware-extraction-with-binwalk` — firmware extraction from embedded devices
- `protocol-reverse-engineering` — reverse engineering communication protocols
- `radare2-hatchery` — radare2 ecosystem tools

## Altium Conversion Tools

- `altium2kicad` (Perl, 933 stars): https://github.com/thesourcerer8/altium2kicad
- KiCad 8 built-in Altium importer: https://www.kicad.org/blog/2020/04/Development-Highlight-Altium-Pcb-Importer/
- `altium-cli` (Rust, broken): https://github.com/akiselev/altium-cli
- KiCad Forum thread on CLI import: https://forum.kicad.info/t/how-to-import-altium-pcbdoc-via-commandline-tools/50893

## Why This Build

### The problem
Research-grade fNIRS (NIRx NIRSport 2) costs $50k-150k. PLUX biosignalsplux fNIRS sensor is $789 for 1 channel with short source-detector separation — measures superficial scalp hemodynamics, not cortical activity.

### Source-detector separation is everything
Light follows a banana-shaped path through tissue. Separation controls measurement depth:
- <10mm: scalp blood flow (artifact)
- 30mm: gray matter (cortical hemodynamics — what we want)
- >50mm: too much attenuation

Per Strangman et al. (PLOS ONE 2013): every 10mm increase up to ~45mm adds ~4% gray matter sensitivity. Depth sensitivity decays as S = 0.75 * 0.85^depth.

PLUX has emitter+detector in one housing = short path = scalp oximetry.
NIRSport 2 uses separate optodes at 30mm = cortical imaging = $50k+.
OpenNIRScap uses separate optodes at 35mm = cortical imaging = $419.

### Why OpenNIRScap specifically
- 24 channels (vs PLUX 1ch, vs DIY-fNIRS headband 4ch)
- 35mm separation (proper cortical depth)
- 52.3 dB SNR, 1 kHz sampling
- Validated hemodynamic response during cognitive tasks (paper Fig. 10)
- $419 total BOM from off-the-shelf parts
- Fully open source (BSD-3, hardware + firmware + software)
- Published May 2025, repo active March 2026
- Comparison from paper (Table II): 24ch/$419/open vs 4ch/$215/open vs 1ch/$789/proprietary

### The strategy for bci.horse
Build 3x OpenNIRScap ($1,257) as the walk-up fNIRS fleet. If/when a commercial reference is acquired (Artinis Brite Lite ~$6k or Cortivision Spectrum C23), use it to validate OpenNIRScap signal quality. The AFE4404 in the earlier DIY spec (bcf-0012) uses the same modified Beer-Lambert deconvolution as NIRx's proprietary pipeline — the physics is identical, only the engineering precision differs.

### Key references
- OpenNIRScap paper: https://arxiv.org/abs/2505.20509
- OpenNIRScap repo: https://github.com/tonykim07/fNIRS
- ninjaNIRS (200 optodes, openfnirs.org): https://openfnirs.org/hardware/ninjanirs/
- Strangman depth sensitivity: https://journals.plos.org/plosone/article?id=10.1371/journal.pone.0066319
- NIRDuino (Arduino fNIRS): https://www.medrxiv.org/content/10.1101/2024.12.20.24318425v1
- FlexNIRS (open-source): https://www.sciencedirect.com/science/article/pii/S1053811922003408
- DIY-fNIRS headband: https://www.hardware-x.com/article/S2468-0672(21)00033-X/fulltext
- Lieberman Lab UCLA (NIRx NIRSport 2 user): Miao, Lieberman, Pluta 2025 hyperscanning review
- Artinis Brite Lite: https://www.artinis.com/brite-lite
- Cortivision Spectrum C23: https://www.cortivision.com/spectrum-23/
- PLUX fNIRS sensor datasheet: https://support.pluxbiosignals.com/wp-content/uploads/2021/10/biosignalsplux-FNIRS-Datasheet.pdf
- bci.horse source-detector physics tree: bcf-0034 in plurigrid/horse
- bci.horse fNIRS comparison: bcf-0032 (NIRSport), bcf-0035 (Brite Lite), bcf-0036 (OpenNIRScap)
