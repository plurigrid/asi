---
name: openscad-bci-hardware
description: Parametric OpenSCAD models for BCI electrode holders, paste adapters, headset hooks, pogo combs, fNIRS housings, and eurorack frames. Use when designing, modifying, or 3D-printing brain-computer interface hardware.
version: 1.0.0
trit: 0
---

# OpenSCAD BCI Hardware

Parametric 3D models for brain-computer interface and neuromodulation hardware.

## Assets Index

| Model | File | Purpose |
|---|---|---|
| Electrode Holder Mod | `electrode_holder_mod.scad` | Modified EEG electrode holder for dry/wet electrodes |
| Paste Adapter | `paste_adapter.scad` | Conductive paste application adapter for wet EEG |
| Headset Hook | `headset_hook.scad` | Mounting hook for BCI headset suspension |
| C3/C4 Pogo Comb | `c3c4_pogo_comb.scad` | Spring-loaded pogo pin electrode comb for motor cortex (C3/C4 10-20 system) |
| fNIRS ECU Housing | `ecu_housing_base.stl` + `ecu_housing_lid.stl` | OpenNIRScap electronics enclosure |
| fNIRS Sensor Capsule | `sensor_capsule.stl` | Light source/detector capsule for fNIRS optodes |
| Electrode Plate 8-up | `electrode_plate_8up.stl` | 8-position electrode array plate |
| Eurorack Frame | `frame-rail.stl`, `frame-connector.stl`, `frame-stand.stl` | Moduleur eurorack housing for BCI signal chain |

## Usage

```bash
# Render STL from SCAD
openscad -o output.stl -D 'electrode_diameter=10' electrode_holder_mod.scad

# Batch render all SCAD files
for f in *.scad; do openscad -o "${f%.scad}.stl" "$f"; done
```

## Design Constraints

- All models parametric (electrode diameter, spacing, head circumference)
- Print orientation: flat side down, no supports needed for most parts
- Material: PETG recommended for skin contact (autoclavable)
- Tolerances: 0.2mm for press-fit, 0.4mm for sliding fit

## Integration

- Pairs with `zig-syrup-bci` for signal acquisition firmware
- Pairs with `opennirscap-build` for fNIRS cap assembly
- Pairs with `cyton-dongle` for OpenBCI Cyton/Daisy connection
