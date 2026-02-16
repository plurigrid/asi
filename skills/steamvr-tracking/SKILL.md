---
name: steamvr-tracking
description: SteamVR Tracking (Lighthouse/Base Stations) setup + specs. Use for playspace sizing, base station placement, compatibility, and troubleshooting across SteamVR-tracked headsets.
license: Apache-2.0
metadata:
  trit: 0
  version: "1.0.0"
  bundle: reality-tech
---

# SteamVR Tracking (Base Stations / Lighthouse)

Use when the user is:
- Setting up Valve/HTC base stations
- Using a headset/controller/tracker that relies on SteamVR Tracking (outside-in)
- Debugging tracking drift, occlusion, or playspace geometry

## What To Ask First (Only If It Blocks Progress)

1. Base station generation: 1.0 or 2.0?
2. How many base stations: 2, 3, or 4?
3. Target playspace size and ceiling height?

## Key Concepts

- Base stations are not cameras; they sweep IR laser patterns that tracked devices read.
- Tracking quality is mostly about:
- Visibility (avoid occlusion)
- Placement geometry (cover the full volume)
- Reflective surfaces (windows/mirrors) and IR interference

## Quick Placement Rules

- Start with 2 base stations, opposite corners, high up, angled down.
- Add a 3rd/4th station only to cover dead zones or larger spaces.
- Avoid direct reflections (mirrors, glossy TV, large windows).

## Compatibility / Gotchas

- Base station 2.0 requires 2.0-tracking-capable hardware.
- For headsets that support both inside-out and SteamVR Tracking (e.g., Varjo/Pimax variants), make sure the runtime and tracking mode match the app:
- SteamVR/OpenVR apps: ensure SteamVR Tracking mode is active and the vendor SteamVR add-on is enabled.

## Interleave With

- `varjo-xr-4` for XR-4 tracking mode + Varjo Base runtime switches
- `ar-vr-xr` for comfort/perf defaults
- `jepsen-testing` when the XR experience depends on a shared-state backend correctness claim
