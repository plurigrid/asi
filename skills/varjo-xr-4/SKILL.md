---
name: varjo-xr-4
description: Varjo XR-4 Series device profile for reality tech. Covers Varjo Base, OpenXR/OpenVR runtime setup, tracking options (inside-out vs SteamVR), and wide-gamut display notes.
license: Apache-2.0
metadata:
  trit: 0
  version: "1.0.0"
  bundle: reality-tech
---

# Varjo XR-4 Series (Device Profile)

Use when the user targets Varjo XR-4 / XR-4 Focal Edition / XR-4 Secure Edition.

## What Matters Most

- Wide-gamut mini-LED displays (98% sRGB / 96% DCI-P3) and high PPD (up to 51)
- Windows + Varjo Base is the control plane
- OpenXR is the default modern API target; OpenVR is still relevant for SteamVR apps
- Tracking mode choice changes your deployment: inside-out vs base-station (SteamVR)

## Setup + Runtime

- Install Varjo Base.
- If prompted, enable OpenXR and OpenVR runtimes (needed for OpenXR apps and SteamVR/OpenVR apps).

## Tracking Options

- Inside-out tracking (no base stations)
- SteamVR Tracking on base station tracking variants (base stations + optional controllers/trackers)
- Third-party tracking (ART/OptiTrack) via API integrations

## Refresh Rate (Practical)

- Typical options are 75 Hz or 90 Hz (configured in Varjo Base).
- 90 Hz is the safer default for VR comfort if you can hit frame rate; 75 Hz can reduce GPU load.

## Color / Rendering Notes

- XR-4 has high DCI-P3 coverage; for color-critical work, validate your look in-headset.
- Treat wide-gamut as a display capability, not a guarantee of correct color: calibration, tone mapping, and content decisions still matter.

## Good “First Questions” For XR-4 Work

Ask up to 3 (only if needed):
1. Are we targeting OpenXR (recommended) or SteamVR/OpenVR legacy content?
2. Which tracking variant do you have: inside-out only or XR-4 base station tracking?
3. What’s the priority: max fidelity (PPD) or stable frame time (comfort)?

## Interleave With

- `steamvr-tracking` for base station specs/placement and pairing
- `xr-color-management` for wide-gamut pipeline and debugging
