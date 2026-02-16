---
name: reality-tech
description: Reality tech umbrella for AR/VR/XR. Choose the right stack (WebXR/OpenXR/Unity/Unreal) and ship with strong defaults for comfort, performance, and privacy.
license: Apache-2.0
metadata:
  trit: 0
  version: "1.0.0"
  bundle: reality-tech
---

# Reality Tech (AR / VR / XR)

Use this skill as a router when the user asks about spatial computing, headsets, passthrough, WebXR/OpenXR, or immersive UI.

Preferred entrypoint skill: `ar-vr-xr` (full workflow + checklists).

## Quick Routing

- If the user says AR (passthrough overlays, hit-test, anchors, occlusion): use `ar`
- If the user says VR (immersion, locomotion, controllers, roomscale): use `vr`
- If the user says XR/MR (mixed reality, spatial computing): use `xr` or `ar-vr-xr`

## First Questions (Only Ask What Blocks Progress)

Ask up to 3:
1. Target platform: Web (WebXR) or native (OpenXR via Unity/Unreal)?
2. Target device(s): Quest, Vision Pro, PCVR (SteamVR), mobile AR?
3. Primary interaction: hands, controllers, gaze?

## Interleave With

- `visual-design` for spatial UI
- `threat-model-generation` + `security-review` for sensor and privacy risks
- `bandwidth-benchmark` for streaming constraints
- `jepsen-testing` for correctness testing of shared-state XR backends
- `varjo-xr-4` when the target hardware is Varjo XR-4 Series
- `steamvr-tracking` for Lighthouse/base station setup- `xr-color-management` for sRGB/P3/Rec.2020 pipeline issues
