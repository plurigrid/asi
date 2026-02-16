---
name: ar-vr-xr
description: Reality tech (AR/VR/XR). Build and ship spatial experiences (WebXR/OpenXR/Unity/Unreal) with strong defaults for interaction, performance, comfort, privacy, and deployment.
license: Apache-2.0
metadata:
  trit: 0
  version: "1.0.0"
  bundle: reality-tech
---

# AR / VR / XR (Reality Tech)

Use this skill when the user is building or debugging:
- AR (camera passthrough overlays)
- VR (fully immersive)
- XR/MR (mixed reality, spatial computing)
- WebXR/OpenXR, Quest/Vision Pro/PCVR
- Unity/Unreal/Web (Three.js, Babylon.js, A-Frame)

## First Questions (Only Ask What Blocks Progress)

Ask up to 3:
1. Target platform: Web (WebXR) or native (OpenXR via Unity/Unreal)?
2. Target device(s): Quest, Vision Pro, PCVR (SteamVR), mobile AR (ARKit/ARCore), other?
3. Interaction + locomotion: hands, controllers, gaze, roomscale, smooth locomotion, teleport?

If the user does not know yet, default to:
- WebXR + Three.js for a fast prototype
- Teleport locomotion + snap-turn for comfort

## Workflow

1. Define the experience mode and constraints.
   - AR vs VR vs MR
   - Required capabilities: 3DoF/6DoF, plane detection, meshing, hand tracking, anchors

2. Establish world scale and coordinate conventions early.
   - 1 unit = 1 meter (recommended)
   - Choose a single "up" axis and stick to it end-to-end

3. Build a vertical slice (minimum shippable loop).
   - Tracking + session start
   - One interaction (grab/select)
   - One UI surface (menu, tooltip, reticle)

4. Budget performance from day 1.
   - Stable frame time beats peak quality
   - Reduce draw calls, overdraw, shader cost, and texture bandwidth

5. Enforce comfort defaults.
   - Avoid sustained acceleration
   - Prefer teleport and snap-turn
   - Keep UI readable and at comfortable depth

6. Treat privacy and sensors as first-class.
   - Camera/mic permissions, spatial maps, room meshes, biometrics
   - Minimize collection, document clearly, store locally when possible

## WebXR Quickstart (Three.js)

```js
import * as THREE from 'three';
import { VRButton } from 'three/examples/jsm/webxr/VRButton.js';

const scene = new THREE.Scene();
const camera = new THREE.PerspectiveCamera(70, window.innerWidth / window.innerHeight, 0.01, 100);
const renderer = new THREE.WebGLRenderer({ antialias: true });
renderer.setSize(window.innerWidth, window.innerHeight);
renderer.xr.enabled = true;
document.body.appendChild(renderer.domElement);
document.body.appendChild(VRButton.createButton(renderer));

const light = new THREE.HemisphereLight(0xffffff, 0x444444, 1.0);
scene.add(light);

const floor = new THREE.Mesh(
  new THREE.PlaneGeometry(10, 10),
  new THREE.MeshStandardMaterial({ color: 0x222222 })
);
floor.rotation.x = -Math.PI / 2;
scene.add(floor);

renderer.setAnimationLoop(() => {
  renderer.render(scene, camera);
});
```

Notes:
- WebXR requires HTTPS (or localhost).
- To target AR: request an `immersive-ar` session and handle hit-test/anchors (framework-specific).

## OpenXR Notes (Unity/Unreal)

- Unity: prefer XR Plugin Management + OpenXR plugin; use XR Interaction Toolkit for baseline interaction.
- Unreal: use the OpenXR plugin; validate input mappings per device.

When debugging native XR:
- Confirm runtime: OpenXR runtime (SteamVR, Oculus, WMR) and version
- Validate action bindings and controller profiles
- Verify frame timing on-device, not just in editor

## Comfort Checklist

- Keep horizon stable; avoid camera bob unless user opts in
- Use snap-turn (30-45 deg) by default
- Teleport is the safest default locomotion
- Avoid "forced" motion tied to animations
- UI: large text, high contrast, avoid depth conflict (z-fighting)

## Performance Checklist

- Measure on target device (Quest/Vision Pro/PCVR), not only desktop
- Reduce: draw calls, transparent layers, dynamic shadows, post-processing
- Prefer baked lighting where possible
- Stream assets with progressive quality (LOD), avoid blocking loads


## Device Profile: Varjo XR-4

If the target device is Varjo XR-4 Series, use `varjo-xr-4` for runtime/tracking/refresh-rate specifics.

## Interleave With New Skills (plurigrid/asi PRs #61-64)

Use these as building blocks:
- `visual-design`: spatial UI readability, typography, contrast, layout
- `svelte-components` / `sveltekit-structure` / `sveltekit-data-flow`: WebXR shells, menus, settings, content pipelines
- `browser-navigation`: XR web debugging and reproducible repro steps
- `bandwidth-benchmark`: asset streaming, scene/texture delivery constraints
- `threat-model-generation` + `security-review`: sensors, permissions, privacy, on-device data
- `jepsen-testing`: correctness thinking for multi-user/shared-state XR backends


## Jepsen For Shared-State XR

Use `jepsen-testing` when your experience includes a backend claim about correctness under faults (multiplayer rooms, shared anchors, inventories, authoritative physics, replicated scene graphs).

XR-specific intake:
- Define the surface: websocket RPC, REST/gRPC, realtime relay, or a persistence API.
- Define acknowledged for XR ops (e.g., "spawn confirmed", "anchor committed", "inventory write ok").
- Pick a checkable property per primitive:
- Room membership/presence: no phantom joins, monotonic session state.
- Object transforms: no lost acknowledged updates; no impossible readbacks.
- Anchors/placements: placement does not disappear after an ok, unless explicitly deleted.

Faults worth testing:
- Partitions between clients and relay/region.
- Process kill/restart of relay, authoritative host, or storage layer.
- Clock skew if you use timestamps for conflict resolution.

Minimization tip:
- Reduce to 1-2 rooms, 2-3 objects, and a single nemesis schedule until the violation is explainable.

## Example Prompts This Skill Should Handle

- "Build a WebXR VR scene with teleport and grab interactions"
- "Port this Unity project to OpenXR and fix controller bindings"
- "Optimize this Quest app to hit stable 72/90 fps"
- "Design a spatial settings UI that stays readable in passthrough"
- "Threat-model an AR app that uses camera + spatial mapping"
- `steamvr-tracking` for Lighthouse/base station setup- `xr-color-management` for sRGB/P3/Rec.2020 pipeline issues
