---
name: xr-color-management
description: Color spaces and gamuts in XR. sRGB vs DCI-P3 vs Rec.2020, OpenXR swapchain formats, and practical guidance for wide-gamut headsets.
license: Apache-2.0
metadata:
  trit: 0
  version: "1.0.0"
  bundle: reality-tech
---

# XR Color Management

Use when the user asks about:
- "best color space" / DCI-P3 / Rec.2020 / sRGB
- why colors look washed out or oversaturated in-headset
- how to ship consistent color across headsets

## Ground Truth

- Color gamut coverage (e.g., "96% DCI-P3") is display capability, not color accuracy.
- XR runtimes often compose in linear space; apps must be explicit about sRGB vs linear formats.

## Practical Defaults

- Keep your pipeline sRGB-correct unless you *know* your runtime + device support wide-gamut end-to-end.
- Prefer a linear rendering workflow with sRGB textures flagged correctly.
- Validate with in-headset test patterns (ramps, skin tones, near-black, saturation sweeps).

## OpenXR Notes

- Use API-specific sRGB swapchain formats when your render targets are sRGB encoded.
- If you submit linear data in 8-bit formats, banding and incorrect tones are common.

## Vendor Extensions (When Available)

- Some runtimes expose explicit color space selection (e.g., Meta's `XR_FB_color_space` can request P3 / Rec.2020 / Rec.709).

## Troubleshooting Checklist

- Confirm you’re not double-applying gamma (too dark/too contrasty) or skipping sRGB decode (too bright/washed).
- Check post-processing: tone mapping, color grading LUTs, exposure auto.
- If the runtime/toolkit offers post-processing (OpenXR Toolkit etc.), use it only to validate hypotheses, not as a permanent substitute for correct pipeline.

## Interleave With

- `varjo-xr-4` for XR-4-specific refresh-rate and Varjo Base settings
- `steamvr-tracking` when the XR setup uses Lighthouse base stations
- `visual-design` (from plurigrid/asi PR #61) for readable spatial UI color/contrast
