---
name: olmoearth-mlx
description: "OlmoEarth MLX: Spatio-Temporal Earth Intelligence"
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# OlmoEarth MLX: Spatio-Temporal Earth Intelligence

**Trit**: +1 (PLUS - world creation via planetary observation)  
**Foundation**: AI2 OlmoEarth + Apple MLX + GeoACSet + Dune.xyz Geographic WEV

## Overview

OlmoEarth is AI2's open spatio-temporal foundation model for planetary intelligence, trained on:
- Sentinel-2 L2A (12 bands, 10-60m resolution)
- Sentinel-1 SAR (VV, VH polarization)
- Landsat (historical continuity)
- WorldCover (11 land cover classes)
- OpenStreetMap raster
- SRTM elevation
- WRI Canopy Height Map

This skill enables:
1. **Geographic embedding** of crypto wallet activity from Dune.xyz
2. **Impact area identification** for Protocol Labs infrastructure
3. **GeoACSet materialization** for categorical spatial reasoning

## Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                     OLMOEARTH-MLX PIPELINE                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  Dune.xyz Query ─┬─► IP Geolocation ─┬─► OlmoEarth Embedding            │
│                  │                   │                                  │
│  Wallet Activity ┘   Region Bounds  ─┘   FlexiVit Encoder               │
│                                              │                          │
│                                              ▼                          │
│                              ┌───────────────────────────────────┐      │
│                              │     GeoACSet Materialization      │      │
│                              │   Regions → Districts → Parcels   │      │
│                              │        with GF(3) trits           │      │
│                              └───────────────────────────────────┘      │
│                                              │                          │
│                                              ▼                          │
│          