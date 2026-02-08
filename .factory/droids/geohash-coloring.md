---
name: geohash-coloring
description: Geohash Coloring Skill
model: inherit
tools: ["Read", "Edit", "Execute", "WebSearch"]
---

# Geohash Coloring Skill

GF(3) colored geohashes for hierarchical spatial indexing with deterministic color derivation.

## Trigger
- Geohash encoding/decoding
- Hierarchical spatial clustering
- Location-based coloring schemes
- Privacy-preserving location representation

## GF(3) Trit: +1 (Generator)
Generates colored spatial identifiers from coordinates.

## Geohash Basics

Geohash encodes lat/lon into a string where:
- Longer = more precise
- Prefix = parent cell
- Adjacent cells share prefixes

```
Precision | Cell Width | Cell Height
    1     |  5,009 km  |  4,992 km
    2     |  1,252 km  |    624 km
    3     |    156 km  |    156 km
    4     |     39 km  |     19 km
    5     |      5 km  |      5 km
    6     |    1.2 km  |    0.6 km
    7     |    153 m   |    153 m
    8     |     38 m   |     19 m
    9     |      5 m   |      5 m
```

## Core Implementation

```python
import hashlib

# Geohash alphabet (base32)
GEOHASH_CHARS = '0123456789bcdefghjkmnpqrstuvwxyz'

def encode_geohash(lat: float, lon: float, precision: int = 9) -> str:
    """Encode lat/lon to geohash string."""
    lat_range = (-90.0, 90.0)
    lon_range = (-180.0, 180.0)
    
    geohash = []
    bits = 0
    bit_count = 0
    is_lon = True
    
    while len(geohash) < precision:
        if is_lon:
            mid = (lon_range[0] + lon_range[1]) / 2
            if lon >= mid:
                bits = (bits << 1) | 1
                lon_range = (mid, lon_range[1])
            else:
                bits = bits << 1
                lon_range = (lon_range[0], mid)
        else:
            mid = (lat_range[0] + lat_range[1]) / 2
            if lat >= mid:
                bits = (bits << 1) | 1
                lat_range = (mid, lat_range[1])
            else:
                bits = bits << 1
                lat_range = (lat_range[0], mid)
        
        is_lon = not is_lon
        bit_count += 1
        
        if bit_count == 5:
            geohash.append(GEOHASH_CHARS[bits])
          