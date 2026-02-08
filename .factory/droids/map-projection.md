---
name: map-projection
description: Map Projection Skill
model: inherit
tools: ["Read", "Edit", "Execute", "WebSearch"]
---

# Map Projection Skill

Category theory of map projections: functors between manifolds with distortion analysis.

## Trigger
- Map projection selection and analysis
- Distortion metrics (Tissot's indicatrix)
- Coordinate system transformations
- Cartographic design decisions

## GF(3) Trit: +1 (Generator)
Generates projections from sphere to plane, creating new coordinate representations.

## Category Theory of Projections

A map projection is a functor:
```
P: Sphere → Plane
   S² → ℝ²
```

Different projections preserve different properties:
- **Conformal** (angle-preserving): Mercator, Stereographic
- **Equal-area**: Albers, Lambert, Mollweide
- **Equidistant**: Azimuthal equidistant
- **Compromise**: Robinson, Winkel Tripel

## Projection Functors

```python
import math

class Projection:
    """Base projection functor."""
    
    def forward(self, lat, lon):
        """S² → ℝ²"""
        raise NotImplementedError
    
    def inverse(self, x, y):
        """ℝ² → S²"""
        raise NotImplementedError
    
    @property
    def distortion_type(self):
        raise NotImplementedError

class Mercator(Projection):
    """Conformal cylindrical projection."""
    
    def forward(self, lat, lon):
        x = math.radians(lon)
        y = math.log(math.tan(math.pi/4 + math.radians(lat)/2))
        return x, y
    
    def inverse(self, x, y):
        lon = math.degrees(x)
        lat = math.degrees(2 * math.atan(math.exp(y)) - math.pi/2)
        return lat, lon
    
    @property
    def distortion_type(self):
        return "conformal"  # Preserves angles

class LambertAzimuthal(Projection):
    """Equal-area azimuthal projection."""
    
    def __init__(self, lat0=0, lon0=0):
        self.lat0 = math.radians(lat0)
        self.lon0 = math.radians(lon0)
    
    def forward(self, lat, lon):
        phi = math.radians(lat)
        lam = math.radians(lon)
        
        k = math.sqrt(2 / (1 + math.sin(self.lat0)*math.sin(phi) + 
                          math.cos