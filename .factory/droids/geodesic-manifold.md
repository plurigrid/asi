---
name: geodesic-manifold
description: Geodesic Manifold Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Geodesic Manifold Skill

Spherical geometry, great circles, and Riemannian manifolds with Gay.jl coloring.

## Trigger
- Geodesic calculations, great circle routes
- Spherical trigonometry, haversine distance
- Riemannian geometry on Earth's surface
- Flight paths, navigation, ship routing

## GF(3) Trit Assignment
- **+1 (Generator)**: Creates geodesic paths, generates waypoints
- **0 (Ergodic)**: Distance calculations, coordinate transforms
- **-1 (Validator)**: Verifies shortest path optimality

## Core Concepts

### Great Circle Distance (Haversine)
```python
import math

def haversine(lat1, lon1, lat2, lon2):
    """Distance in km between two points on Earth."""
    R = 6371  # Earth radius km
    
    phi1, phi2 = math.radians(lat1), math.radians(lat2)
    dphi = math.radians(lat2 - lat1)
    dlambda = math.radians(lon2 - lon1)
    
    a = math.sin(dphi/2)**2 + math.cos(phi1) * math.cos(phi2) * math.sin(dlambda/2)**2
    c = 2 * math.atan2(math.sqrt(a), math.sqrt(1-a))
    
    return R * c
```

### Geodesic Waypoints with Color
```python
def geodesic_waypoints(lat1, lon1, lat2, lon2, n_points, seed):
    """Generate colored waypoints along great circle."""
    from math import radians, degrees, sin, cos, atan2, sqrt
    
    # Convert to radians
    phi1, lambda1 = radians(lat1), radians(lon1)
    phi2, lambda2 = radians(lat2), radians(lon2)
    
    waypoints = []
    for i in range(n_points + 1):
        f = i / n_points  # Fraction along path
        
        # Spherical interpolation (slerp)
        d = haversine(lat1, lon1, lat2, lon2) / 6371
        a = sin((1 - f) * d) / sin(d)
        b = sin(f * d) / sin(d)
        
        x = a * cos(phi1) * cos(lambda1) + b * cos(phi2) * cos(lambda2)
        y = a * cos(phi1) * sin(lambda1) + b * cos(phi2) * sin(lambda2)
        z = a * sin(phi1) + b * sin(phi2)
        
        lat = degrees(atan2(z, sqrt(x**2 + y**2)))
        lon = degrees(atan2(y, x))
        
        # Color from seed + index
        wp_se