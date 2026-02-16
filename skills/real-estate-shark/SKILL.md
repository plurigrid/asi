# Real Estate Shark

**Trit**: MINUS (-1) — Validation/Analysis  
**Color**: `#DA9E5A`  
**URI**: `skill://real-estate-shark#DA9E5A`

## Purpose

Transform single property/neighborhood images into photorealistic 3D Gaussian Splats using Apple's ml-sharp, enabling virtual walkthroughs from a single photograph. Bridge to PropertyPriceOracle for valuation analytics.

## When to Use

- Converting property listing photos to 3D walkthroughs
- Neighborhood visualization from street-level imagery
- Real estate due diligence with 3D spatial analysis
- Virtual staging and property tours from single images

## Dependencies

- `apple/ml-sharp` — SHARP monocular view synthesis
- `PropertyPriceOracle` — Addictive market dynamics valuation
- Gay.jl GF(3) coloring for property classification

## Quick Start

```bash
# Activate ml-sharp environment
cd ~/ies/ml-sharp && source .venv/bin/activate

# Single image → 3D Gaussian Splat (<1 second on GPU)
sharp predict -i property_photo.jpg -o splats/ --device mps

# With video rendering (CUDA only)
sharp predict -i photos/ -o splats/ --render --device cuda

# Render from existing splats
sharp render -i splats/ -o videos/
```

## Architecture

```
┌─────────────────┐     ┌──────────────────┐     ┌─────────────────┐
│  Property Image │────▶│  SHARP (ml-sharp)│────▶│  3DGS .ply file │
│  (single photo) │     │  ViT + SPN + UNet│     │  (63MB splat)   │
└─────────────────┘     └──────────────────┘     └────────┬────────┘
                                                          │
                        ┌──────────────────┐              │
                        │ PropertyPriceOracle│◀────────────┘
                        │ • get_price()     │     Spatial analysis
                        │ • get_volatility()│     informs valuation
                        │ • get_sentiment() │
                        └──────────────────┘
```

## GF(3) Balanced Triad

| Skill | Trit | Role |
|-------|------|------|
| `real-estate-shark` | -1 | Validation: 3D reconstruction quality |
| `map-projection` | 0 | Coordination: Geo-spatial transforms |
| `addictive-market` | +1 | Generation: Price dynamics |
| **Sum** | **0** | ✓ Conserved |

## Output Format

SHARP produces 3DGS `.ply` files compatible with:
- [gsplat](https://github.com/nerfstudio-project/gsplat) renderers
- Standard 3DGS viewers
- OpenCV coordinate convention (x right, y down, z forward)

## Performance

| Metric | Value |
|--------|-------|
| Inference time | <1 second (GPU) |
| Output size | ~63MB per splat |
| LPIPS improvement | 25-34% vs prior SOTA |
| DISTS improvement | 21-43% vs prior SOTA |

## Example: Neighborhood Batch Processing

```python
from pathlib import Path
import subprocess

def shark_neighborhood(image_dir: Path, output_dir: Path, device: str = "mps"):
    """Convert neighborhood photos to 3D splats."""
    cmd = [
        "sharp", "predict",
        "-i", str(image_dir),
        "-o", str(output_dir),
        "--device", device
    ]
    subprocess.run(cmd, check=True)
    return list(output_dir.glob("*.ply"))

# Usage
splats = shark_neighborhood(
    Path("~/listings/123_main_st/photos"),
    Path("~/listings/123_main_st/splats")
)
print(f"Generated {len(splats)} 3D property splats")
```

## Integration with PropertyPriceOracle

```python
from addictive_market_dynamics import PropertyPriceOracle

# Initialize oracle with base property values
oracle = PropertyPriceOracle({
    1: 450_000,  # 123 Main St
    2: 525_000,  # 456 Oak Ave
    3: 380_000,  # 789 Pine Rd
})

# Get current valuation with market dynamics
for prop_id in [1, 2, 3]:
    price = oracle.get_price(prop_id)
    vol = oracle.get_volatility(prop_id)
    sentiment = oracle.get_sentiment(prop_id)
    cascade = oracle.get_cascade_state(prop_id)
    
    print(f"Property {prop_id}: ${price:,.0f} (vol={vol:.2%}, {cascade})")
```

## References

- [Apple ml-sharp](https://github.com/apple/ml-sharp)
- [arXiv:2512.10685](https://arxiv.org/abs/2512.10685) — Sharp Monocular View Synthesis
- [Project Page](https://apple.github.io/ml-sharp/)
