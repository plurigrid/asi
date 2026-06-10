---
name: siggraph
description: SIGGRAPH is the premier venue for computer graphics research. This skill indexes papers, repos, and techniques from SIGGRAPH 2023-2025.
---
# SIGGRAPH Skill

**Trit**: 0 (ERGODIC/Coordinator)  
**Domain**: computer-graphics, research, rendering, animation, simulation  
**Conference**: ACM SIGGRAPH (Special Interest Group on Computer GRAPHics)

---

## Overview

SIGGRAPH is the premier venue for computer graphics research. This skill indexes papers, repos, and techniques from SIGGRAPH 2023-2025.

```
┌─────────────────────────────────────────────────────────────────────────┐
│                      SIGGRAPH RESEARCH DOMAINS                          │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  ┌────────────┐  │
│  │   RENDERING  │  │  ANIMATION   │  │  GEOMETRY    │  │    AI/ML   │  │
│  │              │  │              │  │              │  │            │  │
│  │ • NeRF       │  │ • Motion     │  │ • Meshes     │  │ • Diffusion│  │
│  │ • Gaussians  │  │ • Rigging    │  │ • B-rep      │  │ • GAN      │  │
│  │ • Ray trace  │  │ • Characters │  │ • Splatting  │  │ • ControlN │  │
│  └──────────────┘  └──────────────┘  └──────────────┘  └────────────┘  │
│                                                                         │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  ┌────────────┐  │
│  │  SIMULATION  │  │   IMAGING    │  │   HUMAN      │  │   ACCEL    │  │
│  │              │  │              │  │              │  │            │  │
│  │ • Physics    │  │ • HDR        │  │ • Faces      │  │ • WebGPU   │  │
│  │ • Fluids     │  │ • Colorize   │  │ • Bodies     │  │ • Neural   │  │
│  │ • MPM        │  │ • Edit       │  │ • Motion cap │  │ • Shaders  │  │
│  └──────────────┘  └──────────────┘  └──────────────┘  └────────────┘  │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## SIGGRAPH 2025 Top Papers

| Repo | ★ | Topic | Description |
|------|---|-------|-------------|
| [VAST-AI-Research/UniRig](https://github.com/VAST-AI-Research/UniRig) | 1274 | Rigging | One Model to Rig Them All |
| [XPixelGroup/HYPIR](https://github.com/XPixelGroup/HYPIR) | 1023 | Restoration | Diffusion Score Priors for Image Restoration |
| [aigc3d/LAM](https://github.com/aigc3d/LAM) | 891 | Avatars | Large Avatar Model for One-shot Gaussian Head |
| [microsoft/renderformer](https://github.com/microsoft/renderformer) | 886 | Rendering | Transformer-based Neural Rendering with GI |
| [IGL-HKUST/DiffusionAsShader](https://github.com/IGL-HKUST/DiffusionAsShader) | 796 | Video | 3D-aware Video Diffusion |
| [NYU-ICL/image-gs](https://github.com/NYU-ICL/image-gs) | 422 | 2D Gaussians | Content-Adaptive Image Representation |
| [PrimitiveAnything](https://github.com/PrimitiveAnything/PrimitiveAnything) | 377 | 3D Gen | Human-Crafted Primitive Assembly |
| [3DTopia/LayerPano3D](https://github.com/3DTopia/LayerPano3D) | 305 | Panorama | Layered 3D Panorama Generation |

---

## SIGGRAPH 2024 Top Papers

| Repo | ★ | Topic | Description |
|------|---|-------|-------------|
| [TencentARC/MotionCtrl](https://github.com/TencentARC/MotionCtrl) | 1478 | Motion | Motion Control for Video Generation |
| [graphdeco-inria/hierarchical-3d-gaussians](https://github.com/graphdeco-inria/hierarchical-3d-gaussians) | 1351 | Gaussians | Hierarchical 3DGS for Large Datasets |
| [hbb1/2d-gaussian-splatting](https://github.com/hbb1/2d-gaussian-splatting) | 2962 | 2DGS | Geometrically Accurate Radiance Fields |
| [bytedance/X-Portrait](https://github.com/bytedance/X-Portrait) | 532 | Portraits | Expressive Portrait Animation |
| [MisEty/RTG-SLAM](https://github.com/MisEty/RTG-SLAM) | 468 | SLAM | Real-time 3D Reconstruction with Gaussians |
| [samxuxiang/BrepGen](https://github.com/samxuxiang/BrepGen) | 378 | CAD | B-rep Generative Diffusion Model |
| [AIGAnimation/CAMDM](https://github.com/AIGAnimation/CAMDM) | 286 | Animation | Taming Diffusion for Character Control |
| [electronicarts/pbmpm](https://github.com/electronicarts/pbmpm) | 232 | Physics | WebGPU Position Based MPM |

---

## SIGGRAPH 2023 Classics

| Repo | ★ | Topic | Description |
|------|---|-------|-------------|
| [XingangPan/DragGAN](https://github.com/XingangPan/DragGAN) | 36005 | GAN | Interactive Point-based Image Manipulation |
| [Doubiiu/ToonCrafter](https://github.com/Doubiiu/ToonCrafter) | 5927 | Animation | Generative Cartoon Interpolation |
| [williamyang1991/Rerender_A_Video](https://github.com/williamyang1991/Rerender_A_Video) | 3004 | Video | Zero-Shot Video-to-Video Translation |
| [pix2pixzero](https://github.com/pix2pixzero/pix2pix-zero) | 1143 | Image | Zero-shot Image-to-Image Translation |

---

## Key Techniques

### Gaussian Splatting

```python
# 3D Gaussian Splatting fundamentals
# Each Gaussian: position (μ), covariance (Σ), color (SH), opacity (α)

class Gaussian3D:
    def __init__(self):
        self.position = np.zeros(3)      # μ ∈ R³
        self.covariance = np.eye(3)      # Σ ∈ R³ˣ³ (positive semi-definite)
        self.sh_coeffs = np.zeros(48)    # Spherical harmonics (RGB × 16)
        self.opacity = 1.0               # α ∈ [0, 1]
    
    def splat(self, camera):
        # Project to 2D, compute screen-space covariance
        μ_2d = camera.project(self.position)
        Σ_2d = camera.project_cov(self.covariance)
        return μ_2d, Σ_2d
```

### Neural Radiance Fields (NeRF)

```python
# NeRF: F(x, d) → (c, σ)
# x = 3D position, d = viewing direction
# c = RGB color, σ = volume density

def nerf_forward(model, rays_o, rays_d, near, far, n_samples):
    t = torch.linspace(near, far, n_samples)
    points = rays_o + t * rays_d
    
    # Query MLP
    rgb, density = model(points, rays_d)
    
    # Volume rendering
    weights = compute_transmittance(density, t)
    color = (weights * rgb).sum(dim=-1)
    return color
```

### Material Point Method (MPM)

```javascript
// WebGPU PB-MPM from EA SIGGRAPH 2024
// Position Based Material Point Method

struct Particle {
    position: vec3<f32>,
    velocity: vec3<f32>,
    mass: f32,
    volume: f32,
    deformation_grad: mat3x3<f32>,
}

@compute @workgroup_size(256)
fn p2g(@builtin(global_invocation_id) id: vec3<u32>) {
    // Particle to Grid transfer
    let p = particles[id.x];
    let base = floor(p.position / dx);
    
    for (var i = 0; i < 27; i++) {
        let offset = neighbor_offsets[i];
        let weight = bspline_weight(p.position, base + offset);
        atomicAdd(&grid[base + offset].mass, p.mass * weight);
        atomicAdd(&grid[base + offset].momentum, p.mass * p.velocity * weight);
    }
}
```

---

## GF(3) Research Classification

```
MINUS (-1): Analysis/Measurement Papers
  - Perceptual studies
  - Benchmarks
  - Quality metrics

ERGODIC (0): Method/Algorithm Papers  
  - Novel techniques
  - Hybrid approaches
  - Framework design

PLUS (+1): Generation/Synthesis Papers
  - Generative models
  - Neural rendering
  - Content creation
```

### Balanced Research Pipeline

```clojure
;; catp verification for research workflow
[:literature-review :method-design :implementation]  ; -1 + 0 + 1 = 0 ✓
[:dataset-creation :training :evaluation]             ; -1 + 0 + 1 = 0 ✓
[:problem-analysis :algorithm :results]               ; -1 + 0 + 1 = 0 ✓
```

---

## Resources

### Official
- **SIGGRAPH 2025**: https://s2025.siggraph.org/
- **Papers Program**: https://s2025.conference-schedule.org/?filter1=sstype101
- **ACM DL**: https://dl.acm.org/doi/proceedings/10.1145/3721238

### Curated Lists
- **Ke-Sen Huang's Papers**: https://www.realtimerendering.com/kesen/sig2025.html
- **Paper Copilot**: https://papercopilot.com/paper-list/siggraph-paper-list/siggraph-2025-paper-list/
- **Paper Digest**: https://www.paperdigest.org/2025/08/siggraph-2025-papers-highlights/

### Statistics (SIGGRAPH 2025)
- **Total Accepted**: 710
- **Technical Papers**: 306
- **TOG Papers**: 24
- **Posters**: 380
- **Location**: Vancouver, Canada

---

## Commands

```bash
# Search SIGGRAPH repos
gh search repos "siggraph 2025" --sort stars --limit 20

# Clone top paper implementations
gh repo clone VAST-AI-Research/UniRig
gh repo clone microsoft/renderformer
gh repo clone hbb1/2d-gaussian-splatting

# Track new SIGGRAPH papers
gh api search/repositories -f q="siggraph 2025" --jq '.items[:10] | .[].full_name'
```

---

## Related Skills

| Skill | Trit | Bridge |
|-------|------|--------|
| `algorithmic-art` | +1 | Procedural generation |
| `gay-mcp` | +1 | Color theory for rendering |
| `xogot` | +1 | Game engine integration |
| `mlx-apple-silicon` | 0 | Neural inference on Metal |
| `iroh-p2p` | +1 | Distributed rendering |

---

## SIGGRAPH Asia

| Year | Location | Notable Papers |
|------|----------|----------------|
| 2024 | Tokyo | ToonCrafter, GVHMR, GaussianObject |
| 2023 | Sydney | EasyVolcap, Rerender_A_Video |
| 2022 | Daegu | VideoReTalking, VToonify |

---

**Skill Name**: siggraph  
**Type**: Research / Computer Graphics  
**Trit**: 0 (ERGODIC)  
**GF(3)**: Coordinator role - bridges analysis and synthesis


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
