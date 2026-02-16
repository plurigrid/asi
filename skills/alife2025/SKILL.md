---
name: alife2025
description: ALIFE 2025 Proceedings - 337 pages, 80+ papers on artificial life, evolution, emergence, cellular automata, neural networks, agent-based models. Full Mathpix extraction with equations and figures.
---

# ALIFE 2025 Proceedings Skill

**Status**: ✅ Production Ready (Mathpix extracted)
**Trit**: +1 (PLUS - generative/creative)
**Pages**: 337 | **Papers**: 80+ | **Figures**: 153 | **Equations**: 100+

## Paper Index (Selected)

| Page | Title | Theme |
|------|-------|-------|
| 1 | Chemical Computer (BZ oscillators) | Chemical Computing |
| 5 | Institution Bootstrapping Problem | Social Simulation |
| 9 | Mapping Road to Synthetic Ecosystems | Ecosystems |
| 13 | Structural Cellular Hash Chemistry | Cellular Automata |
| 17 | Evolutionary Advantage of Guilt | Evolution |
| 25 | Stable Scalable Boid Patterns | Swarm Intelligence |
| 37 | BUNCH: Hierarchical Filtering | Emergence Detection |
| 49 | Hummingbird Kernel: Chaotic LV Sampling | Optimization |
| 57 | Predictive-Coding Variational RNN | Free Energy Principle |
| 61 | Neural Cellular Automata Dynamics | NCA |
| 69 | Population of Thoughts: Open-Ended Evolution | LLM + Evolution |
| 73 | Neural Cellular Automata: Cells to Pixels | NCA |
| 77 | Petri Dish NCA | NCA |
| 99 | Language Cellular Automata | NCA + NLP |
| 103 | Lenia Parameter Space | Continuous CA |
| 107 | Evolvable Chemotons | Autopoiesis |
| 111 | Category Theory for Life | Category Theory |
| 115 | Evolving Interaction Protocols | Open-Ended Evolution |
| 127 | Swarm2Algo: Emergent → Distributed Algorithms | Swarm |
| 135 | Open-Ended Evolution in Binary CA | Emergence |
| 139 | Spark: Modular Spiking Neural Networks | Neural |
| 151 | Non-Equilibrium Memories with NCA | NCA |
| 163 | Temporal Memory in Swarm Reservoir | Reservoir Computing |
| 173 | H-Lenia: Hierarchical Lenia | Continuous CA |
| 177 | Emergent Patterns in Galactic Systems | Cosmology + ALife |
| 195 | Neural Particle Automata | Particles |
| 207 | Oscillatory Dynamics for Computation | Analog Computing |
| 219 | Functional Information Decomposition | Information Theory |
| 227 | Particle Life in Sierpinski Gasket | Fractals |
| 231 | Meta-Neural Cellular Automata | Meta-learning |
| 251 | Autotelic RL for Cellular Automata | RL + CA |
| 255 | Developmental Pattern Formation | Morphogenesis |
| 267 | Adversarial Environment for NCA | Adversarial |
| 275 | Growing Neural Cellular Automata | Developmental |
| 283 | Self-Organising Digital Circuits | Digital Morphogenesis |
| 287 | Scaffolding via Morphogenetic Gradients | Development |
| 295 | Swarm Size Estimation via Diffusion | Swarm |
| 301 | Gridarians: LLM-Driven ALife | LLM + ALife |
| 309 | UIUA: Array Language for ALife | Programming Languages |

## Key Equations

### Boid Flocking (Separation/Alignment/Cohesion)
```latex
\sum_{j} w_s(T_i, T_j) \frac{\vec{\xi}_{i,j}(t)}{|\vec{\xi}_{i,j}(t)|} + 
\sum_{j} w_a(T_i, T_j) \frac{\vec{v}_j(t) - \vec{v}_i(t)}{N_{a,i}} + 
\sum_{j} w_c(T_i, T_j) \frac{-\vec{\xi}_{i,j}(t)}{N_{c,i}}
```

### Lotka-Volterra Dynamics (Chaotic Sampling)
```latex
\frac{dx_i}{dt} = x_i\left(r_i + \sum_{j=1}^{4} A_{ij} x_j\right)
```

### Free Energy Minimization
```latex
\mathcal{F} = \underbrace{\sum_{t=1}^{T}\left[\sum_{l}^{L} \frac{\mathbf{w}^l}{R_z^l} \delta(l, r, t)\right]}_{\text{complexity}} - \underbrace{\frac{1}{R_X}\left[\sum_{t=1}^{T}\|\mathbf{X}_t - \overline{\mathbf{X}}_t\|_2^2\right]}_{\text{accuracy}}
```

### H-Lenia Hierarchical Update
```latex
\left[\left[A_i^t + \Delta t G(K * A_i^t)\right]_0^1 + \sum_{j \in N(i)} k_{ji} \cdot E_{ji}^t(\Delta_{j \rightarrow i}^t)\right]_0^1
```

### Lenia Growth Function
```latex
G_{\mu,\sigma}(x) = 2e^{-\frac{(x-\mu)^2}{2\sigma^2}} - 1
```

### Neural Particle Automata
```latex
[\Delta x_i, \Delta S_i] = f_\theta(S_i, \tilde{S}_i, \nabla S_i, \nabla \rho_i)
```

### Restricted Boolean Network
```latex
f_i = \left(\sum_j w_{ij} \cdot x_j\right) > 0
```

### Reaction-Diffusion Laplacian
```latex
\nabla^2 Y_i \approx \frac{\sum_j Y_j - Y_i}{\Delta x} \propto J_{Y_{nb}}^Y - J_Y^Y
```

### Information Synergy
```latex
I_{\text{syn}}(X \rightarrow Y) = I_{\text{tot}} - \sum_{i=1}^{n} I_{\text{ind}}(X_i)
```

## Research Themes

### 1. Neural Cellular Automata (NCA)
- From Cells to Pixels (Pajouheshgar et al.)
- Petri Dish NCA (Zhang, Risi, Darlow)
- Language Cellular Automata (Najarro et al.)
- Growing NCA (Sato, Masumori, Ikegami)
- Meta-NCA with Linear Attention

### 2. Lenia & Continuous CA
- Visualizing Lenia Parameter Space
- H-Lenia: Hierarchical Extension
- Glider Equation for Asymptotic Lenia

### 3. Evolution & Open-Endedness
- Open-Ended Evolution in Binary CA
- Evolvable Chemotons
- Population of Thoughts (LLM + Evolution)
- Attack of the Clones (Diversity in GP)

### 4. Chemical Computing
- BZ Oscillator Reservoir Computing
- Chemical Computer Construction
- Environmentally Driven Autocatalysis

### 5. Swarm Intelligence
- Swarm2Algo: Emergent → Algorithms
- Pheromone-mediated Ant Movement
- Swarm Size Estimation
- Temporal Memory in Swarm Reservoir

### 6. LLM + ALife
- Gridarians: LLM-Driven ALife
- LLM-Driven Social Behaviors
- Strategy Extraction via LLM Annotation
- Internalized Culture in LLM Societies

### 7. Category Theory & Formal Methods
- Integrative Formulation via Category Theory
- Functional Information Decomposition
- UIUA Array Language for ALife

## Extracted Resources

```
/Users/bob/ies/paper_extracts/alife2025/
├── ALIFE2025_full.md          # 925KB markdown
├── ALIFE2025_tex.zip          # 11MB LaTeX + images
├── tex_extracted/
│   └── fed660c6-.../
│       ├── *.tex              # 7283 lines LaTeX
│       └── images/            # 153 figures
└── conversion_status.json
```

## Integration with Gay.jl

```julia
using Gay

# Assign deterministic colors to papers
function paper_color(title::String)
    seed = UInt64(0x414C494645)  # "ALIFE"
    Gay.color_at(hash(title) ⊻ seed, 1)
end

# GF(3) theme classification
THEMES = Dict(
    :nca => -1,        # MINUS: Structure-preserving
    :evolution => 0,   # ERGODIC: Process
    :emergence => +1   # PLUS: Novel patterns
)
```

## Commands

```bash
just alife-toc              # Show table of contents
just alife-paper 42         # Get paper at page 42
just alife-equation "lenia" # Find Lenia equations
just alife-figure 15        # Get figure by number
just alife-theme "nca"      # List NCA papers
```

## See Also

- `acsets-algebraic-databases` - Model ALife structures categorically
- `gay-mcp` - Deterministic coloring for visualization
- `hatchery-papers` - Academic paper patterns
- `glass-bead-game` - Interdisciplinary connections

## Citation

```bibtex
@proceedings{alife2025,
  title     = {Companion Proceedings of the Artificial Life Conference 2025},
  booktitle = {ALIFE 25: Ciphers of Life},
  editor    = {Witkowski, Olaf and Adams, Alyssa M. and Sinapayen, Lana and 
               Baltieri, Manuel and Khosravy, Mahdi},
  year      = {2025},
  pages     = {337}
}
```

---

**Extraction**: Mathpix PDF ID `fed660c6-4d3d-4bb6-bb3c-f9b039187660`
**Source**: `/Users/bob/Downloads/ALIFE2025ProceedingsCompanion (1).pdf`
