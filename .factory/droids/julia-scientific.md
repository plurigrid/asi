---
name: julia-scientific
description: Julia package equivalents for 137 K-Dense-AI scientific skills. Maps Python bioinformatics, chemistry, ML, quantum, and data science packages to native Julia ecosystem.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Julia Scientific Package Mapping Skill

> *"Two languages diverged in a scientific wood, and Julia—Julia took the one with multiple dispatch."*

## bmorphism Contributions

> *"We are building cognitive infrastructure for the next trillion minds"*
> — [Plurigrid: the story thus far](https://gist.github.com/bmorphism/a400e174b9f93db299558a6986be0310)

> *"complexity of information / the burden of integrating it in real time makes technology an indispensable part of our cognitive infrastructure"*
> — [@bmorphism](https://github.com/bmorphism)

**Key References from Plurigrid**:
- [Towards Foundations of Categorical Cybernetics](https://arxiv.org/abs/2105.06332)
- [Organizing Physics with Open Energy-Driven Systems](https://arxiv.org/abs/2404.16140)
- [Compositional game theory](https://arxiv.org/abs/1603.04641)

## Overview

This skill provides comprehensive mappings from **137 K-Dense-AI Python scientific skills** to their **Julia package equivalents**. Coverage is ~85% native Julia, with the remainder accessible via PyCall.jl interop.

## Quick Reference

| Category | Skills | Coverage | Key Packages |
|----------|--------|----------|--------------|
| Bioinformatics | 25 | 92% | BioJulia ecosystem |
| Chemistry | 17 | 85% | JuliaMolSim, Chemellia |
| Quantum | 4 | 100% | Yao.jl, QuantumToolbox.jl |
| ML/AI | 10 | 95% | Flux.jl, MLJ.jl, Lux.jl |
| Data/Stats | 11 | 100% | DataFrames.jl, Turing.jl |
| Visualization | 6 | 100% | Makie.jl, Plots.jl |
| Physics/Astro | 6 | 90% | JuliaAstro ecosystem |
| Clinical/DB | 13 | 60% | JuliaHealth, HTTP.jl |
| Symbolic/Geo | 3 | 100% | Symbolics.jl, GeoDataFrames.jl |
| Lab Automation | 8 | 50% | DrWatson.jl, Dagger.jl |
| Documents | 5 | 80% | PDFIO.jl, Weave.jl |

## GF(3) Conservation

Julia scientific triads maintain balance:

```
bioinformatics (-1) ⊗ visualization (0) ⊗ quantum (+1) = 0 ✓
chemistry (-1) ⊗ data-science (0) ⊗ ml-ai (+1) = 0 ✓
physics (-1) ⊗ symbolic (0) ⊗ clinical (+1) = 0 ✓
```

## Core Mappings

### Bioi