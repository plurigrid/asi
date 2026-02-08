---
name: gay-julia
description: Wide-gamut color sampling with splittable determinism using Pigeons.jl
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Gay.jl - Wide-Gamut Deterministic Color Sampling

Wide-gamut color sampling with splittable determinism using Pigeons.jl SPI pattern and LispSyntax integration.

## bmorphism Contributions

> *"We are building cognitive infrastructure for the next trillion minds"*
> — [Plurigrid: the story thus far](https://gist.github.com/bmorphism/a400e174b9f93db299558a6986be0310)

**Author**: [@bmorphism](https://github.com/bmorphism) (Barton Rhodes)

Gay.jl embodies the Plurigrid principle of **autopoietic ergodicity** — self-sustaining systems that explore all accessible states. The deterministic color generation from seeds mirrors the broader pattern of reproducible, verifiable computation across distributed systems.

**Related bmorphism projects**:
- [bmorphism/slowtime-mcp-server](https://github.com/bmorphism/slowtime-mcp-server) - MCP server for time intervals
- [plurigrid/act](https://github.com/plurigrid/act) - cognitive category theory building blocks
- Parametrised optics for cybernetic systems

## Repository
- **Source**: https://github.com/bmorphism/Gay.jl
- **Author**: [@bmorphism](https://github.com/bmorphism)
- **Language**: Julia
- **Pattern**: SplitMix64 → GF(3) trits → LCH colors

## Core Concepts

### SplitMix64 Determinism
```julia
# Deterministic color from seed
using Gay

seed = 0x598F318E2B9E884
color = gay_color(seed)  # Returns LCH color
trit = gf3_trit(seed)    # Returns :MINUS, :ERGODIC, or :PLUS
```

### GF(3) Conservation
Every color operation preserves the tripartite balance:
- **MINUS** (-1): Contractive operations
- **ERGODIC** (0): Neutral/balanced operations  
- **PLUS** (+1): Expansive operations

Sum of trits across parallel streams must equal 0 (mod 3).

### LispSyntax Integration
```julia
using LispSyntax

# S-expression colorization
sexp = @lisp (defun factorial (n) (if (<= n 1) 1 (* n (factorial (- n 1)))))
colored = colorize(sexp, seed=seed)
```

## Integration with plurigrid/asi

### With gay-mcp skill
```julia
# MCP tool registration w