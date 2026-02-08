# Möbius Path Filter

**Category**: Theorem Dependency Analysis
**Type**: Graph Path Classification
**Language**: Julia
**Status**: Production Ready
**Version**: 1.0.0
**Date**: December 22, 2025

## Overview

Identifies tangled geodesics in proof dependency graphs via Möbius inversion. Classifies paths by prime factorization to determine which dependencies are problematic (create cycles) vs. optimal (linear chains).

## Key Functions

- **`enumerate_paths(adjacency)`**: Discovers all paths in graph
- **`factor_number(n)`**: Prime factorization for Möbius weights
- **`mobius_weight(n)`**: Computes μ(n) ∈ {-1, 0, +1}
- **`filter_tangled_paths(adjacency)`**: Identifies problem paths
- **`generate_filter_report()`**: Human-readable analysis

## Mathematical Foundation

**Möbius Inversion for Path Classification**
```
μ(n) = +1   : prime paths (keep - linear chains)
μ(n) = -1   : odd-composite paths (rewrite needed)
μ(n) = 0    : squared-factors (remove - redundant)
```

Uses prime factorization to weight geodesic paths in dependency graph. Helps identify which theorems create circular dependencies that impede spectral gap.

## Usage

```julia
using MobiusFilter

# Analyze proof dependencies
prime_paths, tangled = filter_tangled_paths(adjacency)

# Get recommendations
report = generate_filter_report(adjacency)
println(report)
```

## Integration Points

- Diagnosis tool for Week 2 analysis phase
- Feeds into safe_rewriting_advisor for remediation
- Used by continuous-inverter for automated detection

## Performance

- Execution time: ~1 second (for 5-node test graphs)
- Path enumeration: Exponential but capped by practical graph size
- Prime factorization: O(√n) per path

## References

- Hardy & Wright (1979): Elementary Number Theory
- Möbius inversion theory for discrete mathematics
