# Integration Guide: Low-Discrepancy Sequences with Gay-MCP

This guide shows how to integrate the new low-discrepancy sequences with the existing `gay-mcp` MCP server tools.

## Current Gay-MCP Tools

The existing gay-mcp MCP server provides:
- `gay_seed`: Set global RNG seed
- `gay_seed_from_drand`: Set seed from drand beacon
- `color_at`: Get color at specific index
- `palette`: Generate N colors
- `next_color`: Get next color from stream
- `golden_thread`: Golden angle spiral (φ)
- `interleave`: Interleaved streams for checkerboard
- `reafference`: Self-recognition via prediction matching
- And many more specialized tools

## New Tools to Add

The low-discrepancy sequences skill adds the following new capabilities that should be exposed as MCP tools:

### 1. Plastic Thread (2D)

```typescript
{
  name: "gay_plastic_thread",
  description: "Generate colors using plastic constant φ₂ for optimal 2D coverage (hue + saturation)",
  inputSchema: {
    type: "object",
    properties: {
      steps: { type: "number", description: "Number of colors to generate" },
      seed: { type: "number", description: "Optional seed (uses global if not provided)" },
      lightness: { type: "number", description: "Lightness 0-1 (default: 0.5)" }
    },
    required: ["steps"]
  }
}
```

**Implementation**:
```julia
function handle_plastic_thread(steps, seed=nothing, lightness=0.5)
    s = isnothing(seed) ? get_global_seed() : seed
    colors = [plastic_color(i, seed=s, lightness=lightness) for i in 1:steps]
    return Dict(
        "colors" => [color_to_hex(c) for c in colors],
        "method" => "plastic",
        "seed" => s,
        "phi2" => φ₂
    )
end
```

### 2. Halton Colors

```typescript
{
  name: "gay_halton",
  description: "Generate colors using Halton sequence with prime bases for nD uniformity",
  inputSchema: {
    type: "object",
    properties: {
      count: { type: "number", description: "Number of colors to generate" },
      bases: { type: "array", items: { type: "number" }, description: "Prime bases (default: [2,3,5])" },
      mode: { type: "string", enum: ["rgb", "hsl"], description: "Color space (default: hsl)" }
    },
    required: ["count"]
  }
}
```

**Implementation**:
```julia
function handle_halton(count, bases=[2,3,5], mode="hsl")
    colors = if mode == "rgb"
        [halton_color(i, bases=bases) for i in 1:count]
    else
        [halton_hsl_color(i, bases=bases) for i in 1:count]
    end
    
    return Dict(
        "colors" => [color_to_hex(c) for c in colors],
        "method" => "halton",
        "bases" => bases,
        "mode" => mode
    )
end
```

### 3. R-Sequence

```typescript
{
  name: "gay_r_sequence",
  description: "Generate colors using R-sequence (d-dimensional golden ratios) for nD coverage",
  inputSchema: {
    type: "object",
    properties: {
      count: { type: "number", description: "Number of colors to generate" },
      dim: { type: "number", description: "Dimension (2=plastic, 3=phi3, default: 3)" },
      seed: { type: "number", description: "Optional seed (uses global if not provided)" }
    },
    required: ["count"]
  }
}
```

**Implementation**:
```julia
function handle_r_sequence(count, dim=3, seed=nothing)
    s = isnothing(seed) ? get_global_seed() : seed
    φ_d = r_sequence_root(dim)
    colors = [r_sequence_color(i, dim=dim, seed=s) for i in 1:count]
    
    return Dict(
        "colors" => [color_to_hex(c) for c in colors],
        "method" => "r_sequence",
        "dimension" => dim,
        "phi_d" => φ_d,
        "seed" => s
    )
end
```

### 4. Kronecker Sequence

```typescript
{
  name: "gay_kronecker",
  description: "Generate colors using Kronecker sequence {nα} mod 1 for equidistribution",
  inputSchema: {
    type: "object",
    properties: {
      count: { type: "number", description: "Number of colors to generate" },
      alpha: { type: "number", description: "Irrational α (default: √2)" },
      seed: { type: "number", description: "Optional seed" },
      saturation: { type: "number", description: "Saturation 0-1 (default: 0.7)" },
      lightness: { type: "number", description: "Lightness 0-1 (default: 0.55)" }
    },
    required: ["count"]
  }
}
```

### 5. Sobol Sequence

```typescript
{
  name: "gay_sobol",
  description: "Generate colors using Sobol sequence for excellent high-dimensional uniformity",
  inputSchema: {
    type: "object",
    properties: {
      count: { type: "number", description: "Number of colors to generate" },
      mode: { type: "string", enum: ["rgb", "hsl"], description: "Color space (default: hsl)" }
    },
    required: ["count"]
  }
}
```

### 6. Continued Fractions

```typescript
{
  name: "gay_continued_fraction",
  description: "Generate colors using continued fraction convergents (geodesic in hyperbolic geometry)",
  inputSchema: {
    type: "object",
    properties: {
      count: { type: "number", description: "Number of colors to generate" },
      cf_type: { type: "string", enum: ["golden", "sqrt2", "e"], description: "CF type (default: golden)" },
      seed: { type: "number", description: "Optional seed" },
      saturation: { type: "number", description: "Saturation 0-1 (default: 0.7)" },
      lightness: { type: "number", description: "Lightness 0-1 (default: 0.55)" }
    },
    required: ["count"]
  }
}
```

### 7. Invert Color (Bijection)

```typescript
{
  name: "gay_invert",
  description: "Recover index n from color (bijection property). Given (color, seed, method) → n",
  inputSchema: {
    type: "object",
    properties: {
      hex: { type: "string", description: "Hex color to invert (e.g., '#A855F7')" },
      method: { 
        type: "string", 
        enum: ["golden", "plastic", "halton", "r_sequence", "kronecker", "sobol", "pisot", "cf"],
        description: "Generation method used"
      },
      seed: { type: "number", description: "Seed used for generation" },
      max_search: { type: "number", description: "Max index to search (default: 10000)" },
      // Method-specific parameters
      dim: { type: "number", description: "For r_sequence: dimension" },
      bases: { type: "array", items: { type: "number" }, description: "For halton: prime bases" },
      alpha: { type: "number", description: "For kronecker: irrational α" },
      cf_type: { type: "string", description: "For cf: continued fraction type" }
    },
    required: ["hex", "method"]
  }
}
```

**Implementation**:
```julia
function handle_invert(hex, method, seed=nothing; kwargs...)
    s = isnothing(seed) ? get_global_seed() : seed
    color = hex_to_rgb(hex)
    
    n = invert_color(color, Symbol(method); seed=s, kwargs...)
    
    if isnothing(n)
        return Dict(
            "found" => false,
            "message" => "Index not found within search range",
            "hex" => hex,
            "method" => method,
            "seed" => s
        )
    else
        # Verify by regenerating
        verification = generate_color(n, method, s; kwargs...)
        
        return Dict(
            "found" => true,
            "index" => n,
            "hex" => hex,
            "method" => method,
            "seed" => s,
            "verification" => color_to_hex(verification),
            "distance" => color_distance(color, verification)
        )
    end
end
```

### 8. Compare Sequences

```typescript
{
  name: "gay_compare_sequences",
  description: "Compare uniformity (discrepancy) of different low-discrepancy sequences",
  inputSchema: {
    type: "object",
    properties: {
      n: { type: "number", description: "Number of points to generate for comparison (default: 1000)" },
      sequences: { 
        type: "array", 
        items: { type: "string" },
        description: "Sequences to compare (default: all)"
      }
    },
    required: []
  }
}
```

**Returns**:
```json
{
  "n": 1000,
  "discrepancy": {
    "golden": 0.012,
    "plastic": 0.010,
    "halton": 0.008,
    "kronecker": 0.013,
    "sobol": 0.006
  },
  "ranking": ["sobol", "halton", "plastic", "golden", "kronecker"],
  "note": "Lower discrepancy = more uniform distribution"
}
```

## Reafference Integration

The bijection property enables enhanced reafference capabilities:

### Enhanced Reafference

```typescript
{
  name: "gay_reafference_lds",
  description: "Self-recognition via low-discrepancy sequence prediction matching",
  inputSchema: {
    type: "object",
    properties: {
      seed: { type: "number", description: "Your identity seed" },
      index: { type: "number", description: "The index you're checking" },
      observed_hex: { type: "string", description: "The hex color you observed" },
      method: { type: "string", description: "Generation method (golden/plastic/halton/...)" }
    },
    required: ["seed", "index", "observed_hex", "method"]
  }
}
```

**Implementation**:
```julia
function handle_reafference_lds(seed, index, observed_hex, method)
    # Generate efference copy (prediction)
    predicted = generate_color(index, method, seed)
    predicted_hex = color_to_hex(predicted)
    
    # Observe
    observed = hex_to_rgb(observed_hex)
    
    # Match?
    distance = color_distance(predicted, observed)
    is_self = distance < 0.01
    
    return Dict(
        "is_self" => is_self,
        "seed" => seed,
        "index" => index,
        "method" => method,
        "predicted" => predicted_hex,
        "observed" => observed_hex,
        "distance" => distance,
        "message" => is_self ? 
            "Reafference: I generated this color (self)" : 
            "Exafference: This color came from elsewhere (other)"
    )
end
```

## Usage Examples

### Generate Plastic Thread

```bash
# Via MCP tool
gay_plastic_thread --steps 10 --seed 42

# Returns:
{
  "colors": ["#A855F7", "#3B82F6", ...],
  "method": "plastic",
  "seed": 42,
  "phi2": 1.3247179572447460
}
```

### Invert Color

```bash
# Via MCP tool
gay_invert --hex "#A855F7" --method plastic --seed 42

# Returns:
{
  "found": true,
  "index": 69,
  "hex": "#A855F7",
  "method": "plastic",
  "seed": 42,
  "verification": "#A855F7",
  "distance": 0.0001
}
```

### Compare Sequences

```bash
# Via MCP tool
gay_compare_sequences --n 1000

# Returns ranking by uniformity
{
  "discrepancy": {
    "sobol": 0.006,    # Best
    "halton": 0.008,
    "plastic": 0.010,
    "golden": 0.012,
    "kronecker": 0.013
  }
}
```

## Integration Steps

1. **Add LowDiscrepancySequences.jl module** to gay-mcp server dependencies
2. **Register new MCP tools** in server tool list
3. **Add helper functions** for color conversion (hex_to_rgb, color_to_hex, color_distance)
4. **Extend global seed** to work with all sequences
5. **Update documentation** with new tool descriptions
6. **Add tests** for bijection property verification

## Compatibility

All new tools are **backwards compatible** with existing gay-mcp tools:
- Same seed system (global + local override)
- Same color format (hex strings)
- Same response structure (JSON with metadata)
- Extends existing capabilities without breaking changes

## Performance Notes

- **Inversion** is O(n) linear search by default; can optimize with binary search for monotonic sequences
- **Sobol** direction numbers could be precomputed for better performance
- **Continued fractions** grow slowly; use caching for large k
- **Halton** is fastest for direct generation
- **Plastic/Golden** are simplest (single division per coordinate)

## Future Enhancements

1. **Precomputed tables** for Sobol direction numbers (Joe & Kuo 2008 dataset)
2. **Binary search inversion** for monotonic sequences (golden, plastic, kronecker)
3. **Multi-dimensional visualization** showing coverage patterns
4. **Discrepancy plots** comparing sequence uniformity over time
5. **Integration with awareness graph** using plastic constant for node colors
