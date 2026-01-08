# Deployment Guide: Low-Discrepancy Sequences MCP Tools

This guide explains how to integrate the new low-discrepancy sequence tools into the gay-mcp MCP server.

## Implementation Files Created

1. **mcp_integration.jl** - Julia implementation layer with 10 new MCP tools
2. **Project.toml** - Julia dependencies specification

## New MCP Tools

### 1. gay_plastic_thread
Generate colors using plastic constant (φ₂) for 2D hue-saturation coverage.

**Input Schema:**
```typescript
{
  steps: number,      // Number of colors to generate
  seed?: number,      // Optional seed (uses global if not provided)
  lightness?: number  // Lightness 0-1 (default: 0.5)
}
```

**Example:**
```bash
# Via MCP
gay_plastic_thread --steps 10 --seed 42
```

**Output:**
```json
{
  "colors": ["#A855F7", "#3B82F6", ...],
  "method": "plastic",
  "seed": 42,
  "steps": 10,
  "phi2": 1.3247179572447460,
  "dimension": 2,
  "uniformity": "optimal_2d"
}
```

### 2. gay_halton
Generate colors using Halton sequence with prime bases.

**Input Schema:**
```typescript
{
  count: number,
  bases?: [number, number, number],  // Default: [2,3,5]
  mode?: "rgb" | "hsl"                // Default: "hsl"
}
```

### 3. gay_r_sequence
Generate colors using R-sequence (d-dimensional golden ratios).

**Input Schema:**
```typescript
{
  count: number,
  dim?: number,    // Dimension (default: 3)
  seed?: number
}
```

### 4. gay_kronecker
Generate colors using Kronecker sequence for equidistribution.

**Input Schema:**
```typescript
{
  count: number,
  alpha?: number,      // Irrational α (default: √2)
  seed?: number,
  saturation?: number,
  lightness?: number
}
```

### 5. gay_sobol
Generate colors using Sobol sequence for high-dimensional uniformity.

**Input Schema:**
```typescript
{
  count: number,
  mode?: "rgb" | "hsl"  // Default: "hsl"
}
```

### 6. gay_pisot
Generate colors using Pisot sequence (quasiperiodic).

**Input Schema:**
```typescript
{
  count: number,
  theta?: number,      // Pisot number (default: φ)
  seed?: number,
  saturation?: number,
  lightness?: number
}
```

### 7. gay_continued_fraction
Generate colors using continued fraction convergents.

**Input Schema:**
```typescript
{
  count: number,
  cf_type?: "golden" | "sqrt2" | "e",  // Default: "golden"
  seed?: number,
  saturation?: number,
  lightness?: number
}
```

### 8. gay_invert
Recover index from color (bijection property).

**Input Schema:**
```typescript
{
  hex: string,           // Hex color (e.g., "#A855F7")
  method: string,        // Method: "golden", "plastic", "halton", etc.
  seed?: number,
  max_search?: number,   // Default: 10000
  // Method-specific params:
  dim?: number,          // For r_sequence
  bases?: number[],      // For halton
  alpha?: number,        // For kronecker
  cf_type?: string       // For continued_fraction
}
```

**Example:**
```bash
gay_invert --hex "#A855F7" --method plastic --seed 42
```

**Output:**
```json
{
  "found": true,
  "index": 69,
  "hex": "#A855F7",
  "method": "plastic",
  "seed": 42,
  "verification": "#A855F7",
  "distance": 0.0001,
  "bijection": "verified",
  "message": "Successfully recovered index from color"
}
```

### 9. gay_compare_sequences
Compare uniformity of different sequences.

**Input Schema:**
```typescript
{
  n?: number,           // Number of points (default: 1000)
  sequences?: string[]  // Sequences to compare (default: all)
}
```

**Output:**
```json
{
  "n": 1000,
  "discrepancy": {
    "sobol": 0.006,
    "halton": 0.008,
    "plastic": 0.010,
    "golden": 0.012,
    "kronecker": 0.013
  },
  "ranking": ["sobol", "halton", "plastic", "golden", "kronecker"],
  "best": "sobol",
  "worst": "kronecker",
  "note": "Lower discrepancy = more uniform distribution"
}
```

### 10. gay_reafference_lds
Self-recognition via color prediction matching.

**Input Schema:**
```typescript
{
  seed: number,
  index: number,
  observed_hex: string,
  method: string,
  // Method-specific params
}
```

**Output:**
```json
{
  "is_self": true,
  "seed": 42,
  "index": 69,
  "method": "plastic",
  "predicted": "#A855F7",
  "observed": "#A855F7",
  "distance": 0.0001,
  "classification": "reafference",
  "message": "Reafference: I generated this color (self-caused)"
}
```

## Installation Steps

### Option 1: Standalone Julia Server

1. **Install Julia dependencies:**
```bash
cd /Users/bob/i/asi/skills/low-discrepancy-sequences
julia --project=. -e 'using Pkg; Pkg.instantiate()'
```

2. **Test the implementation:**
```bash
julia mcp_integration.jl gay_plastic_thread '{"steps": 5, "seed": 42}'
```

3. **Run as JSON-RPC server:**
Create a wrapper script that reads JSON-RPC requests from stdin and calls `handle_mcp_request()`.

### Option 2: Integrate with Existing Gay-MCP Server

The gay-mcp server is likely implemented in TypeScript/Node.js. To integrate:

1. **Bridge via child process:**
```typescript
import { spawn } from 'child_process';

async function callJuliaTool(tool: string, params: any) {
  return new Promise((resolve, reject) => {
    const julia = spawn('julia', [
      'mcp_integration.jl',
      tool,
      JSON.stringify(params)
    ], {
      cwd: '/Users/bob/i/asi/skills/low-discrepancy-sequences'
    });
    
    let output = '';
    julia.stdout.on('data', (data) => output += data);
    julia.on('close', (code) => {
      if (code === 0) {
        resolve(JSON.parse(output));
      } else {
        reject(new Error(`Julia process exited with code ${code}`));
      }
    });
  });
}

// Register MCP tools
server.tool('gay_plastic_thread', async (params) => {
  return await callJuliaTool('gay_plastic_thread', params);
});

server.tool('gay_halton', async (params) => {
  return await callJuliaTool('gay_halton', params);
});

// ... register remaining 8 tools
```

2. **Register tool schemas:**
Add the tool definitions to the gay-mcp server's tool list with proper TypeScript schemas.

### Option 3: Native TypeScript Implementation

Alternatively, port the Julia implementation to TypeScript/JavaScript for direct integration.

## Testing

### Test Individual Tools

```bash
# Test plastic thread
julia mcp_integration.jl gay_plastic_thread '{"steps": 5, "seed": 42}'

# Test Halton
julia mcp_integration.jl gay_halton '{"count": 5, "bases": [2,3,5]}'

# Test R-sequence
julia mcp_integration.jl gay_r_sequence '{"count": 5, "dim": 3, "seed": 42}'

# Test inversion
julia mcp_integration.jl gay_invert '{"hex": "#A855F7", "method": "plastic", "seed": 42}'

# Test comparison
julia mcp_integration.jl gay_compare_sequences '{"n": 1000}'

# Test reafference
julia mcp_integration.jl gay_reafference_lds '{"seed": 42, "index": 69, "observed_hex": "#A855F7", "method": "plastic"}'
```

### Integration Test

```bash
# Run all examples
julia examples.jl

# Run test suite
julia test_low_discrepancy.jl
```

## Performance Considerations

- **Cold start**: First Julia invocation takes ~2s due to compilation
- **Warm performance**: Subsequent calls are fast (<100ms)
- **Optimization**: Consider using Julia daemon (DaemonMode.jl) for persistent process

### Using DaemonMode for Performance

```bash
# Install DaemonMode
julia -e 'using Pkg; Pkg.add("DaemonMode")'

# Start daemon
julia -e 'using DaemonMode; serve()' &

# Call via daemon (no startup overhead)
julia --startup-file=no -e 'using DaemonMode; runargs()' mcp_integration.jl gay_plastic_thread '{"steps": 5}'
```

## File Structure

```
skills/low-discrepancy-sequences/
├── LowDiscrepancySequences.jl      # Core implementation
├── mcp_integration.jl              # MCP tool wrappers
├── Project.toml                    # Julia dependencies
├── INTEGRATION_GUIDE.md            # Tool specifications
├── DEPLOYMENT.md                   # This file
├── examples.jl                     # Visual examples
├── test_low_discrepancy.jl         # Test suite
├── README.md                       # Comprehensive docs
└── SKILL.md                        # Skill definition
```

## Environment Setup

### Required Packages

```julia
using Pkg
Pkg.add([
    "Colors",
    "JSON",
    "Printf",
    "Statistics",
    "Test"
])
```

Or use the Project.toml:

```bash
julia --project=. -e 'using Pkg; Pkg.instantiate()'
```

## Troubleshooting

### Issue: Colors package not found

**Solution:**
```bash
cd /Users/bob/i/asi/skills/low-discrepancy-sequences
julia --project=. -e 'using Pkg; Pkg.add("Colors")'
```

### Issue: Julia not in PATH

**Solution:**
Add Julia to PATH or use full path:
```bash
/Applications/Julia-1.9.app/Contents/Resources/julia/bin/julia mcp_integration.jl ...
```

### Issue: Slow startup time

**Solution:**
Use DaemonMode.jl (see Performance Considerations above) or create a persistent Julia process.

### Issue: JSON parsing errors

**Solution:**
Ensure JSON parameters are properly escaped:
```bash
julia mcp_integration.jl gay_plastic_thread "{\"steps\": 5, \"seed\": 42}"
```

## Next Steps

1. **Install dependencies** - Run `julia --project=. -e 'using Pkg; Pkg.instantiate()'`
2. **Test tools** - Run example commands above
3. **Integrate with gay-mcp** - Choose integration option (1, 2, or 3)
4. **Register tools** - Add tool definitions to MCP server
5. **Deploy** - Test end-to-end with MCP clients

## Status

- ✓ Implementation complete (10 tools, 700+ lines)
- ✓ Project.toml created
- ✓ Documentation complete
- ⏳ Dependency installation required
- ⏳ Integration with gay-mcp server
- ⏳ End-to-end testing

## Support

For issues or questions:
- See INTEGRATION_GUIDE.md for detailed tool specifications
- See README.md for theoretical background
- See examples.jl for usage examples
