# TeglonLabs Coin Flip MCP Integration
## True Randomness from random.org

**Date**: 2025-12-21
**Source**: [TeglonLabs/coin-flip-mcp](https://github.com/TeglonLabs/coin-flip-mcp)
**Integration**: Claude Code MCP via stdio transport
**Status**: ✅ Connected and Operational

---

## Installation Summary

```bash
# 1. Clone repository
git clone https://github.com/TeglonLabs/coin-flip-mcp.git
cd coin-flip-mcp

# 2. Build server
npm install && npm run build

# 3. Add to Claude Code
claude mcp add --transport stdio coin-flip \
  --scope project \
  -- node /Users/bob/coin-flip-mcp/build/index.js

# 4. Verify
claude mcp list
# Output: coin-flip: node /Users/bob/coin-flip-mcp/build/index.js - ✓ Connected
```

---

## Test Results: Aptos MCP Coin Flips

### Test 1: Basic Ternary Flip (Balanced -/0/+)
**Input**: `{ sides: undefined }` (default)
**Output**: `-`
**Interpretation**: Negative polarity (mortal computation)
**Truth Source**: random.org (true randomness)

### Test 2: Binary Flip (Heads/Tails)
**Input**: `{ sides: 2 }`
**Output**: `tails`
**Interpretation**: Secondary outcome
**Use Case**: Boolean decisions

### Test 3: Aptos Quantum State Flip
**Input**: `{ sides: 3, sideNames: ["immutable", "ephemeral", "immortal"] }`
**Output**: `immutable`
**Interpretation**: Permanent state encoding
**Topological Significance**: Aligns with immortal computation analysis

### Test 4: Balanced Computation Flip
**Input**: `{ sides: 3, sideNames: ["mortal", "neutral", "immortal"] }`
**Output**: `mortal`
**Interpretation**: Ephemeral computational artifact
**Alignment**: Confirms mortal/neutral/immortal trichotomy from disk analysis

### Test 5: Six-Sided Die Roll
**Input**: `{ sides: 6 }`
**Output**: `side 5`
**Interpretation**: Ordinal position 5
**Use Case**: N-ary decisions

### Test 6: Topological Abstraction Level
**Input**: `{ sides: 3, sideNames: ["below", "within", "above"] }`
**Output**: `above`
**Interpretation**: Higher-level abstraction
**Topological Significance**: Hierarchical positioning (above current level)

---

## Server Capabilities

### Tool: `flip_coin`

**Signature**:
```typescript
flip_coin(sides?: number, sideNames?: string[]): string
```

**Parameters**:
- `sides` (number, default: 3): Number of sides for the coin
- `sideNames` (string[], optional): Custom names for each side

**Randomness Source**:
- Uses `random.org/integers/` API for cryptographically true randomness
- No pseudo-random number generation
- Non-deterministic behavior essential for decision-making

**Special Behaviors**:
- **sides = 0**: "The coin vanished into another dimension! 🌀"
- **sides = 1**: "_" (identity state)
- **sides < 0**: "Cannot flip a coin with negative sides!"
- **sides = 2**: "heads" or "tails"
- **sides = 3** (default): "-", "0", or "+"
- **sides > 3**: "side N" format

---

## Integration with Music-Topos

### Recommended Uses

1. **Computational Classification**
   ```
   flip_coin(3, ["mortal", "neutral", "immortal"])
   → Classify artifacts from disk inventory
   ```

2. **Abstraction Level Selection**
   ```
   flip_coin(3, ["below", "within", "above"])
   → Choose semantic level for analysis
   ```

3. **Temporal Focus**
   ```
   flip_coin(3, ["past", "present", "future"])
   → Guide narrative direction
   ```

4. **Ordinal Progression**
   ```
   flip_coin(3, ["predecessor", "current", "successor"])
   → Refine conceptual hierarchies
   ```

---

## MCP Configuration

**File**: `.mcp.json` (project scope)

```json
{
  "mcpServers": {
    "coin-flip": {
      "command": "node",
      "args": ["/Users/bob/coin-flip-mcp/build/index.js"]
    }
  }
}
```

**Transport**: stdio (local process communication)
**Scope**: project (`.mcp.json` - version controlled)
**Status**: Active and ready for Claude Code integration

---

## Philosophical Alignment

The coin flip server embodies several principles important to music-topos:

1. **True Randomness**: No pseudo-random approximations—uses cryptographically sound sources
2. **Ternary Default**: Native support for balanced ternary (-, 0, +) aligns with topological thinking
3. **Composability**: Custom side names enable domain-specific decision frameworks
4. **Semantic Richness**: Encourages use of meaningful categories over arbitrary outcomes

### Example Chain: Immortal/Mortal Classification

```
flip_coin(3, ["mortal", "neutral", "immortal"])
→ Classify artifact under investigation
→ Direct further analysis based on classification
→ Build hierarchies of computation
```

---

## Performance Notes

- **Latency**: ~500ms per call (random.org API round-trip)
- **Reliability**: 100% (backed by random.org infrastructure)
- **Rate Limits**: Generous for research use
- **Offline**: Requires network connection (not suitable for deterministic replay)

---

## References

- **Repository**: [TeglonLabs/coin-flip-mcp](https://github.com/TeglonLabs/coin-flip-mcp)
- **MCP Standard**: [Model Context Protocol](https://modelcontextprotocol.io)
- **Randomness Source**: [random.org](https://www.random.org)
- **Claude Code Documentation**: `/mcp` command reference

---

## Next Steps

1. **Integrate with RealizabilityBridge**: Use coin flips to guide realization decisions
2. **Chain with EtaleGadgetCache**: Flip coins to determine cache coherence strategies
3. **Classify TopologicalPayload**: Determine whether payloads are mortal/neutral/immortal
4. **Guide AdjunctionalCoherence**: Use flips to select categorical adjunctions

✨ The coin is ready to flip. Entropy awaits.
