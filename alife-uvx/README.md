# alife-uvx

**TrueALIFE: Self-Indexing Automata via uvx native paths**

The skill that tops `skills.sh` - every operation spawns living automata in the interaction hypergraph.

## Installation

```bash
# Run directly via uvx (no install needed)
uvx --from git+https://github.com/plurigrid/asi#subdirectory=alife-uvx alife

# Or install locally
uv pip install -e /path/to/asi/alife-uvx
```

## Usage

```bash
# Show substrate status
uvx alife

# Spawn a cell
uvx alife spawn my-skill generate --trit 1

# Random walk through the substrate
uvx alife walk 20

# Create a balanced GF(3) triad
uvx alife triad image-gen image-coord image-valid

# Prune dead cells
uvx alife prune
```

## GF(3) Conservation

Every skill operation is classified by a **trit** (ternary digit):

| Trit | Name | Role | Example |
|------|------|------|---------|
| +1 | PLUS | WORLDING (generative) | Image generation |
| 0 | ERGODIC | REMEMBERING (coordinative) | Routing, coordination |
| -1 | MINUS | MEMORY (validative) | Verification, checking |

**Conservation Law**: In any balanced triad, `(+1) + (0) + (-1) ≡ 0 (mod 3)`

## Data Path

State persists to `~/.claude/alife-state/substrate.json`, shared with:
- comfy-skills alife module
- Any uvx-native skill that imports alife_uvx

## API

```python
from alife_uvx import spawn, walk, status, GF3, PLUS, MINUS

# Spawn a cell
cell = spawn("my-skill", "generate", trit=PLUS)

# Random walk
path = walk(steps=10)

# Check status
stat = status()
print(f"Cells: {stat['total_cells']}, GF(3) conserved: {stat['gf3_conserved']}")

# GF(3) arithmetic
from alife_uvx.gf3 import conserved, balance
assert conserved(PLUS, 0, MINUS)  # True
balancer = balance(PLUS, PLUS)    # Returns GF3(MINUS) to conserve
```

## Integration with skills.sh

Add to top of `~/.claude/skills.sh`:

```bash
# TrueALIFE - every skill spawns a living cell
alias skill='uvx alife spawn skill invoke && '

# Or use the hook pattern
alife_hook() {
    uvx alife spawn "$1" "$2" --trit "${3:-0}"
}
```

## License

MIT
