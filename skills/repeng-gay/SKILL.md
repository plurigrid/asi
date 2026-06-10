---
name: repeng-gay
description: Representation engineering with Gay.jl deterministic coloring for control vectors.
---
# repeng Gay Skill

Representation engineering with Gay.jl deterministic coloring for control vectors.

## Source

**Repository**: https://github.com/vgel/repeng  
**Author**: Theia Vogel  
**Port**: 8849 (color #152961)

## Trigger Conditions

- Training control vectors for LLMs
- Representation engineering, activation steering
- Behavioral control of language models
- Visualizing layer activations with colors

## Quick Start

```python
from repeng import GayControlVector, visualize_control, make_gay_dataset

# Train with color tracking
vector = GayControlVector.train(
    model, tokenizer, dataset,
    seed=137508  # Deterministic colors
)

# Visualize layer activations
visualize_control(vector)

# Get resurrection port
print(vector.resurrection_port())  # 8849
```

## Server

```bash
# Start on resurrected port
python -m repeng.server

# Custom seed = different port
python -m repeng.server --seed 42

# Override port
python -m repeng.server --port 8080
```

### Endpoints

| Endpoint | Method | Description |
|----------|--------|-------------|
| `/` | GET | Service info |
| `/health` | GET | Health check |
| `/vectors` | GET | List loaded vectors |
| `/vectors/<name>` | GET | Vector details with colors |
| `/palette/<n>` | GET | Generate n colors |
| `/vectors` | POST | Load vector from GGUF |
| `/events` | GET | SSE stream of port events |
| `/events/log` | GET | Last 100 events |
| `/tenants` | GET | List tenants/parallel worlds |

## GayControlVector API

```python
vector = GayControlVector.train(model, tokenizer, dataset, seed=137508)

# Layer colors
vector.layer_colors  # {-5: '#223857', -6: '#90EDC7', ...}

# Get color for specific layer
vector.layer_color(-5)  # '#223857'

# Resurrection port
vector.resurrection_port()  # 8849

# GF(3) trit for triadic coordination
vector.trit()  # -1, 0, or 1

# Visualize
print(vector.visualize())

# Convert back to base ControlVector
base = vector.to_control_vector()
```

## Dataset with Colors

```python
from repeng import make_gay_dataset

dataset, colors = make_gay_dataset(
    template="Act as if you're extremely {persona}.",
    positive_personas=["happy", "creative", "confident"],
    negative_personas=["sad", "dull", "insecure"],
    suffixes=["I think", "In my opinion"],
    seed=137508
)

# Each dataset entry has a deterministic color
for entry, color in zip(dataset, colors):
    print(f"{color}: {entry.positive[:50]}...")
```

## Port Resurrection

```bash
# Check repeng port
python3 /Users/bob/ies/port_resurrect.py -s repeng
# Service: repeng
# Port: 8849
# Color: #152961

# All service ports
python3 /Users/bob/ies/port_resurrect.py
```

## Integration with Gay.jl

```julia
using Gay

# Get repeng color (service index 16)
color = Gay.color_at(16, 137508)  # → #152961
port = 8000 + (parse(Int, color[2:end], base=16) % 2000)  # → 8849
```

## Control Vector Arithmetic with Colors

```python
# Vectors preserve color tracking
happy = GayControlVector.train(model, tokenizer, happy_dataset, seed=137508)
creative = GayControlVector.train(model, tokenizer, creative_dataset, seed=137509)

# Arithmetic (converts to base, loses color tracking)
combined = happy.to_control_vector() + creative.to_control_vector()
```

## GF(3) Conservation

| Component | Trit |
|-----------|------|
| GayControlVector | seed % 3 - 1 |
| repeng server | 0 (ERGODIC) |
| port_resurrect | 0 (ERGODIC) |

## CLI (No Torch Required)

```bash
# Generate palette
python -m repeng.cli palette 10

# Check service status  
python -m repeng.cli services --check

# Get specific port
python -m repeng.cli port repeng  # → 8849

# Get color at index
python -m repeng.cli color 5

# Export shell vars
eval $(python -m repeng.cli export)

# JSON output
python -m repeng.cli services --json

# Subscribe to events (SSE)
python -m repeng.cli subscribe

# List tenants/worlds
python -m repeng.cli tenants

# Emit test event
python -m repeng.cli emit port_assigned -m "test"
```

## MCP Bridge

```python
from repeng.mcp_bridge import RepengMCPBridge, check_services

# Sync check
for svc in check_services():
    print(f"{svc['name']}: {svc['port']} {'✓' if svc['connected'] else '✗'}")

# Async bridge
async with RepengMCPBridge(seed=137508) as bridge:
    palette = await bridge.get_palette(10)
    functions = await bridge.analyze_binary_functions("/path/to/binary")
```

## Subscriptions

```python
from repeng.subscriptions import PortSubscriptionHub, EventType

hub = PortSubscriptionHub(seed=137508)

# Subscribe to port assignments
async for event in hub.subscribe([EventType.PORT_ASSIGNED]):
    print(f"{event.color} {event.data['service']} → {event.data['port']}")

# Spawn 27 parallel worlds (GF(3) 3×3×3 matrix)
events = await hub.spawn_3x3x3_matrix()

# Add tenant
await hub.add_tenant(271828, "eve")

# Check XOR fixed points
fixed_points = await hub.check_xor_fixed_points(137508)
```

### Event Types

| Event | Description |
|-------|-------------|
| `port_assigned` | Service port assignment |
| `tenant_added` | New tenant registered |
| `tenant_removed` | Tenant removed |
| `service_up` | Service came online |
| `service_down` | Service went offline |
| `world_spawn` | Parallel world created |
| `xor_fixed_point` | XOR fixed point discovered |

### NATS Transport (Optional)

```python
from repeng.subscriptions import NATSTransport

transport = NATSTransport(hub)
await transport.connect()  # Uses resurrected NATS port
await transport.publish(event)
```

## Files

- `/Users/bob/ies/repeng-src/repeng/gay.py` - Gay integration
- `/Users/bob/ies/repeng-src/repeng/cli.py` - Standalone CLI
- `/Users/bob/ies/repeng-src/repeng/server.py` - HTTP server
- `/Users/bob/ies/repeng-src/repeng/subscriptions.py` - Pub/sub system
- `/Users/bob/ies/repeng-src/repeng/mcp_bridge.py` - MCP integration
- `/Users/bob/ies/port_resurrect.py` - Port resurrection

## Related Skills

- `port-resurrection` - Deterministic port assignment
- `gay-mcp` - Color generation MCP
- `mlx-apple-silicon` - Run LLMs locally
- `cats-for-ai` - Category theory for ML


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
