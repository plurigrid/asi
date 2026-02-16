#!/usr/bin/env python3
"""
Turbo ACSet Bridge - py-acsets + JAX parallel colors
"""
# /// script
# requires-python = ">=3.11"
# dependencies = ["acsets", "numpy"]
# ///

import sys, time
import numpy as np

# JAX backend
import jax
jax.config.update("jax_enable_x64", True)
import jax.numpy as jnp
from jax import jit

# py-acsets
from acsets import Ob, Hom, Attr, AttrType, Schema, ACSet

# ═══════════════════════════════════════════════════════════════════════════
# SplitMix64 (JIT-compiled)
# ═══════════════════════════════════════════════════════════════════════════

@jit
def sm64_batch(seed: int, indices: jnp.ndarray) -> jnp.ndarray:
    """Vectorized SplitMix64"""
    z = jnp.uint64(seed) ^ indices.astype(jnp.uint64)
    z = (z ^ (z >> 30)) * jnp.uint64(0xBF58476D1CE4E5B9)
    z = (z ^ (z >> 27)) * jnp.uint64(0x94D049BB133111EB)
    return z ^ (z >> 31)

# ═══════════════════════════════════════════════════════════════════════════
# Color Traceroute Schema (py-acsets native)
# ═══════════════════════════════════════════════════════════════════════════

# Define schema using py-acsets API (pydantic style)
ColorHop = Ob(name="ColorHop")
ColorAgent = Ob(name="ColorAgent")
ColorBridge = Ob(name="ColorBridge")

color_schema = Schema(
    name="ColorTraceroute",
    obs=[ColorHop, ColorAgent, ColorBridge],
    homs=[
        Hom(name="next", dom="ColorHop", codom="ColorHop"),
        Hom(name="source", dom="ColorBridge", codom="ColorHop"),
        Hom(name="target", dom="ColorBridge", codom="ColorHop"),
    ],
    attrtypes=[
        AttrType(name="float", ty=float),
        AttrType(name="int", ty=int),
        AttrType(name="str", ty=str),
    ],
    attrs=[
        Attr(name="hue", dom="ColorHop", codom="float"),
        Attr(name="trit", dom="ColorHop", codom="int"),
        Attr(name="state", dom="ColorHop", codom="int"),
        Attr(name="server", dom="ColorHop", codom="str"),
        
        Attr(name="agent_name", dom="ColorAgent", codom="str"),
        Attr(name="agent_trit", dom="ColorAgent", codom="int"),
        
        Attr(name="bridge_hue", dom="ColorBridge", codom="float"),
        Attr(name="dimension", dom="ColorBridge", codom="int"),
    ],
)

# ═══════════════════════════════════════════════════════════════════════════
# Batch ACSet construction
# ═══════════════════════════════════════════════════════════════════════════

def create_color_acset(seed: int, servers: list[str], n_agents: int = 27) -> ACSet:
    """
    Create ColorTraceroute ACSet with JAX-parallelized colors.
    """
    n_hops = len(servers)
    
    # Generate hop colors in parallel
    indices = jnp.arange(n_hops)
    states = sm64_batch(seed, indices)
    states.block_until_ready()
    
    # Convert to numpy
    states_np = np.array(states)
    hues = (states_np % 65536) / 65536 * 360
    trits = (states_np % 3).astype(int) - 1
    
    # Create ACSet instance
    acset = ACSet(name="traceroute", schema=color_schema)
    
    # Add hops
    for i, server in enumerate(servers):
        part_id = acset.add_part(ColorHop)
        acset.set_subpart(part_id, "hue", float(hues[i]))
        acset.set_subpart(part_id, "trit", int(trits[i]))
        acset.set_subpart(part_id, "state", int(states_np[i]))
        acset.set_subpart(part_id, "server", server)
    
    # Add agents
    agent_indices = jnp.arange(n_agents) + 1000
    agent_states = sm64_batch(seed, agent_indices)
    agent_states.block_until_ready()
    agent_states_np = np.array(agent_states)
    agent_trits = (agent_states_np % 3).astype(int) - 1
    
    for i in range(n_agents):
        path = []
        n = i
        for _ in range(3):
            path.append("-o+"[n % 3])
            n //= 3
        name = "".join(reversed(path))
        part_id = acset.add_part(ColorAgent)
        acset.set_subpart(part_id, "agent_name", name)
        acset.set_subpart(part_id, "agent_trit", int(agent_trits[i]))
    
    # Add bridges between consecutive hops
    for i in range(n_hops - 1):
        bridge_seed = int(states_np[i]) ^ int(states_np[i + 1])
        bridge_state = sm64_batch(bridge_seed, jnp.array([0]))
        bridge_hue = float((int(bridge_state[0]) % 65536) / 65536 * 360)
        dim = 1 if trits[i] != trits[i + 1] else 0
        part_id = acset.add_part(ColorBridge)
        acset.set_subpart(part_id, "bridge_hue", bridge_hue)
        acset.set_subpart(part_id, "dimension", dim)
        acset.set_subpart(part_id, "source", i + 1)  # 1-indexed
        acset.set_subpart(part_id, "target", i + 2)
    
    return acset

# ═══════════════════════════════════════════════════════════════════════════
# Main
# ═══════════════════════════════════════════════════════════════════════════

SERVERS = ["sRGB", "clojure-mcp", "nrepl-mcp", "grain", "modex", "fastmlx", "Gay.jl", "∞"]

def main():
    seed = int(sys.argv[1], 16) if len(sys.argv) > 1 else 0x42D
    
    # Warmup JIT
    _ = sm64_batch(seed, jnp.arange(100)).block_until_ready()
    
    t0 = time.perf_counter()
    acset = create_color_acset(seed, SERVERS, n_agents=27)
    dt = time.perf_counter() - t0
    
    print(f"ACSet created in {dt*1000:.2f}ms")
    print(f"Schema: {acset.schema.name}")
    print(f"Hops: {acset.nparts(ColorHop)}")
    print(f"Agents: {acset.nparts(ColorAgent)}")
    print(f"Bridges: {acset.nparts(ColorBridge)}")
    
    print("\nHops:")
    for i in range(acset.nparts(ColorHop)):
        hue = acset.subpart(i, ColorHop, "hue")
        trit = acset.subpart(i, ColorHop, "trit")
        server = acset.subpart(i, ColorHop, "server")
        h = float(hue)
        r = int(128 + 127 * np.cos((h - 0) * np.pi / 180))
        g = int(128 + 127 * np.cos((h - 120) * np.pi / 180))
        b = int(128 + 127 * np.cos((h - 240) * np.pi / 180))
        print(f"\033[48;2;{r};{g};{b}m  \033[0m {i} {server:12} {'−○+'[trit+1]}")
    
    # Export JSON
    json_data = acset.to_json_dict()
    print(f"\nExportable to Catlab via acset.to_json_dict()")

if __name__ == "__main__":
    main()
