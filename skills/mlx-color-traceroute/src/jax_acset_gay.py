#!/usr/bin/env python3
"""
JAX + py-acsets + Gay.jl Bridge

Parallelizes color generation using JAX vmap/pmap while storing
structure in ACSets for categorical composition.

The bridge works as:
  Gay.jl (Julia) ←→ ACSets (categorical structure) ←→ JAX (parallel compute)
"""
# /// script
# requires-python = ">=3.11"
# dependencies = ["jax", "jaxlib", "numpy", "rich"]
# ///

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Any
import json

# JAX imports with fallback
try:
    # Enable 64-bit mode for SplitMix64
    import jax
    jax.config.update("jax_enable_x64", True)
    import jax.numpy as jnp
    from jax import vmap, pmap, jit
    HAS_JAX = True
except ImportError:
    HAS_JAX = False
    import numpy as jnp
    def vmap(f): return lambda x: [f(xi) for xi in x]
    def jit(f): return f

import numpy as np

# ═══════════════════════════════════════════════════════════════════════════
# SplitMix64 in JAX (matches Gay.jl exactly)
# ═══════════════════════════════════════════════════════════════════════════

@jit
def splitmix64_jax(z: jnp.ndarray) -> jnp.ndarray:
    """
    SplitMix64 PRNG step, vectorized for JAX.
    Matches Gay.jl/src/splittable.jl
    """
    z = z.astype(jnp.uint64)
    z = (z ^ (z >> 30)) * jnp.uint64(0xBF58476D1CE4E5B9)
    z = (z ^ (z >> 27)) * jnp.uint64(0x94D049BB133111EB)
    return z ^ (z >> 31)


@jit
def state_to_color(state: jnp.ndarray) -> Tuple[jnp.ndarray, jnp.ndarray]:
    """
    Convert SplitMix64 state to (hue, trit).
    - hue: 0-360 degrees
    - trit: -1, 0, +1 (GF(3))
    """
    hue = (state % 65536).astype(jnp.float32) / 65536.0 * 360.0
    trit_raw = state % 3
    # Map 0 -> -1, 1 -> 0, 2 -> +1
    trit = trit_raw.astype(jnp.int32) - 1
    return hue, trit


def batch_colors(seed: int, indices: jnp.ndarray) -> Dict[str, jnp.ndarray]:
    """
    Generate colors for a batch of indices in parallel.
    Uses JAX vmap for vectorization.
    """
    seeds = jnp.full_like(indices, seed, dtype=jnp.uint64)
    combined = seeds ^ indices.astype(jnp.uint64)
    states = splitmix64_jax(combined)
    hues, trits = state_to_color(states)
    
    return {
        "indices": indices,
        "states": states,
        "hues": hues,
        "trits": trits,
    }


# ═══════════════════════════════════════════════════════════════════════════
# ACSets Schema for Color Traceroute
# ═══════════════════════════════════════════════════════════════════════════

@dataclass
class Ob:
    """Object in ACSet schema (table)"""
    name: str
    
@dataclass  
class Hom:
    """Morphism in ACSet schema (foreign key)"""
    name: str
    dom: str
    codom: str

@dataclass
class Attr:
    """Attribute in ACSet schema (data column)"""
    name: str
    dom: str
    codom: str  # Type name like "Int", "Float", "String"

@dataclass
class ACSetSchema:
    """
    Schema for an ACSet (Attributed C-Set).
    Defines the categorical structure.
    """
    name: str
    obs: List[Ob] = field(default_factory=list)
    homs: List[Hom] = field(default_factory=list)
    attrs: List[Attr] = field(default_factory=list)
    
    def to_json(self) -> dict:
        return {
            "name": self.name,
            "obs": [o.name for o in self.obs],
            "homs": [{"name": h.name, "dom": h.dom, "codom": h.codom} for h in self.homs],
            "attrs": [{"name": a.name, "dom": a.dom, "codom": a.codom} for a in self.attrs],
        }


# Color Traceroute Schema
COLOR_TRACEROUTE_SCHEMA = ACSetSchema(
    name="ColorTraceroute",
    obs=[
        Ob("Hop"),           # Traceroute hops
        Ob("Agent"),         # Triadic agents
        Ob("Bridge"),        # Observational bridges
    ],
    homs=[
        Hom("next", "Hop", "Hop"),           # Hop → next Hop
        Hom("source", "Bridge", "Hop"),      # Bridge source
        Hom("target", "Bridge", "Hop"),      # Bridge target
        Hom("agent", "Hop", "Agent"),        # Which agent owns hop
    ],
    attrs=[
        Attr("seed", "Hop", "UInt64"),
        Attr("index", "Hop", "Int"),
        Attr("hue", "Hop", "Float"),
        Attr("trit", "Hop", "Int"),          # -1, 0, +1
        Attr("server", "Hop", "String"),
        Attr("latency", "Hop", "Float"),
        
        Attr("agent_seed", "Agent", "UInt64"),
        Attr("agent_trit", "Agent", "Int"),  # Agent disposition
        Attr("agent_name", "Agent", "String"),
        
        Attr("bridge_color", "Bridge", "Float"),
        Attr("dimension", "Bridge", "Int"),  # 0=value, 1=diff, 2=conflict
    ],
)


@dataclass
class ACSet:
    """
    An instance of an ACSet schema.
    Stores data in numpy arrays for JAX compatibility.
    """
    schema: ACSetSchema
    tables: Dict[str, Dict[str, np.ndarray]] = field(default_factory=dict)
    
    def __post_init__(self):
        # Initialize empty tables for each object
        for ob in self.schema.obs:
            if ob.name not in self.tables:
                self.tables[ob.name] = {"_id": np.array([], dtype=np.int64)}
    
    def add_part(self, ob_name: str, **attrs) -> int:
        """Add a part (row) to an object table."""
        table = self.tables[ob_name]
        new_id = len(table["_id"])
        table["_id"] = np.append(table["_id"], new_id)
        
        for key, value in attrs.items():
            if key not in table:
                table[key] = np.array([value])
            else:
                table[key] = np.append(table[key], value)
        
        return new_id
    
    def add_parts(self, ob_name: str, n: int, **attrs) -> np.ndarray:
        """Add multiple parts at once (batch operation)."""
        table = self.tables[ob_name]
        start_id = len(table["_id"])
        new_ids = np.arange(start_id, start_id + n)
        table["_id"] = np.concatenate([table["_id"], new_ids])
        
        for key, value in attrs.items():
            if key not in table:
                table[key] = np.array(value)
            else:
                table[key] = np.concatenate([table[key], np.array(value)])
        
        return new_ids
    
    def nparts(self, ob_name: str) -> int:
        """Number of parts in an object."""
        return len(self.tables[ob_name]["_id"])
    
    def subpart(self, ob_name: str, attr: str, idx: Optional[int] = None) -> np.ndarray:
        """Get attribute values."""
        if idx is not None:
            return self.tables[ob_name][attr][idx]
        return self.tables[ob_name][attr]
    
    def to_json(self) -> dict:
        """Export to Catlab-compatible JSON."""
        result = {
            "schema": self.schema.to_json(),
            "tables": {}
        }
        for ob_name, table in self.tables.items():
            result["tables"][ob_name] = {
                k: v.tolist() for k, v in table.items()
            }
        return result
    
    def fingerprint(self) -> int:
        """Compute SPI-compliant fingerprint by XORing all states."""
        fp = 0
        for ob_name, table in self.tables.items():
            if "seed" in table:
                for s in table["seed"]:
                    fp ^= int(s)
        return fp


# ═══════════════════════════════════════════════════════════════════════════
# Parallel Color Generation with JAX
# ═══════════════════════════════════════════════════════════════════════════

def create_parallel_traceroute(
    seed: int,
    servers: List[str],
    n_agents: int = 27,  # 3³
) -> ACSet:
    """
    Create a color traceroute ACSet with parallel JAX computation.
    
    Args:
        seed: Genesis seed for deterministic colors
        servers: List of server names for hops
        n_agents: Number of triadic agents (default: 27 = 3³)
    
    Returns:
        ACSet with Hop, Agent, and Bridge tables populated
    """
    acset = ACSet(schema=COLOR_TRACEROUTE_SCHEMA)
    
    # Generate hop colors in parallel
    n_hops = len(servers)
    indices = jnp.arange(n_hops)
    colors = batch_colors(seed, indices)
    
    # Add hops to ACSet
    hop_ids = acset.add_parts(
        "Hop",
        n_hops,
        seed=np.full(n_hops, seed),
        index=np.array(colors["indices"]),
        hue=np.array(colors["hues"]),
        trit=np.array(colors["trits"]),
        server=np.array(servers),
        latency=np.array([1 + i * np.log(i + 1) for i in range(n_hops)]),
    )
    
    # Generate triadic agents in parallel
    agent_indices = jnp.arange(n_agents)
    agent_colors = batch_colors(seed, agent_indices + 1000)  # Offset to distinguish
    
    # Agent names based on GF(3) path
    agent_names = []
    for i in range(n_agents):
        path = []
        n = i
        for _ in range(3):  # 3 levels
            path.append(["−", "○", "+"][n % 3])
            n //= 3
        agent_names.append("".join(reversed(path)))
    
    acset.add_parts(
        "Agent",
        n_agents,
        agent_seed=np.array(agent_colors["states"]),
        agent_trit=np.array(agent_colors["trits"]),
        agent_name=np.array(agent_names),
    )
    
    # Create bridges between consecutive hops
    for i in range(n_hops - 1):
        bridge_seed = int(colors["states"][i]) ^ int(colors["states"][i + 1])
        bridge_color = batch_colors(bridge_seed, jnp.array([0]))
        
        acset.add_part(
            "Bridge",
            source=i,
            target=i + 1,
            bridge_color=float(bridge_color["hues"][0]),
            dimension=1 if colors["trits"][i] != colors["trits"][i + 1] else 0,
        )
    
    return acset


# ═══════════════════════════════════════════════════════════════════════════
# GF(3) Conservation Check
# ═══════════════════════════════════════════════════════════════════════════

def check_gf3_conservation(acset: ACSet) -> Dict[str, Any]:
    """
    Verify GF(3) conservation across the ACSet.
    Sum of all trits should be ≡ 0 (mod 3).
    """
    hop_trits = acset.subpart("Hop", "trit")
    agent_trits = acset.subpart("Agent", "agent_trit")
    
    hop_sum = int(np.sum(hop_trits))
    agent_sum = int(np.sum(agent_trits))
    total_sum = hop_sum + agent_sum
    
    return {
        "hop_trit_sum": hop_sum,
        "agent_trit_sum": agent_sum,
        "total_sum": total_sum,
        "mod_3": total_sum % 3,
        "balanced": total_sum % 3 == 0,
    }


# ═══════════════════════════════════════════════════════════════════════════
# Julia Interop (via JSON)
# ═══════════════════════════════════════════════════════════════════════════

def export_for_julia(acset: ACSet, path: str):
    """Export ACSet to JSON for Julia/Catlab import."""
    with open(path, "w") as f:
        json.dump(acset.to_json(), f, indent=2)


def import_from_julia(path: str, schema: ACSetSchema) -> ACSet:
    """Import ACSet from Julia/Catlab JSON export."""
    with open(path) as f:
        data = json.load(f)
    
    acset = ACSet(schema=schema)
    for ob_name, table_data in data.get("tables", {}).items():
        for key, values in table_data.items():
            acset.tables[ob_name][key] = np.array(values)
    
    return acset


# ═══════════════════════════════════════════════════════════════════════════
# CLI / Demo
# ═══════════════════════════════════════════════════════════════════════════

SERVERS = [
    "sRGB", "clojure-mcp", "nrepl-mcp-server", "grain/clj-dspy",
    "modex", "java-probe", "fastmlx", "Gay.jl/Rec2020", "metaphysics"
]


def main():
    from rich.console import Console
    from rich.table import Table
    from rich.panel import Panel
    
    console = Console()
    
    seed = 0x42D
    
    console.print(Panel.fit(
        f"[bold]JAX + py-acsets + Gay.jl Bridge[/]\n"
        f"Seed: [cyan]0x{seed:X}[/] | JAX available: [{'green' if HAS_JAX else 'red'}]{HAS_JAX}[/]",
        border_style="blue"
    ))
    
    # Create parallel traceroute
    acset = create_parallel_traceroute(seed, SERVERS, n_agents=27)
    
    # Display hops
    table = Table(title="Color Traceroute (JAX-parallelized)")
    table.add_column("Hop", style="dim")
    table.add_column("Server")
    table.add_column("Hue", justify="right")
    table.add_column("Trit", justify="center")
    table.add_column("Latency")
    
    for i in range(acset.nparts("Hop")):
        hue = acset.subpart("Hop", "hue", i)
        trit = acset.subpart("Hop", "trit", i)
        server = acset.subpart("Hop", "server", i)
        latency = acset.subpart("Hop", "latency", i)
        trit_sym = {-1: "−", 0: "○", 1: "+"}[int(trit)]
        
        # HSL to RGB for display
        h = float(hue) / 360
        r = int(255 * (1 - abs(h * 6 - 3) + 1) / 2)
        g = int(255 * (1 - abs(h * 6 - 2) + 1) / 2)
        b = int(255 * (1 - abs(h * 6 - 4) + 1) / 2)
        
        table.add_row(
            str(i),
            str(server),
            f"{float(hue):.1f}°",
            trit_sym,
            f"{float(latency):.3f}ms"
        )
    
    console.print(table)
    
    # GF(3) check
    gf3 = check_gf3_conservation(acset)
    console.print(f"\n[bold]GF(3) Conservation:[/]")
    console.print(f"  Hop trits: {gf3['hop_trit_sum']}")
    console.print(f"  Agent trits: {gf3['agent_trit_sum']}")
    console.print(f"  Total: {gf3['total_sum']} ≡ {gf3['mod_3']} (mod 3)")
    if gf3['balanced']:
        console.print("  [green]✓ Balanced[/]")
    else:
        console.print("  [yellow]○ Imbalanced[/]")
    
    # Display agents (first 9)
    console.print(f"\n[bold]Agents ({acset.nparts('Agent')} total, showing 9):[/]")
    for i in range(min(9, acset.nparts("Agent"))):
        name = acset.subpart("Agent", "agent_name", i)
        trit = acset.subpart("Agent", "agent_trit", i)
        trit_sym = {-1: "−", 0: "○", 1: "+"}[int(trit)]
        console.print(f"  [{name}] trit={trit_sym}")
    
    # Fingerprint
    fp = acset.fingerprint()
    console.print(f"\n[bold]ACSet Fingerprint:[/] 0x{fp:016X}")
    
    # Export path
    export_path = "/tmp/color_traceroute.json"
    export_for_julia(acset, export_path)
    console.print(f"\n[dim]Exported to {export_path} (Catlab-compatible)[/]")


if __name__ == "__main__":
    main()
