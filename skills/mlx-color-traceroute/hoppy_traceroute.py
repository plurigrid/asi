#!/usr/bin/env python3
"""
Hoppy Color Traceroute - MLX + Clojure MCP + Gay.jl

Deploy: uv run hoppy_traceroute.py --seed 0x42D
"""
# /// script
# requires-python = ">=3.11"
# dependencies = ["rich", "click"]
# ///

import click
from rich.console import Console
from rich.table import Table
from rich.panel import Panel
from rich.text import Text
import math
from dataclasses import dataclass
from typing import List, Tuple

console = Console()

# MCP ecosystem servers discovered via gh-interactome
SERVERS = [
    ("sRGB", "gamut", "Standard color space"),
    ("clojure-mcp", "bhauman", "★657 - Clojure MCP core"),
    ("nrepl-mcp-server", "JohanCodinha", "★34 - nREPL ↔ Claude"),
    ("grain/clj-dspy", "cjbarre", "★81 - DSPy + behavior trees"),
    ("modex", "theronic", "★108 - MCP client+server"),
    ("java-probe", "awkay", "★3 - Fulcro javadocs for AI"),
    ("fastmlx", "plurigrid", "MLX OpenAI-compat API"),
    ("Gay.jl/Rec2020", "bmorphism", "Wide gamut colors"),
    ("metaphysics", "∞", "Arrival"),
]


@dataclass
class HopColor:
    """Deterministic color from SplitMix64"""
    hue: float
    trit: int  # -1, 0, +1
    state: int
    
    @property
    def trit_symbol(self) -> str:
        return {-1: "−", 0: "○", 1: "+"}[self.trit]
    
    @property
    def rgb(self) -> Tuple[int, int, int]:
        """HSL to RGB (s=0.7, l=0.55)"""
        h = self.hue / 360
        s, l = 0.7, 0.55
        
        def hue2rgb(p, q, t):
            if t < 0: t += 1
            if t > 1: t -= 1
            if t < 1/6: return p + (q - p) * 6 * t
            if t < 1/2: return q
            if t < 2/3: return p + (q - p) * (2/3 - t) * 6
            return p
        
        q = l + s * (1 - abs(2*l - 1)) / 2
        p = 2 * l - q
        r = hue2rgb(p, q, h + 1/3)
        g = hue2rgb(p, q, h)
        b = hue2rgb(p, q, h - 1/3)
        return int(r * 255), int(g * 255), int(b * 255)
    
    @property
    def hex(self) -> str:
        r, g, b = self.rgb
        return f"#{r:02X}{g:02X}{b:02X}"


def splitmix64(z: int) -> int:
    """SplitMix64 PRNG step"""
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & 0xFFFFFFFFFFFFFFFF
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & 0xFFFFFFFFFFFFFFFF
    return (z ^ (z >> 31)) & 0xFFFFFFFFFFFFFFFF


def hop_color(seed: int, idx: int) -> HopColor:
    """Deterministic color for a hop"""
    state = splitmix64(seed ^ idx)
    trit = [-1, 0, 1][state % 3]
    hue = (state % 65536) / 65536.0 * 360
    return HopColor(hue=hue, trit=trit, state=state)


def triadic_split(seed: int) -> dict:
    """Split seed into three GF(3) balanced agents"""
    base = splitmix64(seed)
    return {
        "minus":   base ^ 0x2D2D2D2D2D2D2D2D,
        "ergodic": base ^ 0x5F5F5F5F5F5F5F5F,
        "plus":    base ^ 0x2B2B2B2B2B2B2B2B,
    }


@click.command()
@click.option("--seed", default=0x42D, help="Genesis seed (hex or decimal)")
@click.option("--triadic/--no-triadic", default=False, help="Show triadic agent split")
@click.option("--wide-gamut", type=click.Choice(["srgb", "p3", "rec2020"]), default="rec2020")
def traceroute(seed: int, triadic: bool, wide_gamut: str):
    """Trace color path through Clojure MCP ecosystem
    
    Each hop gets a deterministic color via SplitMix64.
    GF(3) trits track agent disposition: MINUS(-1), ERGODIC(0), PLUS(+1).
    """
    
    # Header
    console.print(Panel.fit(
        f"[bold]COLOR TRACEROUTE TO METAPHYSICS[/]\n"
        f"Seed: [cyan]0x{seed:X}[/] | Gamut: [magenta]{wide_gamut.upper()}[/]",
        border_style="blue"
    ))
    
    # Main traceroute table
    table = Table(show_header=True, header_style="bold")
    table.add_column("Hop", style="dim", width=4)
    table.add_column("Server", width=20)
    table.add_column("Author", width=15)
    table.add_column("Color", width=10)
    table.add_column("Trit", width=4, justify="center")
    table.add_column("Latency", width=10)
    table.add_column("Info", style="dim")
    
    trit_sum = 0
    colors: List[HopColor] = []
    
    for i, (server, author, info) in enumerate(SERVERS):
        color = hop_color(seed, i)
        colors.append(color)
        r, g, b = color.rgb
        trit_sum += color.trit
        latency = f"{(1 + i * math.log(i + 1)):.3f}ms"
        
        # Color swatch with rich markup
        swatch = f"[on rgb({r},{g},{b})]  {color.hex}  [/]"
        
        table.add_row(
            str(i),
            server,
            author,
            swatch,
            color.trit_symbol,
            latency,
            info
        )
    
    console.print(table)
    
    # GF(3) conservation check
    console.print()
    balance_mod = trit_sum % 3
    if balance_mod == 0:
        console.print(f"[green]✓ GF(3) sum = {trit_sum} ≡ 0 (mod 3) — Triadic balance conserved[/]")
    else:
        console.print(f"[yellow]○ GF(3) sum = {trit_sum} ≡ {balance_mod} (mod 3)[/]")
    
    # Triadic split if requested
    if triadic:
        console.print()
        console.print("[bold]Triadic Agent Split:[/]")
        agents = triadic_split(seed)
        for name, agent_seed in agents.items():
            color = hop_color(agent_seed, 0)
            r, g, b = color.rgb
            console.print(f"  {name.upper():8} seed=0x{agent_seed:016X} [on rgb({r},{g},{b})]  {color.hex}  [/]")
    
    # Color sequence visualization
    console.print()
    text = Text("Route: ")
    for i, color in enumerate(colors):
        r, g, b = color.rgb
        text.append("██", style=f"rgb({r},{g},{b})")
        if i < len(colors) - 1:
            text.append("→", style="dim")
    console.print(text)


@click.command()
@click.option("--seed", default=0x42D)
@click.option("--count", default=27, help="Number of agents (default: 3³=27)")
def spawn_hierarchy(seed: int, count: int):
    """Spawn hierarchical agents with GF(3) balance"""
    console.print(f"[bold]Spawning {count} agents from seed 0x{seed:X}[/]")
    
    agents = []
    for i in range(count):
        color = hop_color(seed, i)
        agents.append(color)
    
    trit_sum = sum(a.trit for a in agents)
    console.print(f"Total trit sum: {trit_sum} mod 3 = {trit_sum % 3}")
    
    # Show first 9
    for i, color in enumerate(agents[:9]):
        r, g, b = color.rgb
        console.print(f"  Agent {i:2d}: [on rgb({r},{g},{b})]  {color.hex}  [/] trit={color.trit_symbol}")


@click.group()
def cli():
    """Hoppy Color Traceroute - MLX + Clojure MCP + Gay.jl"""
    pass


cli.add_command(traceroute, name="trace")
cli.add_command(spawn_hierarchy, name="spawn")


if __name__ == "__main__":
    # Default to traceroute if run directly
    traceroute()
