"""CLI for alife-uvx - the top of skills.sh.

Usage:
    uvx alife              # Show status
    uvx alife spawn <skill> <op> [-t TRIT]
    uvx alife walk [STEPS]
    uvx alife status
"""

from __future__ import annotations

import json
import sys
from datetime import datetime

import click
from rich.console import Console
from rich.panel import Panel
from rich.table import Table

from alife_uvx import __version__
from alife_uvx.gf3 import GF3, PLUS, ERGODIC, MINUS
from alife_uvx.substrate import (
    get_substrate,
    spawn as substrate_spawn,
    walk as substrate_walk,
    status as substrate_status,
)

console = Console()


def _trit_style(trit: int) -> str:
    """Get rich style for a trit value."""
    if trit == 1:
        return "green"
    elif trit == -1:
        return "red"
    else:
        return "yellow"


@click.group(invoke_without_command=True)
@click.version_option(__version__, prog_name="alife-uvx")
@click.pass_context
def main(ctx: click.Context) -> None:
    """TrueALIFE: Self-Indexing Automata via uvx native paths.
    
    Every skill operation spawns a living cell in the substrate.
    GF(3) conservation: (+1) + (0) + (-1) ≡ 0 (mod 3)
    """
    if ctx.invoked_subcommand is None:
        # Default: show status
        ctx.invoke(status_cmd)


@main.command("status")
@click.option("--json", "as_json", is_flag=True, help="Output as JSON")
def status_cmd(as_json: bool = False) -> None:
    """Show ALife substrate status - the living skill hypergraph."""
    stat = substrate_status()
    
    if as_json:
        click.echo(json.dumps(stat, indent=2))
        return
    
    # Color based on conservation
    conserved_style = "green" if stat["gf3_conserved"] else "red"
    conserved_text = "CONSERVED ✓" if stat["gf3_conserved"] else "IMBALANCED ✗"
    
    console.print(Panel(
        f"[bold]ALife Substrate[/bold]\n\n"
        f"  Total cells:  {stat['total_cells']}\n"
        f"  Alive cells:  {stat['alive_cells']}\n"
        f"  GF(3) sum:    [{conserved_style}]{stat['gf3_sum']}[/{conserved_style}] "
        f"({conserved_text})\n"
        f"  Current:      [dim]{stat['current_hash'] or 'none'}[/dim]\n\n"
        f"[bold]Random Walk Sample:[/bold]",
        title="[cyan]🧬 TrueALIFE[/cyan]",
        border_style="cyan",
    ))
    
    if stat["random_walk_sample"]:
        table = Table(show_header=True, header_style="bold magenta")
        table.add_column("Step")
        table.add_column("Skill")
        table.add_column("Op")
        table.add_column("Trit", justify="center")
        
        for i, cell in enumerate(stat["random_walk_sample"]):
            trit = cell["trit"]
            style = _trit_style(trit)
            table.add_row(
                str(i),
                cell["skill"],
                cell["op"],
                f"[{style}]{trit:+d}[/{style}]",
            )
        
        console.print(table)
    else:
        console.print("[dim]  No cells yet - start using skills![/dim]")
    
    console.print()
    console.print("[dim]uvx alife spawn <skill> <op> --trit 1  # Spawn a cell[/dim]")
    console.print("[dim]uvx alife walk 20                      # Random walk[/dim]")


@main.command("spawn")
@click.argument("skill_id")
@click.argument("operation", default="invoke")
@click.option("--trit", "-t", default=0, type=int, help="GF(3) trit: -1, 0, +1")
@click.option("--json", "as_json", is_flag=True, help="Output as JSON")
def spawn_cmd(skill_id: str, operation: str, trit: int, as_json: bool = False) -> None:
    """Spawn a new cell in the alife substrate.
    
    Examples:
        uvx alife spawn my-skill generate --trit 1
        uvx alife spawn validator check --trit -1
    """
    cell = substrate_spawn(skill_id, operation, trit)
    
    if as_json:
        click.echo(json.dumps(cell.to_dict(), indent=2))
        return
    
    style = _trit_style(cell.trit)
    substrate = get_substrate()
    
    console.print(
        f"[bold green]✓ Spawned cell[/bold green]\n"
        f"  Hash:   [cyan]{cell.hash}[/cyan]\n"
        f"  Skill:  {cell.skill_id}\n"
        f"  Op:     {cell.operation}\n"
        f"  Trit:   [{style}]{cell.trit:+d}[/{style}] ({GF3(cell.trit).name})\n"
        f"  GF(3):  {substrate.gf3_sum} ({'✓' if substrate.is_conserved else '✗'})"
    )


@main.command("walk")
@click.argument("steps", default=10, type=int)
@click.option("--json", "as_json", is_flag=True, help="Output as JSON")
def walk_cmd(steps: int, as_json: bool = False) -> None:
    """Random walk through the alife substrate (soft-machine pattern).
    
    Each step follows parent/child links with deterministic chaos.
    """
    # Spawn cell for this walk operation
    substrate_spawn("alife-walk", "traverse", trit=0, steps=steps)
    
    path = substrate_walk(steps)
    
    if as_json:
        click.echo(json.dumps([c.to_dict() for c in path], indent=2))
        return
    
    console.print(f"[bold cyan]Random Walk ({len(path)} steps)[/bold cyan]\n")
    
    for i, cell in enumerate(path):
        style = _trit_style(cell.trit)
        age = (datetime.utcnow() - cell.timestamp).total_seconds()
        alive = "🟢" if cell.is_alive else "⚫"
        
        console.print(
            f"  {alive} {i}: [{style}]{cell.trit:+d}[/{style}] "
            f"[cyan]{cell.skill_id}[/cyan]:{cell.operation} "
            f"[dim]({cell.hash[:8]}, {age:.0f}s ago)[/dim]"
        )
    
    if not path:
        console.print("[yellow]  No path found - substrate may be empty[/yellow]")
        console.print("[dim]  Try: uvx alife spawn my-skill generate --trit 1[/dim]")


@main.command("prune")
def prune_cmd() -> None:
    """Remove dead cells (older than mixing time)."""
    substrate = get_substrate()
    count = substrate.prune_dead()
    console.print(f"[green]Pruned {count} dead cells[/green]")


@main.command("triad")
@click.argument("generator")
@click.argument("coordinator") 
@click.argument("validator")
def triad_cmd(generator: str, coordinator: str, validator: str) -> None:
    """Create a balanced GF(3) triad of cells.
    
    Spawns three cells with trits +1, 0, -1 that sum to 0.
    
    Example:
        uvx alife triad image-gen image-coord image-valid
    """
    c1 = substrate_spawn(generator, "generate", trit=PLUS)
    c2 = substrate_spawn(coordinator, "coordinate", trit=ERGODIC)
    c3 = substrate_spawn(validator, "validate", trit=MINUS)
    
    substrate = get_substrate()
    
    console.print("[bold green]✓ Created balanced triad[/bold green]\n")
    console.print(f"  [green]+1[/green] {generator}:{c1.hash[:8]}")
    console.print(f"  [yellow] 0[/yellow] {coordinator}:{c2.hash[:8]}")
    console.print(f"  [red]-1[/red] {validator}:{c3.hash[:8]}")
    console.print(f"\n  Sum: (+1) + (0) + (-1) = {substrate.gf3_sum} ✓")


if __name__ == "__main__":
    main()
