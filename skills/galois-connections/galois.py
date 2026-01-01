#!/usr/bin/env python3
"""
Galois Connections: Lawful conversions via adjoint pairs.

Based on cmk/connections (Haskell) - lifted as Python behaviors.

Usage:
    uv run galois.py floor 3.7
    uv run galois.py ceiling 3.7
    uv run galois.py round 3.5
    uv run galois.py outer "1/7"
    uv run galois.py verify
"""
# /// script
# requires-python = ">=3.11"
# dependencies = ["rich"]
# ///

from dataclasses import dataclass
from typing import TypeVar, Generic, Callable, Optional, Tuple
from fractions import Fraction
import math

from rich.console import Console
from rich.table import Table

console = Console()

P = TypeVar('P')
Q = TypeVar('Q')


@dataclass
class GaloisConnection(Generic[P, Q]):
    """
    A Galois connection between preorders P and Q.
    
    f ⊣ g means: f(x) ≤ y ⟺ x ≤ g(y)
    """
    name: str
    left: Callable[[P], Q]   # f: P → Q (floor-like, lower adjoint)
    right: Callable[[Q], P]  # g: Q → P (ceiling-like, upper adjoint)
    embed: Optional[Callable[[Q], P]] = None  # embedding if available
    
    def floor(self, x: P) -> Q:
        """Greatest lower bound: max { y : f(y) ≤ x }"""
        return self.left(x)
    
    def ceiling(self, x: P) -> Q:
        """Least upper bound: min { y : x ≤ g(y) }"""
        return self.right(x)
    
    def outer(self, x: P) -> Tuple[Q, Q]:
        """Bounding interval in target type."""
        return (self.left(x), self.right(x))
    
    def inner(self, x: P) -> Optional[Q]:
        """Exact representation if possible."""
        lo, hi = self.outer(x)
        return lo if lo == hi else None
    
    def is_exact(self, x: P) -> bool:
        """Check if x is exactly representable."""
        lo, hi = self.outer(x)
        return lo == hi


@dataclass
class AdjointString(Generic[P, Q]):
    """
    Adjoint string f ⊣ g ⊣ h for lawful rounding.
    
    Enables floor, round, ceiling, and truncate.
    """
    name: str
    floor_fn: Callable[[P], Q]    # f: left adjoint
    round_fn: Callable[[P], Q]    # g: middle (both left of h and right of f)
    ceiling_fn: Callable[[P], Q]  # h: right adjoint
    
    def floor(self, x: P) -> Q:
        return self.floor_fn(x)
    
    def ceiling(self, x: P) -> Q:
        return self.ceiling_fn(x)
    
    def round(self, x: P) -> Q:
        return self.round_fn(x)
    
    def truncate(self, x: P) -> Q:
        """Round toward zero."""
        if x >= 0:
            return self.floor_fn(x)
        else:
            return self.ceiling_fn(x)
    
    def outer(self, x: P) -> Tuple[Q, Q]:
        return (self.floor_fn(x), self.ceiling_fn(x))


# ============================================================================
# Concrete Connections
# ============================================================================

def safe_floor(x: float) -> Optional[int]:
    """Floor with NaN/Inf handling."""
    if not math.isfinite(x):
        return None
    if x > 2**63 - 1 or x < -(2**63):
        return None
    return int(math.floor(x))


def safe_ceiling(x: float) -> Optional[int]:
    """Ceiling with NaN/Inf handling."""
    if not math.isfinite(x):
        return None
    if x > 2**63 - 1 or x < -(2**63):
        return None
    return int(math.ceil(x))


def safe_round(x: float) -> Optional[int]:
    """Round with NaN/Inf handling (banker's rounding)."""
    if not math.isfinite(x):
        return None
    if x > 2**63 - 1 or x < -(2**63):
        return None
    return round(x)


# Float → Int adjoint string
FLOAT_INT = AdjointString(
    name="Float → Int",
    floor_fn=safe_floor,
    round_fn=safe_round,
    ceiling_fn=safe_ceiling,
)


def rational_floor_float(r: Fraction) -> float:
    """Floor of Rational in Float (greatest float ≤ r)."""
    f = float(r)
    if math.isfinite(f) and Fraction(f) > r:
        return math.nextafter(f, float('-inf'))
    return f


def rational_ceiling_float(r: Fraction) -> float:
    """Ceiling of Rational in Float (least float ≥ r)."""
    f = float(r)
    if math.isfinite(f) and Fraction(f) < r:
        return math.nextafter(f, float('inf'))
    return f


def rational_round_float(r: Fraction) -> float:
    """Round Rational to nearest Float."""
    return float(r)


# Rational → Float adjoint string
RATIONAL_FLOAT = AdjointString(
    name="Rational → Float",
    floor_fn=rational_floor_float,
    round_fn=rational_round_float,
    ceiling_fn=rational_ceiling_float,
)


# Ordering → Bool connection (from cmk/connections)
def ordering_to_bool_floor(o: str) -> bool:
    """f: Ordering → Bool (left adjoint)"""
    return o != "LT"


def bool_to_ordering_middle(b: bool) -> str:
    """g: Bool → Ordering (middle)"""
    return "LT" if not b else "GT"


def ordering_to_bool_ceiling(o: str) -> bool:
    """h: Ordering → Bool (right adjoint)"""
    return o == "GT"


ORDERING_BOOL = AdjointString(
    name="Ordering → Bool",
    floor_fn=ordering_to_bool_floor,
    round_fn=lambda o: ordering_to_bool_floor(o),  # same as floor for this
    ceiling_fn=ordering_to_bool_ceiling,
)


# ============================================================================
# Verification
# ============================================================================

def verify_adjunction(
    f: Callable, g: Callable,
    test_points_p: list, test_points_q: list,
    le_p: Callable = lambda a, b: a <= b,
    le_q: Callable = lambda a, b: a <= b,
) -> list:
    """
    Verify adjunction property: f(x) ≤ y ⟺ x ≤ g(y)
    
    Returns list of violations.
    """
    violations = []
    for x in test_points_p:
        for y in test_points_q:
            fx = f(x)
            gy = g(y)
            if fx is None or gy is None:
                continue
            
            left_holds = le_q(fx, y)
            right_holds = le_p(x, gy)
            
            if left_holds != right_holds:
                violations.append({
                    "x": x, "y": y,
                    "f(x)": fx, "g(y)": gy,
                    "f(x)≤y": left_holds,
                    "x≤g(y)": right_holds,
                })
    
    return violations


def verify_float_int():
    """Verify Float → Int adjoint string."""
    test_floats = [-2.5, -2.0, -1.5, -1.0, -0.5, 0.0, 0.5, 1.0, 1.5, 2.0, 2.5]
    test_ints = list(range(-3, 4))
    
    console.print("[bold]Verifying Float → Int adjunction...[/bold]")
    
    # Verify f ⊣ g (floor ⊣ embed)
    violations = verify_adjunction(
        FLOAT_INT.floor_fn,
        lambda i: float(i),  # embed
        test_floats,
        test_ints,
    )
    
    if violations:
        console.print(f"[red]Found {len(violations)} violations![/red]")
        for v in violations[:5]:
            console.print(f"  {v}")
    else:
        console.print("[green]✓ floor ⊣ embed verified[/green]")
    
    return len(violations) == 0


def verify_ordering_bool():
    """Verify Ordering → Bool adjoint string."""
    orderings = ["LT", "EQ", "GT"]
    bools = [False, True]
    
    console.print("[bold]Verifying Ordering → Bool adjunction...[/bold]")
    
    # Custom ordering on Ordering
    ord_le = lambda a, b: orderings.index(a) <= orderings.index(b)
    
    violations = verify_adjunction(
        ORDERING_BOOL.floor_fn,
        bool_to_ordering_middle,
        orderings,
        bools,
        le_p=ord_le,
    )
    
    if violations:
        console.print(f"[red]Found {len(violations)} violations![/red]")
        for v in violations:
            console.print(f"  {v}")
    else:
        console.print("[green]✓ ordbin verified[/green]")
    
    return len(violations) == 0


# ============================================================================
# Display
# ============================================================================

def display_connections():
    """Display available Galois connections."""
    table = Table(title="🔗 Available Galois Connections")
    table.add_column("Name", style="bold")
    table.add_column("Source", style="cyan")
    table.add_column("Target", style="green")
    table.add_column("Operations")
    
    table.add_row("Float → Int", "float", "int", "floor, ceiling, round, truncate")
    table.add_row("Rational → Float", "Fraction", "float", "floor, ceiling, round")
    table.add_row("Ordering → Bool", "LT|EQ|GT", "bool", "floor, ceiling")
    
    console.print(table)


def display_example(x: float):
    """Show all conversions for a value."""
    table = Table(title=f"🔢 Conversions for {x}")
    table.add_column("Operation", style="bold")
    table.add_column("Result", style="cyan")
    table.add_column("Description")
    
    table.add_row("floor", str(FLOAT_INT.floor(x)), "Greatest int ≤ x")
    table.add_row("ceiling", str(FLOAT_INT.ceiling(x)), "Least int ≥ x")
    table.add_row("round", str(FLOAT_INT.round(x)), "Nearest int (banker's)")
    table.add_row("truncate", str(FLOAT_INT.truncate(x)), "Round toward zero")
    table.add_row("outer", str(FLOAT_INT.outer(x)), "Bounding interval")
    
    console.print(table)


def display_rational_example(r_str: str):
    """Show Rational → Float conversions."""
    try:
        if "/" in r_str:
            num, den = r_str.split("/")
            r = Fraction(int(num), int(den))
        else:
            r = Fraction(r_str)
    except:
        console.print(f"[red]Cannot parse '{r_str}' as rational[/red]")
        return
    
    table = Table(title=f"🔢 Rational {r} → Float")
    table.add_column("Operation", style="bold")
    table.add_column("Result", style="cyan")
    table.add_column("Exact?")
    
    lo = RATIONAL_FLOAT.floor(r)
    hi = RATIONAL_FLOAT.ceiling(r)
    mid = RATIONAL_FLOAT.round(r)
    
    table.add_row("floor", f"{lo:.15g}", "")
    table.add_row("round", f"{mid:.15g}", "✓" if Fraction(mid) == r else "")
    table.add_row("ceiling", f"{hi:.15g}", "")
    table.add_row("outer", f"({lo:.15g}, {hi:.15g})", "✓" if lo == hi else "interval")
    
    console.print(table)
    
    # Show exactness analysis
    if Fraction(mid) == r:
        console.print(f"[green]✓ {r} is exactly representable as {mid}[/green]")
    else:
        console.print(f"[yellow]⚠ {r} is NOT exactly representable[/yellow]")
        console.print(f"  Represented as: {Fraction(mid)}")
        console.print(f"  Error: {float(r - Fraction(mid)):.2e}")


if __name__ == "__main__":
    import sys
    
    if len(sys.argv) < 2:
        console.print("[bold]Galois Connections[/bold]")
        console.print()
        console.print("Commands:")
        console.print("  list              - Show available connections")
        console.print("  floor X           - Floor of X (float → int)")
        console.print("  ceiling X         - Ceiling of X")
        console.print("  round X           - Round X (banker's)")
        console.print("  truncate X        - Truncate X (toward zero)")
        console.print("  outer X           - Show bounding interval")
        console.print("  all X             - Show all conversions")
        console.print("  rational R        - Rational R → Float analysis")
        console.print("  verify            - Verify adjunction properties")
        sys.exit(0)
    
    cmd = sys.argv[1]
    
    if cmd == "list":
        display_connections()
    elif cmd == "floor" and len(sys.argv) > 2:
        x = float(sys.argv[2])
        console.print(f"floor({x}) = {FLOAT_INT.floor(x)}")
    elif cmd == "ceiling" and len(sys.argv) > 2:
        x = float(sys.argv[2])
        console.print(f"ceiling({x}) = {FLOAT_INT.ceiling(x)}")
    elif cmd == "round" and len(sys.argv) > 2:
        x = float(sys.argv[2])
        console.print(f"round({x}) = {FLOAT_INT.round(x)}")
    elif cmd == "truncate" and len(sys.argv) > 2:
        x = float(sys.argv[2])
        console.print(f"truncate({x}) = {FLOAT_INT.truncate(x)}")
    elif cmd == "outer" and len(sys.argv) > 2:
        x = float(sys.argv[2])
        console.print(f"outer({x}) = {FLOAT_INT.outer(x)}")
    elif cmd == "all" and len(sys.argv) > 2:
        x = float(sys.argv[2])
        display_example(x)
    elif cmd == "rational" and len(sys.argv) > 2:
        display_rational_example(sys.argv[2])
    elif cmd == "verify":
        ok1 = verify_float_int()
        ok2 = verify_ordering_bool()
        if ok1 and ok2:
            console.print("[bold green]All adjunctions verified![/bold green]")
        else:
            console.print("[bold red]Some adjunctions failed![/bold red]")
            sys.exit(1)
    else:
        console.print(f"[red]Unknown command: {cmd}[/red]")
