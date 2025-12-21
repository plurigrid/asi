#!/usr/bin/env python3
"""
CODEX-GAY Color Operator Algebra - Command Line Interface
Query and explore the saturated color algebra from the terminal
"""

import sys
import json
from codex_gay_integration import CodexGayIntegration
from pathlib import Path


def print_color(color: dict, width: int = 70) -> None:
    """Pretty print a color entry"""
    hex_val = color.get('hex', 'N/A')
    cycle = color.get('cycle', '?')
    rgb = color.get('rgb', {})
    l = color.get('L', 0)
    c = color.get('C', 0)
    h = color.get('H', 0)

    # ANSI color background for hex display
    r = int(rgb.get('r', 0) * 255)
    g = int(rgb.get('g', 0) * 255)
    b = int(rgb.get('b', 0) * 255)

    # Determine if text should be light or dark
    brightness = (0.299 * r + 0.587 * g + 0.114 * b) / 255
    text_color = '37' if brightness < 0.5 else '30'

    color_box = f"\033[48;2;{r};{g};{b};{text_color}m {hex_val} \033[0m"

    print(f"  {color_box}")
    print(f"    Cycle: {cycle}")
    print(f"    LCH: L={l:7.2f}  C={c:7.2f}  H={h:7.2f}°")
    print(f"    RGB: R={rgb.get('r', 0):.3f}  G={rgb.get('g', 0):.3f}  B={rgb.get('b', 0):.3f}")


def cmd_color(args: list, integration: CodexGayIntegration) -> None:
    """Get a specific color by index: color <index>"""
    if not args:
        print("Usage: color <index>")
        return

    try:
        index = int(args[0])
        color = integration.get_color(index)
        if color:
            print(f"\nColor[{index}]:")
            print_color(color)
        else:
            print(f"✗ Color index {index} not found (valid range: 0-35)")
    except ValueError:
        print(f"✗ Invalid index: {args[0]} (must be integer)")


def cmd_range(args: list, integration: CodexGayIntegration) -> None:
    """Get colors in range: range <start> <end>"""
    if len(args) < 2:
        print("Usage: range <start> <end>")
        return

    try:
        start = int(args[0])
        end = int(args[1])
        colors = integration.get_colors_in_range(start, end)
        print(f"\nColors [{start}:{end}] ({len(colors)} colors):\n")
        for color in colors:
            print(f"  {color['hex']:7s}  L={color['L']:6.2f}  C={color['C']:6.2f}  H={color['H']:7.2f}°")
    except ValueError:
        print("✗ Invalid range (must be integers)")


def cmd_search(args: list, integration: CodexGayIntegration) -> None:
    """Search for colors: search <hex|lightness|chroma|hue> <criteria>"""
    if not args:
        print("Usage: search hex <#XXXXXX>")
        print("       search lightness <min> <max>")
        print("       search chroma <min> <max>")
        print("       search hue <min> <max>")
        return

    search_type = args[0].lower()

    if search_type == 'hex' and len(args) > 1:
        color = integration.get_color_by_hex(args[1])
        if color:
            print(f"\nFound: {color['hex']}")
            print_color(color)
        else:
            print(f"✗ No color found with hex {args[1]}")

    elif search_type == 'lightness' and len(args) > 2:
        try:
            min_l = float(args[1])
            max_l = float(args[2])
            colors = integration.get_colors_by_lightness_range(min_l, max_l)
            print(f"\nFound {len(colors)} colors with L in [{min_l}, {max_l}]:\n")
            for color in colors:
                print(f"  {color['hex']:7s}  L={color['L']:6.2f}  C={color['C']:6.2f}  H={color['H']:7.2f}°")
        except ValueError:
            print("✗ Invalid range (must be numbers)")

    elif search_type == 'chroma' and len(args) > 2:
        try:
            min_c = float(args[1])
            max_c = float(args[2])
            colors = integration.get_colors_by_chroma_range(min_c, max_c)
            print(f"\nFound {len(colors)} colors with C in [{min_c}, {max_c}]:\n")
            for color in colors:
                print(f"  {color['hex']:7s}  L={color['L']:6.2f}  C={color['C']:6.2f}  H={color['H']:7.2f}°")
        except ValueError:
            print("✗ Invalid range (must be numbers)")

    elif search_type == 'hue' and len(args) > 2:
        try:
            min_h = float(args[1])
            max_h = float(args[2])
            colors = integration.get_colors_by_hue_range(min_h, max_h)
            print(f"\nFound {len(colors)} colors with H in [{min_h}, {max_h}]:\n")
            for color in colors:
                print(f"  {color['hex']:7s}  L={color['L']:6.2f}  C={color['C']:6.2f}  H={color['H']:7.2f}°")
        except ValueError:
            print("✗ Invalid range (must be numbers)")
    else:
        print("✗ Unknown search type or missing arguments")


def cmd_bright(args: list, integration: CodexGayIntegration) -> None:
    """Get bright colors: bright [threshold=80]"""
    threshold = float(args[0]) if args else 80.0
    colors = integration.get_colors_by_lightness_range(threshold, 100)
    print(f"\nBright colors (L ≥ {threshold}): {len(colors)} colors\n")
    for color in colors:
        print(f"  {color['hex']:7s}  L={color['L']:6.2f}  C={color['C']:6.2f}  H={color['H']:7.2f}°")


def cmd_dark(args: list, integration: CodexGayIntegration) -> None:
    """Get dark colors: dark [threshold=20]"""
    threshold = float(args[0]) if args else 20.0
    colors = integration.get_colors_by_lightness_range(0, threshold)
    print(f"\nDark colors (L ≤ {threshold}): {len(colors)} colors\n")
    for color in colors:
        print(f"  {color['hex']:7s}  L={color['L']:6.2f}  C={color['C']:6.2f}  H={color['H']:7.2f}°")


def cmd_saturated(args: list, integration: CodexGayIntegration) -> None:
    """Get highly saturated colors: saturated [threshold=70]"""
    threshold = float(args[0]) if args else 70.0
    colors = integration.get_colors_by_chroma_range(threshold, 100)
    print(f"\nHighly saturated colors (C ≥ {threshold}): {len(colors)} colors\n")
    for color in colors:
        print(f"  {color['hex']:7s}  L={color['L']:6.2f}  C={color['C']:6.2f}  H={color['H']:7.2f}°")


def cmd_desaturated(args: list, integration: CodexGayIntegration) -> None:
    """Get desaturated colors: desaturated [threshold=30]"""
    threshold = float(args[0]) if args else 30.0
    colors = integration.get_colors_by_chroma_range(0, threshold)
    print(f"\nDesaturated colors (C ≤ {threshold}): {len(colors)} colors\n")
    for color in colors:
        print(f"  {color['hex']:7s}  L={color['L']:6.2f}  C={color['C']:6.2f}  H={color['H']:7.2f}°")


def cmd_similar(args: list, integration: CodexGayIntegration) -> None:
    """Find similar colors: similar <index> [threshold=0.2]"""
    if not args:
        print("Usage: similar <index> [threshold=0.2]")
        return

    try:
        index = int(args[0])
        threshold = float(args[1]) if len(args) > 1 else 0.2
        similar = integration.get_similar_colors(index, threshold)
        print(f"\nColors similar to Color[{index}] (distance < {threshold}):\n")
        for match in similar:
            color = match['color']
            print(f"  {color['hex']:7s}  Distance={match['distance']:.3f}  "
                  f"L={color['L']:6.2f}  C={color['C']:6.2f}  H={color['H']:7.2f}°")
    except ValueError:
        print("✗ Invalid arguments")


def cmd_complementary(args: list, integration: CodexGayIntegration) -> None:
    """Find complementary color: complementary <index>"""
    if not args:
        print("Usage: complementary <index>")
        return

    try:
        index = int(args[0])
        comp = integration.get_complementary_color(index)
        if comp:
            source = integration.get_color(index)
            print(f"\nComplementary color for Color[{index}]:")
            print(f"  Source: {source['hex']} (H={source['H']:.2f}°)")
            print(f"  Complement: {comp['hex']} (H={comp['H']:.2f}°)")
            print_color(comp)
        else:
            print(f"✗ Could not find complementary color for index {index}")
    except ValueError:
        print("✗ Invalid index")


def cmd_stats(args: list, integration: CodexGayIntegration) -> None:
    """Show statistics: stats [all|coverage|saturation|hue]"""
    stat_type = args[0].lower() if args else 'all'

    if stat_type in ('all', 'coverage'):
        print("\n" + "─"*70)
        print("COLOR SPACE COVERAGE")
        print("─"*70)
        coverage = integration.get_color_space_coverage()
        for space in ['lightness', 'chroma', 'hue']:
            c = coverage[space]
            print(f"{space.upper():10s}: [{c['min']:7.2f}, {c['max']:7.2f}]  "
                  f"range={c['range']:7.2f}  mean={c['mean']:7.2f}")

    if stat_type in ('all', 'saturation'):
        print("\n" + "─"*70)
        print("SATURATION ANALYSIS")
        print("─"*70)
        sat = integration.get_saturation_metrics()
        print(f"Total colors: {sat['total_colors']}")
        print(f"  High saturation (C>60):    {sat['high_saturation_count']:2d} colors")
        print(f"  Medium saturation (30-60): {sat['medium_saturation_count']:2d} colors")
        print(f"  Low saturation (C<30):     {sat['low_saturation_count']:2d} colors")
        print(f"Average chroma: {sat['mean_chroma']:.2f}")

    if stat_type in ('all', 'hue'):
        print("\n" + "─"*70)
        print("HUE DISTRIBUTION")
        print("─"*70)
        hue = integration.get_hue_distribution()
        for region, count in hue['regions'].items():
            print(f"  {region.capitalize():6s}: {count:2d} colors")
        print(f"\nStatus: {hue['coverage_status']}")


def cmd_bifurcation(args: list, integration: CodexGayIntegration) -> None:
    """Show bifurcation structure: bifurcation"""
    info = integration.get_bifurcation_info()
    avg = integration.get_bifurcation_averages()

    print("\n" + "─"*70)
    print("BIFURCATION STRUCTURE")
    print("─"*70)
    print(f"Bifurcation depth: {info['depth']}")
    print(f"Total nodes: {info['total_nodes']}")
    print(f"Total operators: {info['total_operators']} (3 per node)")
    print(f"Total entropy: {info['total_entropy_bits']:.4f} bits")

    root = avg.get('root', {})
    print(f"\nRoot average: RGB({root.get('r', 0):.3f}, {root.get('g', 0):.3f}, {root.get('b', 0):.3f})")

    print(f"\nLevel 1 branches (3 bifurcations):")
    for branch in avg.get('level_1', []):
        print(f"  Branch {branch['node']:3s}: {branch['color_count']:2d} colors, "
              f"avg chroma: {branch['avg_chroma']:6.2f}")


def cmd_all(args: list, integration: CodexGayIntegration) -> None:
    """Show all colors: all"""
    print("\nAll 36 colors in the chain:\n")
    for i, color in enumerate(integration.colors):
        print(f"[{i:2d}] {color['hex']:7s}  L={color['L']:6.2f}  C={color['C']:6.2f}  H={color['H']:7.2f}°")


def cmd_help(args: list = None, integration: CodexGayIntegration = None) -> None:
    """Show help: help [command]"""
    if args:
        cmd = args[0].lower()
        help_text = {
            'color': 'Get a specific color by index\n         Usage: color <index>',
            'range': 'Get colors in a range\n         Usage: range <start> <end>',
            'search': 'Search for colors\n         Usage: search hex <#XXXXXX>\n                search lightness <min> <max>\n                search chroma <min> <max>\n                search hue <min> <max>',
            'bright': 'Get bright colors\n         Usage: bright [threshold=80]',
            'dark': 'Get dark colors\n         Usage: dark [threshold=20]',
            'saturated': 'Get saturated colors\n         Usage: saturated [threshold=70]',
            'desaturated': 'Get desaturated colors\n         Usage: desaturated [threshold=30]',
            'similar': 'Find similar colors\n         Usage: similar <index> [threshold=0.2]',
            'complementary': 'Find complementary color\n         Usage: complementary <index>',
            'stats': 'Show statistics\n         Usage: stats [all|coverage|saturation|hue]',
            'bifurcation': 'Show bifurcation structure\n         Usage: bifurcation',
            'all': 'Show all colors\n         Usage: all',
        }
        if cmd in help_text:
            print(f"\n{cmd.upper()}: {help_text[cmd]}")
        else:
            print(f"✗ Unknown command: {cmd}")
    else:
        print("""
╔══════════════════════════════════════════════════════════════════════╗
║                CODEX-GAY CLI - COMMAND REFERENCE                    ║
╚══════════════════════════════════════════════════════════════════════╝

NAVIGATION:
  color <index>              Get a specific color
  range <start> <end>        Get colors in range
  all                        Show all 36 colors

SEARCH:
  search hex <#XXXXXX>       Find color by hex value
  search lightness <min> <max>  Find colors by lightness
  search chroma <min> <max>     Find colors by saturation
  search hue <min> <max>        Find colors by hue

QUICK FILTERS:
  bright [threshold=80]      Get bright colors
  dark [threshold=20]        Get dark colors
  saturated [threshold=70]   Get highly saturated colors
  desaturated [threshold=30] Get desaturated colors

ANALYSIS:
  similar <index> [threshold]  Find similar colors
  complementary <index>        Find complementary color
  stats [type]               Show statistics
  bifurcation                Show bifurcation structure

OTHER:
  help [command]             Show this help or command-specific help
  quit/exit                  Exit the program

EXAMPLES:
  color 18                   Get color at index 18
  range 0 11                 Get first 12 colors
  search lightness 80 100    Get bright colors (90-100)
  saturated 60               Get colors with C≥60
  similar 5 0.15             Find colors like index 5
  stats coverage             Show lightness/chroma/hue coverage
        """)


def main():
    """Interactive CLI"""
    print("\n" + "╔" + "═"*70 + "╗")
    print("║" + " "*15 + "CODEX-GAY COLOR OPERATOR ALGEBRA CLI" + " "*19 + "║")
    print("╚" + "═"*70 + "╝\n")

    try:
        integration = CodexGayIntegration()
        print(f"✓ Loaded {len(integration.colors)} colors")
        print(f"✓ Bifurcation nodes: {integration.get_bifurcation_info()['total_nodes']}")
        print(f"✓ Total entropy: {integration.get_bifurcation_info()['total_entropy_bits']:.4f} bits\n")
        print("Type 'help' for commands or 'quit' to exit.\n")
    except FileNotFoundError as e:
        print(f"✗ {e}")
        return

    commands = {
        'color': cmd_color,
        'range': cmd_range,
        'search': cmd_search,
        'bright': cmd_bright,
        'dark': cmd_dark,
        'saturated': cmd_saturated,
        'desaturated': cmd_desaturated,
        'similar': cmd_similar,
        'complementary': cmd_complementary,
        'stats': cmd_stats,
        'bifurcation': cmd_bifurcation,
        'all': cmd_all,
        'help': cmd_help,
    }

    while True:
        try:
            line = input("codex-gay> ").strip()
            if not line:
                continue

            parts = line.split()
            cmd = parts[0].lower()
            args = parts[1:] if len(parts) > 1 else []

            if cmd in ('quit', 'exit'):
                print("\n✓ Goodbye!")
                break
            elif cmd in commands:
                commands[cmd](args, integration)
            else:
                print(f"✗ Unknown command: {cmd} (type 'help' for commands)")

        except KeyboardInterrupt:
            print("\n\n✓ Interrupted")
            break
        except Exception as e:
            print(f"✗ Error: {e}")


if __name__ == "__main__":
    main()
