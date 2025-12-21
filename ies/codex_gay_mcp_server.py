#!/usr/bin/env python3
"""
CODEX-RS + GAY.JL COLOR OPERATOR ALGEBRA MCP SERVER
Exposes color algebra skills as MCP resources and tools
"""

import json
import asyncio
from typing import Any
from pathlib import Path

class CodexGayMCPServer:
    """MCP Server for codex-rs color operator algebra integration"""

    def __init__(self):
        self.color_export_path = Path("/Users/bob/ies/codex_gay_color_export.json")
        self.algebra_data = self._load_algebra_data()

    def _load_algebra_data(self) -> dict:
        """Load the serialized color algebra from Julia export"""
        if self.color_export_path.exists():
            with open(self.color_export_path) as f:
                return json.load(f)
        return {}

    async def initialize(self):
        """Initialize the MCP server resources"""
        print("╔════════════════════════════════════════════════════════════════╗")
        print("║   CODEX-RS MCP SERVER - GAY.JL COLOR OPERATOR ALGEBRA        ║")
        print("╚════════════════════════════════════════════════════════════════╝\n")

        if not self.algebra_data:
            print("✗ Failed to load color algebra data")
            return False

        print("✓ Loaded color algebra data")
        print(f"  Genesis: {self.algebra_data.get('genesis', {}).get('prompt', 'Unknown')}")
        print(f"  Algorithm: {self.algebra_data.get('genesis', {}).get('algorithm', 'Unknown')}")
        print(f"  Total colors: {len(self.algebra_data.get('colors', []))}")
        print(f"  Bifurcation nodes: {self.algebra_data.get('algebra', {}).get('total_nodes', 0)}")
        print(f"  Total entropy: {self.algebra_data.get('algebra', {}).get('total_entropy', 0):.4f} bits")

        return True

    def get_color_at_index(self, index: int) -> dict:
        """Get color data for a specific cycle index"""
        colors = self.algebra_data.get('colors', [])
        if 0 <= index < len(colors):
            return colors[index]
        return {}

    def get_bifurcation_averages(self) -> dict:
        """Get the 3-per-bifurcation color averages"""
        return self.algebra_data.get('bifurcation_averages', {})

    def list_resources(self) -> list:
        """List all available MCP resources"""
        resources = [
            {
                "name": "color-algebra/genesis",
                "description": "Genesis information for the color algebra system",
                "data": self.algebra_data.get('genesis', {})
            },
            {
                "name": "color-algebra/structure",
                "description": "Bifurcation structure and operator information",
                "data": self.algebra_data.get('algebra', {})
            },
            {
                "name": "color-algebra/colors",
                "description": "Complete 36-cycle color chain with LCH and RGB values",
                "data": self.algebra_data.get('colors', [])
            },
            {
                "name": "color-algebra/bifurcation-averages",
                "description": "3-per-bifurcation color averaging results",
                "data": self.get_bifurcation_averages()
            }
        ]
        return resources

    def list_tools(self) -> list:
        """List all available MCP tools"""
        tools = [
            {
                "name": "get_color",
                "description": "Get color data for a specific cycle index",
                "inputSchema": {
                    "type": "object",
                    "properties": {
                        "index": {
                            "type": "integer",
                            "description": "Cycle index (0-35)"
                        }
                    },
                    "required": ["index"]
                }
            },
            {
                "name": "get_bifurcation_stats",
                "description": "Get statistics for bifurcation nodes",
                "inputSchema": {
                    "type": "object",
                    "properties": {
                        "level": {
                            "type": "integer",
                            "description": "Bifurcation level (1-3)",
                            "default": 1
                        }
                    }
                }
            },
            {
                "name": "entropy_analysis",
                "description": "Get entropy analysis results",
                "inputSchema": {
                    "type": "object",
                    "properties": {}
                }
            },
            {
                "name": "color_space_coverage",
                "description": "Get color space coverage statistics",
                "inputSchema": {
                    "type": "object",
                    "properties": {}
                }
            }
        ]
        return tools

    async def call_tool(self, tool_name: str, arguments: dict) -> Any:
        """Call a tool with the given arguments"""
        if tool_name == "get_color":
            return self.get_color_at_index(arguments.get("index", 0))

        elif tool_name == "get_bifurcation_stats":
            level = arguments.get("level", 1)
            averages = self.get_bifurcation_averages()
            if level == 1:
                return averages.get("level_1", [])
            return {}

        elif tool_name == "entropy_analysis":
            algebra = self.algebra_data.get("algebra", {})
            return {
                "total_entropy": algebra.get("total_entropy", 0),
                "bifurcation_depth": algebra.get("bifurcation_depth", 0),
                "total_nodes": algebra.get("total_nodes", 0),
                "total_operators": algebra.get("total_operators", 0)
            }

        elif tool_name == "color_space_coverage":
            # Analyze color space coverage from the color data
            colors = self.algebra_data.get('colors', [])
            if not colors:
                return {}

            lightness = [c.get('L', 0) for c in colors]
            chroma = [c.get('C', 0) for c in colors]
            hue = [c.get('H', 0) for c in colors]

            return {
                "lightness": {
                    "min": min(lightness),
                    "max": max(lightness),
                    "range": max(lightness) - min(lightness)
                },
                "chroma": {
                    "min": min(chroma),
                    "max": max(chroma),
                    "range": max(chroma) - min(chroma)
                },
                "hue": {
                    "min": min(hue),
                    "max": max(hue),
                    "range": max(hue) - min(hue)
                }
            }

        return {"error": f"Unknown tool: {tool_name}"}

    def get_status(self) -> dict:
        """Get server status"""
        algebra = self.algebra_data.get('algebra', {})
        return {
            "status": "ready",
            "name": "codex-gay-mcp",
            "version": "0.1.0",
            "capabilities": {
                "colors_available": len(self.algebra_data.get('colors', [])),
                "bifurcation_nodes": algebra.get('total_nodes', 0),
                "operators": algebra.get('total_operators', 0),
                "total_entropy_bits": algebra.get('total_entropy', 0)
            }
        }


async def main():
    """Main entry point for MCP server"""
    server = CodexGayMCPServer()

    # Initialize the server
    success = await server.initialize()
    if not success:
        print("Failed to initialize MCP server")
        return

    # Display available resources
    print("\n╔════════════════════════════════════════════════════════════════╗")
    print("║                    AVAILABLE RESOURCES                       ║")
    print("╚════════════════════════════════════════════════════════════════╝\n")

    for resource in server.list_resources():
        print(f"✓ {resource['name']}")
        print(f"  {resource['description']}")

    # Display available tools
    print("\n╔════════════════════════════════════════════════════════════════╗")
    print("║                      AVAILABLE TOOLS                         ║")
    print("╚════════════════════════════════════════════════════════════════╝\n")

    for tool in server.list_tools():
        print(f"✓ {tool['name']}")
        print(f"  {tool['description']}")

    # Demonstrate tool usage
    print("\n╔════════════════════════════════════════════════════════════════╗")
    print("║                    DEMONSTRATION CALLS                       ║")
    print("╚════════════════════════════════════════════════════════════════╝\n")

    # Get a color
    color = await server.call_tool("get_color", {"index": 0})
    print("✓ get_color(0):")
    if color:
        print(f"  Hex: {color.get('hex')}")
        print(f"  L={color.get('L'):.2f} C={color.get('C'):.2f} H={color.get('H'):.2f}")

    # Get entropy analysis
    entropy = await server.call_tool("entropy_analysis", {})
    print("\n✓ entropy_analysis():")
    print(f"  Total entropy: {entropy.get('total_entropy', 0):.4f} bits")
    print(f"  Total nodes: {entropy.get('total_nodes', 0)}")

    # Get color space coverage
    coverage = await server.call_tool("color_space_coverage", {})
    print("\n✓ color_space_coverage():")
    print(f"  Lightness range: [{coverage['lightness']['min']:.2f}, {coverage['lightness']['max']:.2f}]")
    print(f"  Chroma range: [{coverage['chroma']['min']:.2f}, {coverage['chroma']['max']:.2f}]")
    print(f"  Hue range: [{coverage['hue']['min']:.2f}, {coverage['hue']['max']:.2f}]")

    # Show server status
    print("\n╔════════════════════════════════════════════════════════════════╗")
    print("║                      SERVER STATUS                           ║")
    print("╚════════════════════════════════════════════════════════════════╝\n")

    status = server.get_status()
    print(f"Status: {status['status']}")
    print(f"Name: {status['name']}")
    print(f"Version: {status['version']}")
    print(f"Colors available: {status['capabilities']['colors_available']}")
    print(f"Bifurcation nodes: {status['capabilities']['bifurcation_nodes']}")
    print(f"Total operators: {status['capabilities']['operators']}")
    print(f"Total entropy: {status['capabilities']['total_entropy_bits']:.4f} bits")

    print("\n✓ MCP Server ready for codex-rs integration")
    print("  To use with codex-rs, configure as MCP resource server")


if __name__ == "__main__":
    asyncio.run(main())
