#!/usr/bin/env python3
"""
Copy-on-Interact MCP Server: Live thread attachments with bidirectional GitHub sync.

Tools:
- coi_interact: Trigger copy-on-interact with a GitHub URL
- coi_link_threads: Create bidirectional thread links
- coi_cobordisms: Find shared boundaries between repo communities
- coi_summary: Get interaction summary with GF(3) verification
"""
# /// script
# requires-python = ">=3.11"  
# dependencies = ["fastmcp>=0.4", "rich"]
# ///

from fastmcp import FastMCP
from copy_on_interact import (
    CopyOnInteractState, 
    InteractionType,
    Trit,
)
import json

mcp = FastMCP("copy-on-interact")

# Global state with Gay.jl seed
STATE = CopyOnInteractState(seed=0x42D)


@mcp.tool()
def coi_interact(url: str, interaction_type: str = "mention") -> dict:
    """
    Trigger copy-on-interact with a GitHub URL.
    
    Args:
        url: GitHub URL (repo, issue, PR, commit)
        interaction_type: fork|pr|issue|mention|star|review
    
    Returns:
        Interaction record with color and trit
    """
    try:
        itype = InteractionType(interaction_type.lower())
    except ValueError:
        itype = InteractionType.MENTION
    
    interaction = STATE.on_interact(url, itype)
    if not interaction:
        return {"error": f"Could not parse URL: {url}"}
    
    return {
        "id": interaction.id,
        "url": interaction.url,
        "type": interaction.type.value,
        "trit": {-1: "⊖ MINUS", 0: "○ ERGODIC", 1: "⊕ PLUS"}[interaction.trit.value],
        "color": interaction.color.to_css(),
        "timestamp": interaction.timestamp,
    }


@mcp.tool()
def coi_link_threads(thread_a: str, thread_b: str) -> dict:
    """
    Create bidirectional link between two threads.
    
    Args:
        thread_a: First thread ID (e.g., "T-001")
        thread_b: Second thread ID (e.g., "T-002")
    
    Returns:
        Forward and backward link records
    """
    fwd, bwd = STATE.create_bidirectional_link(thread_a, thread_b)
    
    return {
        "forward": {
            "from": thread_a,
            "to": thread_b,
            "color": fwd.color.to_css(),
        },
        "backward": {
            "from": thread_b,
            "to": thread_a,
            "color": bwd.color.to_css(),
        },
        "gf3_conserved": STATE.verify_gf3_conservation(),
    }


@mcp.tool()
def coi_cobordisms() -> dict:
    """
    Find shared boundaries between different repo communities.
    
    Returns:
        List of cobordisms (shared interactions between repos)
    """
    cobordisms = STATE.find_cobordisms()
    return {
        "cobordisms": cobordisms,
        "total_repos": len(STATE.remote_refs),
        "bridge_strength": sum(c["shared_count"] for c in cobordisms),
    }


@mcp.tool()
def coi_summary() -> dict:
    """
    Get interaction summary with GF(3) verification.
    
    Returns:
        Summary statistics and conservation status
    """
    return STATE.summary()


@mcp.tool()
def coi_export_acset() -> dict:
    """
    Export current state as ACSet-compatible JSON.
    
    Returns:
        ACSet schema and data tables
    """
    return STATE.export_acset_json()


@mcp.tool()
def coi_reset(seed: int = 0x42D) -> dict:
    """
    Reset state with new seed.
    
    Args:
        seed: New SplitMix64 seed (default: 0x42D)
    
    Returns:
        Confirmation with new seed
    """
    global STATE
    STATE = CopyOnInteractState(seed=seed)
    return {"status": "reset", "seed": hex(seed)}


if __name__ == "__main__":
    mcp.run()
