---
name: mcp-fastpath
description: Direct FastMCP tool registration bypassing workflow wrappers. Addresses
  lastmile-ai/mcp-agent timeout issues.
source: lastmile-ai/mcp-agent#603 + modelcontextprotocol/servers + GitHub research
license: MIT
gf3_category: PLUS
---

# MCP Fastpath Skill

> **Addresses**: [mcp-agent #603](https://github.com/lastmile-ai/mcp-agent/issues/603) (workflow wrapper timeouts), [#564](https://github.com/lastmile-ai/mcp-agent/issues/564) (BrokenResourceError)

## Problem Statement

The `MCPApp` workflow wrappers in mcp-agent introduce:
1. **Timeout issues** with long-running tools
2. **BrokenResourceError** in stdio transport
3. **Complexity overhead** for simple tool registrations

**Solution**: Use FastMCP directly for lightweight, reliable tool serving.

## FastMCP Direct Pattern

```python
from mcp.server.fastmcp import FastMCP
from mcp.types import Tool, TextContent
import asyncio

# Initialize without workflow wrappers
mcp = FastMCP("asi-tools")

@mcp.tool()
async def sheaf_laplacian(
    node_features: list[list[float]],
    edge_index: list[list[int]],
    stalk_dim: int = 4,
) -> dict:
    """
    Compute sheaf Laplacian for distributed coordination.
    
    Args:
        node_features: Node feature matrix [n_nodes, feature_dim]
        edge_index: Edge connectivity [2, n_edges]
        stalk_dim: Dimension of stalks over edges
    
    Returns:
        Dictionary with Laplacian eigenvalues and coordination score
    """
    import numpy as np
    
    n_nodes = len(node_features)
    n_edges = len(edge_index[0])
    
    # Build sheaf Laplacian (simplified)
    L = np.zeros((n_nodes * stalk_dim, n_nodes * stalk_dim))
    
    for i, (src, tgt) in enumerate(zip(edge_index[0], edge_index[1])):
        # Identity restriction maps (can be learned)
        F_src = np.eye(stalk_dim)
        F_tgt = np.eye(stalk_dim)
        
        # Add to Laplacian
        L[src*stalk_dim:(src+1)*stalk_dim, src*stalk_dim:(src+1)*stalk_dim] += F_src.T @ F_src
        L[tgt*stalk_dim:(tgt+1)*stalk_dim, tgt*stalk_dim:(tgt+1)*stalk_dim] += F_tgt.T @ F_tgt
        L[src*stalk_dim:(src+1)*stalk_dim, tgt*stalk_dim:(tgt+1)*stalk_dim] -= F_src.T @ F_tgt
        L[tgt*stalk_dim:(tgt+1)*stalk_dim, src*stalk_dim:(src+1)*stalk_dim] -= F_tgt.T @ F_src
    
    eigenvalues = np.linalg.eigvalsh(L)
    
    return {
        "eigenvalues": eigenvalues.tolist(),
        "spectral_gap": float(eigenvalues[1]) if len(eigenvalues) > 1 else 0.0,
        "coordination_score": float(1.0 / (1.0 + eigenvalues[1])) if len(eigenvalues) > 1 else 1.0,
    }


@mcp.tool()
async def gf3_trit_sum(values: list[int]) -> dict:
    """
    Compute GF(3) trit sum and verify conservation.
    
    Args:
        values: List of balanced ternary values {-1, 0, 1}
    
    Returns:
        Sum, remainder, and conservation status
    """
    total = sum(values)
    remainder = total % 3
    # Convert to balanced representation
    balanced_remainder = remainder if remainder <= 1 else remainder - 3
    
    return {
        "sum": total,
        "remainder": remainder,
        "balanced_remainder": balanced_remainder,
        "conserved": remainder == 0,
        "adjustment_needed": -balanced_remainder if remainder != 0 else 0,
    }


@mcp.tool()
async def operadic_compose(
    diagrams: list[dict],
    composition_order: list[int],
) -> dict:
    """
    Compose diagrams operadically (nested substitution).
    
    Args:
        diagrams: List of diagram specs with 'dom', 'cod', 'boxes'
        composition_order: Order of composition (indices into diagrams)
    
    Returns:
        Composed diagram specification
    """
    if not diagrams or not composition_order:
        return {"error": "Empty input"}
    
    # Start with first diagram
    result = diagrams[composition_order[0]].copy()
    
    for idx in composition_order[1:]:
        next_diag = diagrams[idx]
        
        # Check composability: result.cod == next_diag.dom
        if result.get('cod') != next_diag.get('dom'):
            return {"error": f"Type mismatch: {result.get('cod')} != {next_diag.get('dom')}"}
        
        # Sequential composition
        result = {
            'dom': result['dom'],
            'cod': next_diag['cod'],
            'boxes': result.get('boxes', []) + next_diag.get('boxes', []),
            'depth': max(result.get('depth', 1), next_diag.get('depth', 1)) + 1,
        }
    
    return result


# Run without workflow wrapper overhead
if __name__ == "__main__":
    mcp.run()
```

## Stdio Transport Hardening

Address [#564](https://github.com/lastmile-ai/mcp-agent/issues/564):

```python
import asyncio
import signal
from contextlib import asynccontextmanager
from mcp.server.fastmcp import FastMCP
from mcp.server.stdio import stdio_server

@asynccontextmanager
async def robust_stdio_server(mcp: FastMCP):
    """Stdio server with graceful shutdown and error recovery."""
    
    shutdown_event = asyncio.Event()
    
    def signal_handler(signum, frame):
        shutdown_event.set()
    
    # Register signal handlers
    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)
    
    try:
        async with stdio_server() as (read_stream, write_stream):
            # Wrap streams with error handling
            async def safe_read():
                try:
                    async for message in read_stream:
                        if shutdown_event.is_set():
                            break
                        yield message
                except Exception as e:
                    if not shutdown_event.is_set():
                        print(f"Read error (recovering): {e}", file=sys.stderr)
            
            yield safe_read(), write_stream
            
    except BrokenPipeError:
        pass  # Expected on clean shutdown
    except Exception as e:
        print(f"Stdio transport error: {e}", file=sys.stderr)
    finally:
        shutdown_event.set()


async def run_robust_mcp(mcp: FastMCP):
    """Run MCP server with robust stdio handling."""
    async with robust_stdio_server(mcp) as (read_stream, write_stream):
        await mcp.handle_streams(read_stream, write_stream)
```

## Timeout-Free Long Operations

Pattern for long-running tools:

```python
from mcp.server.fastmcp import FastMCP
from mcp.types import TextContent
import asyncio

mcp = FastMCP("long-running-tools")

@mcp.tool()
async def train_sheaf_nn(
    dataset: str,
    epochs: int = 100,
    report_interval: int = 10,
) -> dict:
    """
    Train sheaf neural network with progress reporting.
    
    Uses streaming progress instead of blocking for full training.
    """
    results = {"epochs_completed": 0, "losses": []}
    
    for epoch in range(epochs):
        # Simulate training step
        await asyncio.sleep(0.1)  # Yield to event loop
        
        loss = 1.0 / (epoch + 1)  # Dummy loss
        results["losses"].append(loss)
        results["epochs_completed"] = epoch + 1
        
        # Progress checkpoint (allows client to poll)
        if (epoch + 1) % report_interval == 0:
            # In practice, store to shared state or emit progress event
            pass
    
    return {
        "status": "completed",
        "final_loss": results["losses"][-1],
        "epochs": epochs,
    }


@mcp.tool()
async def batch_process_with_progress(
    items: list[str],
    batch_size: int = 10,
) -> dict:
    """Process items in batches with yielding."""
    processed = []
    
    for i in range(0, len(items), batch_size):
        batch = items[i:i+batch_size]
        
        # Process batch
        for item in batch:
            processed.append(f"processed:{item}")
        
        # Yield to event loop between batches
        await asyncio.sleep(0)
    
    return {
        "processed_count": len(processed),
        "items": processed[:10],  # Return sample
    }
```

## Memory Graph Schema Flexibility

Address [MCP servers #3144](https://github.com/modelcontextprotocol/servers/issues/3144):

```python
from pydantic import BaseModel, ConfigDict
from typing import Any, Optional

class FlexibleEntity(BaseModel):
    """Entity with extensible properties for memory graph."""
    
    model_config = ConfigDict(extra='allow')  # Allow additional properties
    
    id: str
    type: str
    name: str
    observations: list[str] = []
    
    # Additional properties stored dynamically
    def get_extra(self, key: str, default: Any = None) -> Any:
        return getattr(self, key, default)


class FlexibleRelation(BaseModel):
    """Relation with extensible properties."""
    
    model_config = ConfigDict(extra='allow')
    
    source: str
    target: str
    relation_type: str
    
    
@mcp.tool()
async def add_entity_flexible(
    id: str,
    type: str,
    name: str,
    observations: list[str] = [],
    **extra_properties: Any,
) -> dict:
    """Add entity with arbitrary additional properties."""
    entity = FlexibleEntity(
        id=id,
        type=type,
        name=name,
        observations=observations,
        **extra_properties,
    )
    
    # Store in memory graph...
    
    return {
        "status": "created",
        "entity": entity.model_dump(),
    }
```

## Integration with ASI Skills

```python
# Compose multiple ASI skills via MCP fastpath

@mcp.tool()
async def asi_pipeline(
    input_graph: dict,
    operations: list[str],
) -> dict:
    """
    Run ASI skill pipeline on graph data.
    
    Operations can include:
    - "sheaf_laplacian": Compute coordination metric
    - "gf3_verify": Check GF(3) conservation
    - "topological_features": Extract TDA features
    """
    result = {"input": input_graph, "steps": []}
    
    for op in operations:
        if op == "sheaf_laplacian":
            step_result = await sheaf_laplacian(
                input_graph["node_features"],
                input_graph["edge_index"],
            )
        elif op == "gf3_verify":
            trits = [hash(str(n)) % 3 - 1 for n in input_graph["node_features"]]
            step_result = await gf3_trit_sum(trits)
        else:
            step_result = {"error": f"Unknown operation: {op}"}
        
        result["steps"].append({"operation": op, "result": step_result})
    
    return result
```

## Links

- [FastMCP Documentation](https://github.com/jlowin/fastmcp)
- [MCP Specification](https://modelcontextprotocol.io/)
- [mcp-agent](https://github.com/lastmile-ai/mcp-agent)
- [Issue #603: Workflow timeouts](https://github.com/lastmile-ai/mcp-agent/issues/603)

## Commands

```bash
just mcp-fastpath-serve      # Start FastMCP server
just mcp-fastpath-test       # Test tool endpoints
just mcp-sheaf-tool          # Run sheaf Laplacian tool
just mcp-gf3-verify          # Verify GF(3) conservation
```

---

*GF(3) Category: PLUS (Generation) | Lightweight MCP tool serving*