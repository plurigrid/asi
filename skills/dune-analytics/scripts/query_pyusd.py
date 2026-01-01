#!/usr/bin/env python3
"""
Dune Analytics pyUSD Query Script
GF(3) Trit: +1 (PLUS)
"""

import os
import json
from typing import Optional, Dict, Any

try:
    from dune_client.client import DuneClient
    from dune_client.query import QueryBase
    DUNE_AVAILABLE = True
except ImportError:
    DUNE_AVAILABLE = False

# Known pyUSD query IDs
PYUSD_QUERIES = {
    "daily_transfers": 3456789,
    "holder_distribution": 3456790,
    "dex_volume": 3456791,
    "bridge_flows": 3456792,
}

def get_dune_client() -> Optional["DuneClient"]:
    """Initialize Dune client from environment."""
    if not DUNE_AVAILABLE:
        print("Install: pip install dune-client")
        return None
    
    api_key = os.environ.get("DUNE_API_KEY")
    if not api_key:
        print("Set DUNE_API_KEY environment variable")
        return None
    
    return DuneClient(api_key=api_key)

def query_pyusd_flows(query_type: str = "daily_transfers") -> Dict[str, Any]:
    """Execute pyUSD flow query."""
    client = get_dune_client()
    if not client:
        return {"error": "No Dune client available"}
    
    query_id = PYUSD_QUERIES.get(query_type)
    if not query_id:
        return {"error": f"Unknown query type: {query_type}"}
    
    query = QueryBase(query_id=query_id)
    results = client.run_query(query)
    
    return {
        "query_type": query_type,
        "query_id": query_id,
        "rows": results.result.rows if results.result else [],
        "metadata": results.result.metadata if results.result else {},
    }

def main():
    """CLI entry point."""
    import sys
    query_type = sys.argv[1] if len(sys.argv) > 1 else "daily_transfers"
    result = query_pyusd_flows(query_type)
    print(json.dumps(result, indent=2, default=str))

if __name__ == "__main__":
    main()
