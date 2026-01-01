#!/usr/bin/env python3
"""
Bridge Dune Analytics to pyUSD Discovery Engine
GF(3) Trit: 0 (ERGODIC - synthesis)
"""

import os
import sys

# Use environment variable or fall back to script's directory
IES_PATH = os.environ.get("IES_PATH", os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, IES_PATH)

from typing import Dict, List, Any
from dataclasses import dataclass

@dataclass
class DuneDiscoveryBridge:
    """Connect Dune query results to discovery opportunities."""
    
    def enrich_with_dune(self, opportunities: List[Dict]) -> List[Dict]:
        """Enrich discovery opportunities with on-chain Dune data."""
        from query_pyusd import query_pyusd_flows
        
        dex_data = query_pyusd_flows("dex_volume")
        bridge_data = query_pyusd_flows("bridge_flows")
        
        for opp in opportunities:
            symbol = opp.get("asset_symbol", "")
            
            # Match DEX volume
            for row in dex_data.get("rows", []):
                if row.get("token_symbol") == symbol:
                    opp["dune_dex_volume_24h"] = row.get("volume_usd", 0)
                    opp["dune_dex_trades_24h"] = row.get("trade_count", 0)
            
            # Match bridge flows
            for row in bridge_data.get("rows", []):
                if row.get("token_symbol") == symbol:
                    opp["dune_bridge_inflow"] = row.get("inflow_usd", 0)
                    opp["dune_bridge_outflow"] = row.get("outflow_usd", 0)
        
        return opportunities

def integrate_pyusd_discovery():
    """Full integration with pyUSD discovery engine."""
    try:
        from pyusd_discovery_engine import PyusdDiscoveryEngine, DiscoveryMode
        
        engine = PyusdDiscoveryEngine()
        opportunities = engine.discover_opportunities(mode=DiscoveryMode.HYBRID)
        
        bridge = DuneDiscoveryBridge()
        enriched = bridge.enrich_with_dune([vars(o) for o in opportunities])
        
        return enriched
    except ImportError as e:
        return {"error": str(e), "hint": "Set IES_PATH environment variable or run from ies directory"}

if __name__ == "__main__":
    import json
    result = integrate_pyusd_discovery()
    print(json.dumps(result, indent=2, default=str))
