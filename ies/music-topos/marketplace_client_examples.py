#!/usr/bin/env python3
"""
Example Client Scripts for Marketplace Gateway

Demonstrates how to use the unified API marketplace:
- Single application execution
- Multi-step composition chains
- WebSocket streaming
- Error handling
"""

import asyncio
import aiohttp
import json
from typing import Dict, Any, List


class MarketplaceClient:
    """Client for interacting with Marketplace Gateway"""

    def __init__(self, base_url: str = "http://localhost:8080", api_key: str = "demo_key"):
        self.base_url = base_url
        self.api_key = api_key
        self.headers = {"X-API-Key": api_key, "Content-Type": "application/json"}

    async def list_apps(self) -> Dict[str, Any]:
        """List all available applications"""
        async with aiohttp.ClientSession() as session:
            async with session.get(
                f"{self.base_url}/apps",
                headers=self.headers
            ) as resp:
                return await resp.json()

    async def execute(self, app_name: str, params: Dict[str, Any]) -> Dict[str, Any]:
        """Execute single application"""
        async with aiohttp.ClientSession() as session:
            async with session.post(
                f"{self.base_url}/execute",
                headers=self.headers,
                json={"app_name": app_name, "params": params}
            ) as resp:
                return await resp.json()

    async def compose(self, steps: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Execute composition chain"""
        async with aiohttp.ClientSession() as session:
            async with session.post(
                f"{self.base_url}/compose",
                headers=self.headers,
                json={"steps": steps}
            ) as resp:
                return await resp.json()

    async def get_result(self, result_id: str) -> Dict[str, Any]:
        """Get cached result by ID"""
        async with aiohttp.ClientSession() as session:
            async with session.get(
                f"{self.base_url}/results/{result_id}",
                headers=self.headers
            ) as resp:
                return await resp.json()

    async def health_check(self) -> Dict[str, Any]:
        """Check gateway health"""
        async with aiohttp.ClientSession() as session:
            async with session.get(f"{self.base_url}/health") as resp:
                return await resp.json()


# =============================================================================
# EXAMPLE 1: List All Applications
# =============================================================================

async def example_list_apps():
    """Example: List all available applications"""
    print("\n" + "=" * 70)
    print("EXAMPLE 1: List All Applications")
    print("=" * 70)

    client = MarketplaceClient()
    result = await client.list_apps()

    print(f"\nTotal applications: {result['total']}\n")

    for app in result['applications']:
        print(f"  📦 {app['name']:20} ({app['category']:8}) - {app['description']}")
        print(f"     Rate limit: {app['rate_limit']}/min")


# =============================================================================
# EXAMPLE 2: Execute Market Maker
# =============================================================================

async def example_market_maker():
    """Example: Get market maker quote"""
    print("\n" + "=" * 70)
    print("EXAMPLE 2: Market Maker - Get Quote")
    print("=" * 70)

    client = MarketplaceClient()

    result = await client.execute(
        app_name="market_maker",
        params={
            "query_type": "quote",
            "asset": "PROP",
            "amount": 5000.0
        }
    )

    print("\n📊 Market Maker Quote:")
    print(f"  Asset: {result['output']['asset']}")
    print(f"  Bid: ${result['output']['bid']:.4f}")
    print(f"  Ask: ${result['output']['ask']:.4f}")
    print(f"  Spread: ${result['output']['spread']:.4f}")
    print(f"  Mid Price: ${result['output']['mid_price']:.4f}")
    print(f"  Liquidity Score: {result['output']['liquidity_score']:.2f}")
    print(f"  GF(3) Valid: {result['gf3_valid']}")
    print(f"  Execution Time: {result['execution_time_ms']:.2f}ms")


# =============================================================================
# EXAMPLE 3: Execute Composer
# =============================================================================

async def example_composer():
    """Example: Generate music composition"""
    print("\n" + "=" * 70)
    print("EXAMPLE 3: Composer - Generate Melody")
    print("=" * 70)

    client = MarketplaceClient()

    result = await client.execute(
        app_name="composer",
        params={
            "style": "classical",
            "length": 8,
            "key": "C"
        }
    )

    print("\n🎵 Music Composition:")
    print(f"  Style: {result['output']['style']}")
    print(f"  Key: {result['output']['key']}")
    print(f"  Tempo: {result['output']['tempo']} BPM")
    print(f"  Time Signature: {result['output']['time_signature']}")
    print(f"  Melody: {len(result['output']['melody'])} notes")
    print(f"  Harmony: {len(result['output']['harmony'])} chords")
    print(f"  First 4 notes: {result['output']['melody'][:4]}")
    print(f"  GF(3) Valid: {result['gf3_valid']}")


# =============================================================================
# EXAMPLE 4: Execute Personalizer
# =============================================================================

async def example_personalizer():
    """Example: Get personalized recommendations"""
    print("\n" + "=" * 70)
    print("EXAMPLE 4: Personalizer - Get Recommendations")
    print("=" * 70)

    client = MarketplaceClient()

    result = await client.execute(
        app_name="personalizer",
        params={
            "user_id": "user_12345",
            "query_type": "recommend",
            "context": {"preferences": ["classical", "jazz"]}
        }
    )

    print("\n👤 Personalized Recommendations:")
    print(f"  User: {result['output']['user_id']}")
    print(f"  Personalization Score: {result['output']['personalization_score']:.2f}")
    print("\n  Top Recommendations:")

    for rec in result['output']['recommendations'][:3]:
        print(f"    {rec['item_id']} - Score: {rec['score']:.2f} - {rec['reason']}")

    print(f"\n  GF(3) Valid: {result['gf3_valid']}")


# =============================================================================
# EXAMPLE 5: Composition Chain - Market Analysis
# =============================================================================

async def example_market_analysis_chain():
    """Example: Market Maker → Consensus → Query Engine"""
    print("\n" + "=" * 70)
    print("EXAMPLE 5: Composition Chain - Market Analysis")
    print("=" * 70)

    client = MarketplaceClient()

    result = await client.compose(steps=[
        {
            "app_name": "market_maker",
            "input_mapping": {},
            "params": {
                "query_type": "quote",
                "asset": "PROP",
                "amount": 10000
            }
        },
        {
            "app_name": "consensus",
            "input_mapping": {"mid_price": "proposal"},
            "params": {"agents": 5}
        },
        {
            "app_name": "query_engine",
            "input_mapping": {},
            "params": {
                "queries": ["historical_data", "volatility", "sentiment"],
                "parallel": True
            }
        }
    ])

    print(f"\n🔗 Chain Status: {result['status']}")
    print(f"   Total Steps: {result['steps']}")

    for i, step_result in enumerate(result['results'], 1):
        print(f"\n   Step {i}: {step_result['app_name']}")
        print(f"     Status: {step_result['status']}")
        print(f"     Execution: {step_result['execution_time_ms']:.2f}ms")
        print(f"     GF(3) Valid: {step_result['gf3_valid']}")

    print("\n   Final Output Keys:", list(result['results'][-1]['output'].keys()))


# =============================================================================
# EXAMPLE 6: Composition Chain - Music Personalization
# =============================================================================

async def example_music_personalization_chain():
    """Example: Composer → Personalizer → Query Engine"""
    print("\n" + "=" * 70)
    print("EXAMPLE 6: Composition Chain - Music Personalization")
    print("=" * 70)

    client = MarketplaceClient()

    result = await client.compose(steps=[
        {
            "app_name": "composer",
            "input_mapping": {},
            "params": {
                "style": "jazz",
                "length": 16,
                "key": "Am"
            }
        },
        {
            "app_name": "personalizer",
            "input_mapping": {"key": "context"},
            "params": {
                "user_id": "music_lover_42",
                "query_type": "recommend"
            }
        },
        {
            "app_name": "thread_analysis",
            "input_mapping": {},
            "params": {
                "thread_id": "music_thread_123",
                "analysis_type": "summary"
            }
        }
    ])

    print(f"\n🎼 Music Personalization Chain:")
    print(f"   Status: {result['status']}")
    print(f"   Total Steps: {result['steps']}")

    # Show composition
    step1 = result['results'][0]['output']
    print(f"\n   1. Composition Generated:")
    print(f"      Style: {step1['style']}, Key: {step1['key']}")
    print(f"      Melody: {len(step1['melody'])} notes")

    # Show recommendations
    step2 = result['results'][1]['output']
    print(f"\n   2. Personalized Recommendations:")
    print(f"      User: {step2['user_id']}")
    print(f"      Top 3: {[r['item_id'] for r in step2['recommendations'][:3]]}")

    # Show thread analysis
    step3 = result['results'][2]['output']
    print(f"\n   3. Thread Analysis:")
    print(f"      Messages: {step3['message_count']}")
    print(f"      Sentiment: {step3['sentiment']:.2f}")


# =============================================================================
# EXAMPLE 7: Composition Chain - World Navigation
# =============================================================================

async def example_world_navigation_chain():
    """Example: World Navigator → Epistemology → Pattern Discovery"""
    print("\n" + "=" * 70)
    print("EXAMPLE 7: Composition Chain - World Navigation")
    print("=" * 70)

    client = MarketplaceClient()

    result = await client.compose(steps=[
        {
            "app_name": "world_navigator",
            "input_mapping": {},
            "params": {
                "current_world": "world_0",
                "distance": 3
            }
        },
        {
            "app_name": "epistemology",
            "input_mapping": {},
            "params": {
                "concept": "knowledge_graph",
                "depth": 2
            }
        },
        {
            "app_name": "pattern_discovery",
            "input_mapping": {"related_concepts": "data"},
            "params": {
                "dimensions": 5
            }
        }
    ])

    print(f"\n🌍 World Navigation Chain:")
    print(f"   Status: {result['status']}")

    # Show worlds
    step1 = result['results'][0]['output']
    print(f"\n   1. Worlds Reachable: {len(step1['reachable_worlds'])}")
    for world in step1['reachable_worlds'][:3]:
        print(f"      {world['world_id']} (distance={world['distance']}, entropy={world['entropy']:.2f})")

    # Show knowledge
    step2 = result['results'][1]['output']
    print(f"\n   2. Knowledge Graph:")
    print(f"      Concept: {step2['concept']}")
    print(f"      Related: {len(step2['related_concepts'])} concepts")

    # Show patterns
    step3 = result['results'][2]['output']
    print(f"\n   3. Patterns Discovered: {step3['total_patterns']}")
    for pattern in step3['patterns'][:2]:
        print(f"      {pattern['pattern_id']} (confidence={pattern['confidence']:.2f})")


# =============================================================================
# EXAMPLE 8: Composition Chain - Active Inference
# =============================================================================

async def example_active_inference_chain():
    """Example: Active Inference → Color Navigator → Consensus"""
    print("\n" + "=" * 70)
    print("EXAMPLE 8: Composition Chain - Active Inference Loop")
    print("=" * 70)

    client = MarketplaceClient()

    result = await client.compose(steps=[
        {
            "app_name": "active_inference",
            "input_mapping": {},
            "params": {
                "observation": [0.6, 0.3, 0.1],
                "prior": [0.33, 0.33, 0.34]
            }
        },
        {
            "app_name": "color_navigator",
            "input_mapping": {"posterior": "start_color"},
            "params": {
                "steps": 5
            }
        },
        {
            "app_name": "consensus",
            "input_mapping": {"final_color": "proposal"},
            "params": {
                "agents": 3
            }
        }
    ])

    print(f"\n🧠 Active Inference Chain:")

    # Show inference
    step1 = result['results'][0]['output']
    print(f"\n   1. Active Inference:")
    print(f"      Free Energy: {step1['free_energy']:.4f}")
    print(f"      Surprise: {step1['surprise']:.4f}")
    print(f"      Posterior: {[f'{p:.3f}' for p in step1['posterior']]}")

    # Show navigation
    step2 = result['results'][1]['output']
    print(f"\n   2. Color Navigation:")
    print(f"      Steps: {len(step2['trajectory']) - 1}")
    print(f"      Final Color: {step2['final_color']}")

    # Show consensus
    step3 = result['results'][2]['output']
    print(f"\n   3. Consensus:")
    print(f"      Reached: {step3['consensus_reached']}")
    print(f"      Agents: {step3['agents']}")


# =============================================================================
# EXAMPLE 9: Parallel Queries with Query Engine
# =============================================================================

async def example_parallel_queries():
    """Example: Execute parallel batch queries"""
    print("\n" + "=" * 70)
    print("EXAMPLE 9: Query Engine - Parallel Batch Processing")
    print("=" * 70)

    client = MarketplaceClient()

    result = await client.execute(
        app_name="query_engine",
        params={
            "queries": [
                "SELECT * FROM markets WHERE volume > 1000",
                "SELECT * FROM users WHERE active = true",
                "SELECT * FROM transactions WHERE timestamp > NOW() - INTERVAL '1 day'",
                "SELECT * FROM analytics WHERE metric = 'engagement'"
            ],
            "parallel": True
        }
    )

    print("\n⚡ Parallel Query Results:")
    print(f"  Total Queries: {result['output']['total_queries']}")
    print(f"  Parallel Mode: {result['output']['parallel']}")
    print(f"  Execution Time: {result['execution_time_ms']:.2f}ms")
    print("\n  Results:")

    for i, query_result in enumerate(result['output']['results'], 1):
        print(f"    Query {i}: {query_result['result_count']} results (GF3={query_result['gf3_color']})")


# =============================================================================
# EXAMPLE 10: Health Check
# =============================================================================

async def example_health_check():
    """Example: Check gateway health"""
    print("\n" + "=" * 70)
    print("EXAMPLE 10: Health Check")
    print("=" * 70)

    client = MarketplaceClient()
    result = await client.health_check()

    print("\n💚 Gateway Health:")
    print(f"  Status: {result['status']}")
    print(f"  Apps Count: {result['apps_count']}")
    print(f"  Cached Results: {result['cached_results']}")


# =============================================================================
# RUN ALL EXAMPLES
# =============================================================================

async def run_all_examples():
    """Run all example demonstrations"""
    print("\n" + "=" * 70)
    print("MARKETPLACE GATEWAY - CLIENT EXAMPLES")
    print("=" * 70)
    print("\nThese examples demonstrate the unified API marketplace")
    print("integrating 11 ALPHA-BETA-GAMMA applications.")
    print("\nPrerequisite: Start the gateway server:")
    print("  python marketplace_gateway.py --port 8080")

    try:
        # Run all examples
        await example_health_check()
        await example_list_apps()
        await example_market_maker()
        await example_composer()
        await example_personalizer()
        await example_parallel_queries()
        await example_market_analysis_chain()
        await example_music_personalization_chain()
        await example_world_navigation_chain()
        await example_active_inference_chain()

        print("\n" + "=" * 70)
        print("✅ ALL EXAMPLES COMPLETED SUCCESSFULLY")
        print("=" * 70)

    except aiohttp.ClientError as e:
        print(f"\n❌ Connection Error: {e}")
        print("\nMake sure the gateway server is running:")
        print("  python marketplace_gateway.py --port 8080")


if __name__ == "__main__":
    asyncio.run(run_all_examples())
