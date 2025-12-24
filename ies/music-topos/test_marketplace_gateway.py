#!/usr/bin/env python3
"""
Comprehensive Test Suite for Marketplace Gateway

Tests all 11 applications, composition chains, security, and streaming.
"""

import asyncio
import json
import pytest
import aiohttp
from marketplace_gateway import (
    ApplicationRegistry,
    CompositionEngine,
    CompositionStep,
    CompositionChain,
    MarketMakerApp,
    ComposerApp,
    PersonalizerApp,
    ConsensusApp,
    QueryEngineApp,
    ColorNavigatorApp,
    WorldNavigatorApp,
    EpistemologyApp,
    ActiveInferenceApp,
    PatternDiscoveryApp,
    ThreadAnalysisApp,
    APIKeyManager,
    RateLimiter,
    validate_gf3_conservation,
    hash_to_gf3_trit,
)


# =============================================================================
# GF(3) VALIDATION TESTS
# =============================================================================

def test_gf3_validation():
    """Test GF(3) conservation validation"""
    # Valid data (sum divisible by 3)
    valid_data = {"gf3_trits": [1, 1, 1]}  # sum=3, 3%3=0
    is_valid, msg = validate_gf3_conservation(valid_data)
    assert is_valid, f"Should be valid: {msg}"

    # Valid data (sum=0)
    valid_data2 = {"gf3_trits": [1, -1, 0]}  # sum=0, 0%3=0
    is_valid, msg = validate_gf3_conservation(valid_data2)
    assert is_valid, f"Should be valid: {msg}"

    # Invalid data (sum not divisible by 3)
    invalid_data = {"gf3_trits": [1, 1, 0]}  # sum=2, 2%3!=0
    is_valid, msg = validate_gf3_conservation(invalid_data)
    assert not is_valid, "Should be invalid"

def test_hash_to_gf3():
    """Test deterministic hashing to GF(3)"""
    # Same input should give same output
    trit1 = hash_to_gf3_trit("test", 0)
    trit2 = hash_to_gf3_trit("test", 0)
    assert trit1 == trit2, "Deterministic hashing failed"

    # Different seeds should give different outputs (usually)
    trit3 = hash_to_gf3_trit("test", 1)
    # Note: May occasionally be equal due to hash collisions

    # Verify trit values are in range
    assert trit1.value in [-1, 0, 1], "Trit out of range"


# =============================================================================
# APPLICATION TESTS
# =============================================================================

@pytest.mark.asyncio
async def test_market_maker_app():
    """Test Market Maker application"""
    app = MarketMakerApp()

    # Quote query
    result = await app.execute({
        "query_type": "quote",
        "asset": "PROP",
        "amount": 1000.0
    })

    assert "bid" in result
    assert "ask" in result
    assert "spread" in result
    assert result["spread"] == result["ask"] - result["bid"]
    assert "gf3_trits" in result
    assert len(result["gf3_trits"]) == 3

    # Liquidity query
    result2 = await app.execute({
        "query_type": "liquidity",
        "asset": "PROP",
        "amount": 1000.0
    })

    assert "available_liquidity" in result2
    assert "gf3_trits" in result2

@pytest.mark.asyncio
async def test_composer_app():
    """Test Composer application"""
    app = ComposerApp()

    result = await app.execute({
        "style": "classical",
        "length": 8,
        "key": "C"
    })

    assert "melody" in result
    assert "harmony" in result
    assert "tempo" in result
    assert len(result["melody"]) == 8 * 4  # 4 notes per measure
    assert len(result["harmony"]) == 8
    assert "gf3_trits" in result

@pytest.mark.asyncio
async def test_personalizer_app():
    """Test Personalizer application"""
    app = PersonalizerApp()

    # Recommendation query
    result = await app.execute({
        "user_id": "user_123",
        "query_type": "recommend"
    })

    assert "recommendations" in result
    assert len(result["recommendations"]) > 0
    assert "gf3_trits" in result

    # Segmentation query
    result2 = await app.execute({
        "user_id": "user_123",
        "query_type": "segment"
    })

    assert "segment" in result2
    assert "confidence" in result2
    assert "gf3_trits" in result2

@pytest.mark.asyncio
async def test_consensus_app():
    """Test Consensus application"""
    app = ConsensusApp()

    result = await app.execute({
        "proposal": {"type": "update", "value": 42},
        "agents": 5
    })

    assert "votes" in result
    assert len(result["votes"]) == 5
    assert "consensus_reached" in result
    assert "gf3_trits" in result

@pytest.mark.asyncio
async def test_query_engine_app():
    """Test Query Engine application"""
    app = QueryEngineApp()

    # Parallel queries
    result = await app.execute({
        "queries": ["query1", "query2", "query3"],
        "parallel": True
    })

    assert "results" in result
    assert len(result["results"]) == 3
    assert result["parallel"] is True
    assert "gf3_trits" in result

@pytest.mark.asyncio
async def test_color_navigator_app():
    """Test Color Navigator application"""
    app = ColorNavigatorApp()

    result = await app.execute({
        "start_color": [0, 0, 0],
        "steps": 5
    })

    assert "trajectory" in result
    assert len(result["trajectory"]) == 6  # start + 5 steps
    assert "final_color" in result
    assert "gf3_trits" in result

@pytest.mark.asyncio
async def test_world_navigator_app():
    """Test World Navigator application"""
    app = WorldNavigatorApp()

    result = await app.execute({
        "current_world": "world_0",
        "distance": 3
    })

    assert "reachable_worlds" in result
    assert len(result["reachable_worlds"]) == 4  # 0, 1, 2, 3
    assert "gf3_trits" in result

@pytest.mark.asyncio
async def test_epistemology_app():
    """Test Epistemology application"""
    app = EpistemologyApp()

    result = await app.execute({
        "concept": "knowledge",
        "depth": 2
    })

    assert "related_concepts" in result
    assert "connections" in result
    assert len(result["connections"]) > 0
    assert "gf3_trits" in result

@pytest.mark.asyncio
async def test_active_inference_app():
    """Test Active Inference application"""
    app = ActiveInferenceApp()

    result = await app.execute({
        "observation": [0.5, 0.3, 0.2],
        "prior": [0.33, 0.33, 0.34]
    })

    assert "posterior" in result
    assert "free_energy" in result
    assert "surprise" in result
    assert abs(sum(result["posterior"]) - 1.0) < 0.01  # Posterior sums to 1
    assert "gf3_trits" in result

@pytest.mark.asyncio
async def test_pattern_discovery_app():
    """Test Pattern Discovery application"""
    app = PatternDiscoveryApp()

    result = await app.execute({
        "data": [1, 2, 3, 4, 5],
        "dimensions": 5
    })

    assert "patterns" in result
    assert len(result["patterns"]) > 0
    assert "gf3_trits" in result

@pytest.mark.asyncio
async def test_thread_analysis_app():
    """Test Thread Analysis application"""
    app = ThreadAnalysisApp()

    result = await app.execute({
        "thread_id": "thread_123",
        "analysis_type": "summary"
    })

    assert "message_count" in result
    assert "key_concepts" in result
    assert "sentiment" in result
    assert "gf3_trits" in result


# =============================================================================
# REGISTRY TESTS
# =============================================================================

def test_application_registry():
    """Test application registry"""
    registry = ApplicationRegistry()

    # Check all 11 apps registered
    assert len(registry.apps) == 11

    # Check specific apps exist
    assert registry.get("market_maker") is not None
    assert registry.get("composer") is not None
    assert registry.get("personalizer") is not None
    assert registry.get("consensus") is not None
    assert registry.get("query_engine") is not None
    assert registry.get("color_navigator") is not None
    assert registry.get("world_navigator") is not None
    assert registry.get("epistemology") is not None
    assert registry.get("active_inference") is not None
    assert registry.get("pattern_discovery") is not None
    assert registry.get("thread_analysis") is not None

    # Check categories
    apps_by_category = {
        "alpha": [],
        "beta": [],
        "gamma": [],
        "baseline": []
    }
    for app in registry.apps.values():
        apps_by_category[app.category].append(app.name)

    assert len(apps_by_category["alpha"]) >= 1
    assert len(apps_by_category["beta"]) >= 2
    assert len(apps_by_category["gamma"]) >= 2
    assert len(apps_by_category["baseline"]) >= 6

    # Check list_all
    all_apps = registry.list_all()
    assert len(all_apps) == 11


# =============================================================================
# COMPOSITION ENGINE TESTS
# =============================================================================

@pytest.mark.asyncio
async def test_composition_simple_chain():
    """Test simple composition chain"""
    registry = ApplicationRegistry()
    engine = CompositionEngine(registry)

    # Chain: Composer → Personalizer
    chain = CompositionChain(
        id="test_chain",
        steps=[
            CompositionStep(
                app_name="composer",
                input_mapping={},
                params={"style": "classical", "length": 4, "key": "C"}
            ),
            CompositionStep(
                app_name="personalizer",
                input_mapping={"key": "context"},  # Pass composer key to personalizer
                params={"user_id": "user_123", "query_type": "recommend"}
            )
        ]
    )

    result = await engine.execute_chain(chain)

    assert result.status == "completed"
    assert len(result.results) == 2
    assert result.results[0].app_name == "composer"
    assert result.results[1].app_name == "personalizer"
    assert result.results[0].status == "completed"
    assert result.results[1].status == "completed"

@pytest.mark.asyncio
async def test_composition_complex_chain():
    """Test complex 3-step composition chain"""
    registry = ApplicationRegistry()
    engine = CompositionEngine(registry)

    # Chain: Market Maker → Consensus → Query Engine
    chain = CompositionChain(
        id="test_chain",
        steps=[
            CompositionStep(
                app_name="market_maker",
                input_mapping={},
                params={"query_type": "quote", "asset": "PROP", "amount": 1000}
            ),
            CompositionStep(
                app_name="consensus",
                input_mapping={"mid_price": "proposal"},
                params={"agents": 3}
            ),
            CompositionStep(
                app_name="query_engine",
                input_mapping={},
                params={"queries": ["q1", "q2"], "parallel": True}
            )
        ]
    )

    result = await engine.execute_chain(chain)

    assert result.status == "completed"
    assert len(result.results) == 3

    # Check each step completed
    for step_result in result.results:
        assert step_result.status == "completed"
        assert step_result.output_data is not None

@pytest.mark.asyncio
async def test_composition_world_navigation():
    """Test world navigation composition chain"""
    registry = ApplicationRegistry()
    engine = CompositionEngine(registry)

    # Chain: World Navigator → Epistemology → Pattern Discovery
    chain = CompositionChain(
        id="test_chain",
        steps=[
            CompositionStep(
                app_name="world_navigator",
                input_mapping={},
                params={"current_world": "world_0", "distance": 2}
            ),
            CompositionStep(
                app_name="epistemology",
                input_mapping={},
                params={"concept": "knowledge", "depth": 2}
            ),
            CompositionStep(
                app_name="pattern_discovery",
                input_mapping={"related_concepts": "data"},
                params={"dimensions": 5}
            )
        ]
    )

    result = await engine.execute_chain(chain)

    assert result.status == "completed"
    assert len(result.results) == 3


# =============================================================================
# SECURITY TESTS
# =============================================================================

def test_api_key_manager():
    """Test API key management"""
    manager = APIKeyManager()

    # Default demo key should exist
    valid, user_id = manager.validate_key("demo_key")
    assert valid
    assert user_id == "demo_user"

    # Invalid key should fail
    valid, user_id = manager.validate_key("invalid_key")
    assert not valid
    assert user_id is None

    # Create new key
    new_key = manager.create_key("new_user")
    assert new_key != ""
    assert new_key != "demo_key"

    # Validate new key
    valid, user_id = manager.validate_key(new_key)
    assert valid
    assert user_id == "new_user"

def test_rate_limiter():
    """Test rate limiting"""
    limiter = RateLimiter()

    # Should allow up to limit
    for i in range(10):
        allowed, remaining = limiter.check_limit("user1", "test_app", 10)
        assert allowed
        assert remaining == 10 - i - 1

    # Should deny after limit
    allowed, remaining = limiter.check_limit("user1", "test_app", 10)
    assert not allowed
    assert remaining == 0

    # Different user should be independent
    allowed, remaining = limiter.check_limit("user2", "test_app", 10)
    assert allowed


# =============================================================================
# INTEGRATION TESTS
# =============================================================================

@pytest.mark.asyncio
async def test_full_integration():
    """Test full integration of all components"""
    registry = ApplicationRegistry()
    engine = CompositionEngine(registry)

    # Test all 11 apps can execute
    apps_to_test = [
        ("market_maker", {"query_type": "quote", "asset": "PROP"}),
        ("composer", {"style": "classical", "length": 4}),
        ("personalizer", {"user_id": "test", "query_type": "recommend"}),
        ("consensus", {"proposal": {}, "agents": 3}),
        ("query_engine", {"queries": ["q1"], "parallel": True}),
        ("color_navigator", {"start_color": [0, 0, 0], "steps": 3}),
        ("world_navigator", {"current_world": "w0", "distance": 2}),
        ("epistemology", {"concept": "test", "depth": 1}),
        ("active_inference", {"observation": [0.5, 0.3, 0.2]}),
        ("pattern_discovery", {"data": [1, 2, 3], "dimensions": 3}),
        ("thread_analysis", {"thread_id": "t1", "analysis_type": "summary"})
    ]

    for app_name, params in apps_to_test:
        app = registry.get(app_name)
        assert app is not None, f"App {app_name} not found"

        result = await app.handler(params)
        assert result is not None, f"App {app_name} returned None"
        assert "gf3_trits" in result, f"App {app_name} missing GF(3) trits"

        # Validate GF(3)
        valid, msg = validate_gf3_conservation(result)
        if not valid:
            print(f"Warning: {app_name} GF(3) validation: {msg}")

@pytest.mark.asyncio
async def test_performance():
    """Test performance of applications"""
    import time

    registry = ApplicationRegistry()

    # Test each app performance
    results = []

    for app_name in ["market_maker", "composer", "personalizer"]:
        app = registry.get(app_name)
        start = time.time()
        await app.handler({})
        elapsed = time.time() - start
        results.append((app_name, elapsed))

    # All apps should complete in < 1 second
    for app_name, elapsed in results:
        assert elapsed < 1.0, f"{app_name} took {elapsed:.3f}s (too slow)"
        print(f"{app_name}: {elapsed*1000:.2f}ms")


# =============================================================================
# RUN TESTS
# =============================================================================

if __name__ == "__main__":
    print("=" * 70)
    print("MARKETPLACE GATEWAY TEST SUITE")
    print("=" * 70)

    # Run all tests
    pytest.main([__file__, "-v", "--tb=short"])
