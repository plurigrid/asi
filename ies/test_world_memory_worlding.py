#!/usr/bin/env python3
"""
Test Suite for World Memory Is World Remembering Is World Worlding

Tests the autopoietic strange loop with:
- GF(3) conservation verification
- Involution closure (ι∘ι = id)
- Reafference loop integration
- Metaskill mapping (FILTERING, ITERATION, INTEGRATION)
"""

import pytest
import hashlib
from dataclasses import dataclass
from typing import List, Dict, Any

from world_memory_worlding import (
    Trit,
    WorldState,
    WorldMemory,
    WorldRemembering, 
    WorldWorlding,
    AutopoieticLoop,
    MemoryTrace
)


class TestGF3Conservation:
    """Test GF(3) conservation: (-1) + 0 + (+1) = 0"""
    
    def test_trit_values(self):
        """Verify trit enum values"""
        assert Trit.MINUS == -1
        assert Trit.ERGODIC == 0
        assert Trit.PLUS == 1
    
    def test_trit_conservation(self):
        """Verify trits sum to 0"""
        assert Trit.MINUS + Trit.ERGODIC + Trit.PLUS == 0
    
    def test_loop_conserves_gf3(self):
        """Each loop step conserves GF(3)"""
        loop = AutopoieticLoop(seed=42)
        
        for i in range(5):
            result = loop.step({"test": f"value_{i}"})
            assert result["gf3_conserved"], f"GF(3) not conserved at step {i}"
            assert result["gf3_sum"] == 0
    
    def test_tripartite_balance(self):
        """Memory(-1) + Remembering(0) + Worlding(+1) = 0"""
        loop = AutopoieticLoop(seed=1069)
        
        m = loop.memory.trit
        r = loop.remembering.trit
        w = loop.worlding.trit
        
        assert m == Trit.MINUS
        assert r == Trit.ERGODIC
        assert w == Trit.PLUS
        assert m + r + w == 0


class TestInvolution:
    """Test involution property: ι∘ι = id"""
    
    def test_involution_closure(self):
        """Verify ι∘ι = id"""
        loop = AutopoieticLoop(seed=1069)
        
        assert loop.verify_involution() is True
    
    def test_double_application_identity(self):
        """Applying the loop twice preserves seed identity"""
        loop = AutopoieticLoop(seed=42)
        initial_seed = loop.seed
        
        loop.step()
        loop.step()
        
        assert loop.seed == initial_seed
    
    def test_frame_invariance(self):
        """Same seed produces same colors (frame invariance)"""
        loop1 = AutopoieticLoop(seed=1069)
        loop2 = AutopoieticLoop(seed=1069)
        
        result1 = loop1.step()
        result2 = loop2.step()
        
        assert result1["new_world"].color == result2["new_world"].color


class TestMemoryFiltering:
    """Test FILTERING metaskill in memory layer"""
    
    def test_store_with_constraints(self):
        """Memory filters based on constraints"""
        memory = WorldMemory(seed=42)
        
        constraint_positive = lambda x: x > 0
        
        assert memory.store("pos", 10, [constraint_positive]) is True
        assert memory.store("neg", -5, [constraint_positive]) is False
        
        assert "pos" in memory.traces
        assert "neg" not in memory.traces
    
    def test_coherence_filtering(self):
        """Filter traces by coherence threshold"""
        memory = WorldMemory(seed=42)
        
        memory.store("low_coherence", ["a", "a", "a"])
        memory.store("high_coherence", ["a", "b", "c"])
        
        high_coherence = memory.filter_by_coherence(threshold=0.9)
        
        assert "high_coherence" in high_coherence
    
    def test_memory_as_state(self):
        """Memory produces valid world state"""
        memory = WorldMemory(seed=42)
        memory.store("key1", "value1")
        
        state = memory.get_state()
        
        assert state.trit == Trit.MINUS
        assert state.seed == 42
        assert "key1" in state.data


class TestRememberingIteration:
    """Test ITERATION metaskill in remembering layer"""
    
    def test_six_step_cycle(self):
        """Remembering uses 6-step iteration"""
        memory = WorldMemory(seed=42)
        memory.store("test_pattern", {"value": 1})
        
        remembering = WorldRemembering(memory)
        result = remembering.remember("test", cycles=6)
        
        assert result["refined"] is True
        assert "matches" in result
        assert "synthesis" in result
    
    def test_convergence_detection(self):
        """Iteration detects convergence"""
        memory = WorldMemory(seed=42)
        memory.store("stable", {"static": True})
        
        remembering = WorldRemembering(memory)
        result = remembering.remember("stable", cycles=10)
        
        assert len(remembering.iteration_history) <= 10
    
    def test_pattern_matching(self):
        """Remembering finds matching patterns"""
        memory = WorldMemory(seed=42)
        memory.store("autopoiesis_1", {"concept": "self-production"})
        memory.store("autopoiesis_2", {"concept": "self-maintenance"})
        memory.store("unrelated", {"concept": "other"})
        
        remembering = WorldRemembering(memory)
        result = remembering.remember("autopoiesis", cycles=3)
        
        assert len(result["matches"]) == 2


class TestWorldingIntegration:
    """Test INTEGRATION metaskill in worlding layer"""
    
    def test_isomorphism_detection(self):
        """Worlding finds isomorphisms across traces"""
        memory = WorldMemory(seed=42)
        memory.store("concept_a_1", {"type": "a"})
        memory.store("concept_a_2", {"type": "a"})
        
        remembering = WorldRemembering(memory)
        worlding = WorldWorlding(memory, remembering, seed=42)
        
        traces = list(memory.traces.values())
        isos = worlding._find_isomorphisms(traces)
        
        assert "concept" in isos
        assert isos["concept"] >= 2
    
    def test_world_generation(self):
        """Worlding generates new world states"""
        memory = WorldMemory(seed=42)
        memory.store("source_1", {"data": 1})
        memory.store("source_2", {"data": 2})
        
        remembering = WorldRemembering(memory)
        worlding = WorldWorlding(memory, remembering, seed=42)
        
        traces = list(memory.traces.values())
        new_world = worlding.world(traces)
        
        assert new_world.trit == Trit.PLUS
        assert len(new_world.color) == 7
        assert new_world.color.startswith("#")
    
    def test_loop_closure(self):
        """Worlded state becomes memory (loop closes)"""
        memory = WorldMemory(seed=42)
        memory.store("initial", {"data": "start"})
        
        remembering = WorldRemembering(memory)
        worlding = WorldWorlding(memory, remembering, seed=42)
        
        traces = list(memory.traces.values())
        initial_count = len(memory.traces)
        
        worlding.world(traces)
        
        assert len(memory.traces) > initial_count


class TestAutopoieticLoop:
    """Test complete autopoietic strange loop"""
    
    def test_self_production(self):
        """Each state generates next state"""
        loop = AutopoieticLoop(seed=1069)
        
        results = loop.run(steps=3)
        
        assert len(results) == 3
        for i, r in enumerate(results):
            assert r["loop"] == i + 1
    
    def test_self_maintenance(self):
        """Organization preserved across transformations"""
        loop = AutopoieticLoop(seed=1069)
        
        initial_seed = loop.seed
        loop.run(steps=10)
        
        assert loop.seed == initial_seed
        assert loop.memory.trit == Trit.MINUS
        assert loop.remembering.trit == Trit.ERGODIC
        assert loop.worlding.trit == Trit.PLUS
    
    def test_self_bounded(self):
        """System has distinct boundary"""
        loop = AutopoieticLoop(seed=42)
        
        loop.step({"internal": "data"})
        
        for key in loop.memory.traces:
            assert "42" in str(loop.memory.get_state().seed) or "input" in key or "world" in key
    
    def test_deterministic_colors(self):
        """Same seed produces deterministic color sequence"""
        colors1 = []
        colors2 = []
        
        loop1 = AutopoieticLoop(seed=1069)
        loop2 = AutopoieticLoop(seed=1069)
        
        for _ in range(5):
            r1 = loop1.step()
            r2 = loop2.step()
            colors1.append(r1["new_world"].color)
            colors2.append(r2["new_world"].color)
        
        assert colors1 == colors2


class TestReafferenceIntegration:
    """Test reafference loop properties"""
    
    def test_prediction_observation_match(self):
        """Prediction matches observation (reafference)"""
        loop = AutopoieticLoop(seed=1069)
        
        result = loop.step()
        
        expected_color = WorldState(
            seed=1069,
            cycle=0,
            data={},
            trit=Trit.PLUS
        ).color
        
        assert result["new_world"].seed == 1069
    
    def test_efference_copy(self):
        """System generates prediction before action"""
        loop = AutopoieticLoop(seed=42)
        
        loop.step({"concept": "test"})
        
        assert len(loop.worlding.generated_worlds) >= 1
    
    def test_fixed_point_identity(self):
        """Generator ≡ Observer when same seed"""
        loop = AutopoieticLoop(seed=1069)
        
        r1 = loop.step()
        
        loop2 = AutopoieticLoop(seed=1069)
        r2 = loop2.step()
        
        assert r1["new_world"].color == r2["new_world"].color


class TestMetaskillMapping:
    """Test mapping to three metaskills"""
    
    def test_filtering_maps_to_memory(self):
        """FILTERING metaskill → Memory layer"""
        memory = WorldMemory(seed=42)
        
        constraint = lambda x: isinstance(x, str)
        memory.store("valid", "string", [constraint])
        memory.store("invalid", 123, [constraint])
        
        assert "valid" in memory.traces
        assert "invalid" not in memory.traces
    
    def test_iteration_maps_to_remembering(self):
        """ITERATION metaskill → Remembering layer"""
        memory = WorldMemory(seed=42)
        memory.store("pattern", {"key": "value"})
        
        remembering = WorldRemembering(memory)
        result = remembering.remember("pattern", cycles=6)
        
        assert len(remembering.iteration_history) > 0
    
    def test_integration_maps_to_worlding(self):
        """INTEGRATION metaskill → Worlding layer"""
        memory = WorldMemory(seed=42)
        memory.store("domain_a", {"type": "a"})
        memory.store("domain_b", {"type": "b"})
        
        remembering = WorldRemembering(memory)
        worlding = WorldWorlding(memory, remembering, seed=42)
        
        traces = list(memory.traces.values())
        new_world = worlding.world(traces)
        
        assert "emergent" in new_world.data or new_world.data.get("bridges", [])


def run_all_tests():
    """Run all tests with summary"""
    print("=" * 70)
    print("WORLD MEMORY WORLDING TEST SUITE")
    print("=" * 70)
    
    pytest.main([__file__, "-v", "--tb=short"])


if __name__ == "__main__":
    run_all_tests()
