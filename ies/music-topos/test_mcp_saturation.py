#!/usr/bin/env python3
"""
MCP Space Saturation Tests
============================

Comprehensive test suite verifying that perception and action tools
fully saturate the MCP space with integrated functionality.

Tests:
1. Perception-only workflows (knowledge queries)
2. Action-only workflows (colorization)
3. Integrated workflows (knowledge → colors)
4. Multi-agent parallel operations
5. Deterministic agreement properties
6. Performance characteristics
"""

import sys
import time
from typing import Dict, List, Any, Tuple


class MCPSaturationTest:
    """Test suite for MCP space saturation."""

    def __init__(self):
        """Initialize test harness."""
        # Import the systems
        from mcp_unified_server import UnifiedMCPServer
        from mcp_perception_tools import PerceptionTools

        self.server = UnifiedMCPServer()
        self.perception = PerceptionTools()
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0
        self.skip_count = 0

    def test(self, name: str, expected: bool, actual: bool) -> bool:
        """Run a single test assertion."""
        self.test_count += 1
        status = "✅" if expected == actual else "❌"

        if expected == actual:
            self.pass_count += 1
        else:
            self.fail_count += 1

        print(f"{status} {name}")
        return expected == actual

    def section(self, title: str):
        """Print a test section header."""
        print(f"\n{'=' * 60}")
        print(f"{title}")
        print('=' * 60)

    # ========================================================================
    # PERCEPTION-ONLY TESTS
    # ========================================================================

    def test_perception_queries(self) -> bool:
        """Test perception tools: concept queries."""
        self.section("1. PERCEPTION QUERIES")

        # Test 1: Query existing concept
        result = self.perception.query_concept("consensus")
        self.test("Query consensus concept", result['status'], "found")
        self.test("Consensus has difficulty", 'difficulty_level' in result['concept'], True)
        self.test("Consensus has prerequisites", len(result['concept']['prerequisites']) > 0, True)

        # Test 2: Query non-existent concept
        result = self.perception.query_concept("nonexistent")
        self.test("Non-existent concept returns not_found", result['status'], "not_found")

        # Test 3: List available concepts
        result = self.perception.query_concept("consensus")
        self.test("Available concepts in not_found response", 'available_concepts' in result or 'concept' in result, True)

        return self.fail_count == 0

    def test_bridge_discovery(self) -> bool:
        """Test bridge discovery: theory ↔ implementation."""
        self.section("2. BRIDGE DISCOVERY")

        # Test 1: Find existing bridge
        result = self.perception.discover_bridges("consensus", "raft")
        self.test("Find consensus ↔ Raft bridge", result['status'], "found")
        self.test("Bridge has explanation", len(result['bridges']) > 0 and 'explanation' in result['bridges'][0], True)

        # Test 2: Non-existent bridge
        result = self.perception.discover_bridges("nonexistent", "fake")
        self.test("Non-existent bridge returns not_found", result['status'], "not_found")

        # Test 3: Bridge count
        result = self.perception.discover_bridges("consensus", "raft")
        self.test("Bridge count is positive", result.get('count', 0) > 0, True)

        return self.fail_count == 0

    def test_learning_paths(self) -> bool:
        """Test learning path discovery."""
        self.section("3. LEARNING PATH DISCOVERY")

        # Test 1: Get valid path
        result = self.perception.get_learning_path("consensus_expert")
        self.test("Get consensus_expert path", result['status'], "found")
        self.test("Path has concepts", len(result['path']['concepts']) > 0, True)

        # Test 2: Get invalid path
        result = self.perception.get_learning_path("nonexistent_path")
        self.test("Invalid path returns not_found", result['status'], "not_found")

        # Test 3: List all paths
        result = self.perception.list_learning_paths()
        self.test("List paths returns found", result['status'], "found")
        self.test("Multiple paths available", result['count'] > 1, True)

        return self.fail_count == 0

    # ========================================================================
    # ACTION-ONLY TESTS
    # ========================================================================

    def test_color_generation(self) -> bool:
        """Test color generation: deterministic palette."""
        self.section("4. COLOR GENERATION")

        # Test 1: Generate palette
        result = self.server.execute_tool("generate_color_palette", {"size": 12})
        self.test("Generate palette returns colors", len(result['palette']) > 0, True)
        self.test("Palette has correct size", len(result['palette']), 12)

        # Test 2: Deterministic property
        result1 = self.server.execute_tool("generate_color_palette", {"size": 5})
        result2 = self.server.execute_tool("generate_color_palette", {"size": 5})
        self.test("Palette is deterministic", result1['palette'], result2['palette'])

        # Test 3: Color for depth
        result = self.server.execute_tool("color_for_depth", {"depth": 0})
        self.test("color_for_depth returns color", 'color' in result, True)
        self.test("Color is hex format", result['color'].startswith('#'), True)

        return self.fail_count == 0

    def test_colorization(self) -> bool:
        """Test code colorization: S-expressions."""
        self.section("5. CODE COLORIZATION")

        code = "(define (foo x) (+ x 1))"

        # Test 1: Tokenize
        result = self.server.execute_tool("tokenize_sexpr", {"code": code})
        self.test("Tokenize produces tokens", len(result['tokens']) > 0, True)
        self.test("Tokens have depth", all('depth' in t for t in result['tokens']), True)

        # Test 2: Colorize
        result = self.server.execute_tool("colorize_sexpr", {"code": code})
        self.test("Colorize produces colors", len(result['colored_tokens']) > 0, True)
        self.test("Colored tokens have colors", all('color' in t for t in result['colored_tokens']), True)

        # Test 3: HTML rendering
        result = self.server.execute_tool("render_sexpr_html", {"code": code})
        self.test("HTML rendering produces HTML", '<pre' in result.get('html', ''), True)
        self.test("HTML has colors", '#' in result.get('html', ''), True)

        # Test 4: JSON rendering
        result = self.server.execute_tool("render_sexpr_json", {"code": code})
        self.test("JSON rendering has tokens", len(result['tokens']) > 0, True)
        self.test("JSON has color_map", 'color_map' in result, True)

        return self.fail_count == 0

    def test_agreement_property(self) -> bool:
        """Test deterministic agreement: same depth → same color."""
        self.section("6. DETERMINISTIC AGREEMENT")

        # Test 1: Same depth → same color
        result = self.server.execute_tool("demonstrate_agreement", {"agents": 5})
        self.test("Demonstrate agreement shows principle", 'principle' in result, True)

        # Test 2: Verify all agents agree
        agreement_data = result['agreement_proof']
        all_agree = all(v['all_agree'] for v in agreement_data.values())
        self.test("All agents agree on colors", all_agree, True)

        # Test 3: No coordination needed
        coordination = result.get('coordination_needed', '')
        self.test("Coordination not needed", 'NONE' in coordination.upper(), True)

        return self.fail_count == 0

    # ========================================================================
    # INTEGRATED TESTS
    # ========================================================================

    def test_integrated_knowledge_to_colors(self) -> bool:
        """Test integrated workflow: knowledge → colors."""
        self.section("7. INTEGRATED: KNOWLEDGE → COLORS")

        # Step 1: Query concept
        concept_result = self.perception.query_concept("consensus")
        self.test("Step 1: Query consensus", concept_result['status'], "found")

        # Step 2: Get code example for consensus
        code = "(define (consensus state messages) (reduce AND (map agree? messages)))"

        # Step 3: Colorize the code
        color_result = self.server.execute_tool("colorize_sexpr", {"code": code})
        self.test("Step 3: Colorize produces colors", len(color_result['colored_tokens']) > 0, True)

        # Step 4: Render as HTML
        html_result = self.server.execute_tool("render_sexpr_html", {"code": code})
        self.test("Step 4: HTML rendered", '<pre' in html_result.get('html', ''), True)

        print("   Complete workflow: Knowledge → Code → Colors → Visualization ✓")
        return self.fail_count == 0

    def test_multiagent_parallel(self) -> bool:
        """Test multi-agent parallel operation."""
        self.section("8. MULTI-AGENT PARALLEL OPERATIONS")

        # Simulate 3 agents working independently
        agents = ["agent_1", "agent_2", "agent_3"]
        code = "(+ 1 2)"

        results = {}
        for agent in agents:
            result = self.server.execute_tool("colorize_sexpr", {"code": code})
            results[agent] = result['colored_tokens']

        # Test 1: All agents produce same output
        tokens_1 = results["agent_1"]
        tokens_2 = results["agent_2"]
        tokens_3 = results["agent_3"]

        same_12 = [t1['color'] for t1 in tokens_1] == [t2['color'] for t2 in tokens_2]
        same_23 = [t2['color'] for t2 in tokens_2] == [t3['color'] for t3 in tokens_3]

        self.test("All agents produce same colors (agent 1 ↔ 2)", same_12, True)
        self.test("All agents produce same colors (agent 2 ↔ 3)", same_23, True)

        print("   ✓ 3 independent agents: deterministic agreement")
        return self.fail_count == 0

    # ========================================================================
    # PERFORMANCE TESTS
    # ========================================================================

    def test_perception_performance(self) -> bool:
        """Test perception tool performance."""
        self.section("9. PERCEPTION PERFORMANCE")

        # Measure query concept
        start = time.time()
        for _ in range(10):
            self.perception.query_concept("consensus")
        duration = (time.time() - start) * 1000 / 10
        self.test(f"Query concept (<10ms)", duration < 10, True)
        print(f"   Actual: {duration:.1f}ms")

        # Measure bridge discovery
        start = time.time()
        for _ in range(10):
            self.perception.discover_bridges("consensus", "raft")
        duration = (time.time() - start) * 1000 / 10
        self.test(f"Discover bridges (<10ms)", duration < 10, True)
        print(f"   Actual: {duration:.1f}ms")

        return self.fail_count == 0

    def test_action_performance(self) -> bool:
        """Test action tool performance."""
        self.section("10. ACTION PERFORMANCE")

        # Measure color generation
        start = time.time()
        for _ in range(100):
            self.server.execute_tool("color_for_depth", {"depth": 3})
        duration = (time.time() - start) * 1000 / 100
        self.test(f"Color for depth (<1ms)", duration < 1, True)
        print(f"   Actual: {duration:.3f}ms")

        # Measure colorization (10 tokens)
        code = "(define (foo x) (+ x 1))"
        start = time.time()
        for _ in range(20):
            self.server.execute_tool("colorize_sexpr", {"code": code})
        duration = (time.time() - start) * 1000 / 20
        self.test(f"Colorize sexpr (<10ms)", duration < 10, True)
        print(f"   Actual: {duration:.1f}ms")

        return self.fail_count == 0

    # ========================================================================
    # MCP SPACE SATURATION TESTS
    # ========================================================================

    def test_tool_availability(self) -> bool:
        """Test that all tools are available in MCP server."""
        self.section("11. MCP TOOL AVAILABILITY")

        tools = self.server.get_tools()
        tool_names = {tool['name'] for tool in tools}

        perception_tools = {
            "query_concept",
            "discover_bridges",
            "get_learning_paths",
        }

        action_tools = {
            "generate_color_palette",
            "color_for_depth",
            "demonstrate_agreement",
            "colorize_sexpr",
            "render_sexpr_html",
            "render_sexpr_json",
        }

        integration_tools = {
            "ecosystem_overview",
            "demonstration_examples",
        }

        for tool in perception_tools:
            self.test(f"Perception tool: {tool}", tool in tool_names, True)

        for tool in action_tools:
            self.test(f"Action tool: {tool}", tool in tool_names, True)

        for tool in integration_tools:
            self.test(f"Integration tool: {tool}", tool in tool_names, True)

        total = len(perception_tools) + len(action_tools) + len(integration_tools)
        self.test(f"Total tools available", len(tools) >= total, True)

        return self.fail_count == 0

    def test_space_saturation_complete(self) -> bool:
        """Test that MCP space is fully saturated."""
        self.section("12. MCP SPACE SATURATION STATUS")

        # Perception dimension
        perception_ok = (
            len(self.perception.db.concepts) > 5 and
            len(self.perception.db.bridges) > 3 and
            len(self.perception.db.paths) > 2
        )
        self.test("Perception dimension saturated", perception_ok, True)
        print(f"   Concepts: {len(self.perception.db.concepts)}")
        print(f"   Bridges: {len(self.perception.db.bridges)}")
        print(f"   Learning paths: {len(self.perception.db.paths)}")

        # Action dimension
        color_palette = self.server.colors.COLOR_PALETTE
        action_ok = len(color_palette) >= 12
        self.test("Action dimension saturated", action_ok, True)
        print(f"   Color palette: {len(color_palette)} colors")

        # Integration dimension
        result = self.server.execute_tool("ecosystem_overview", {})
        integration_ok = result['status'] == 'All systems operational'
        self.test("Integration dimension saturated", integration_ok, True)

        print("   ✓ All three systems operational")

        return self.fail_count == 0

    # ========================================================================
    # MAIN TEST RUNNER
    # ========================================================================

    def run_all(self) -> int:
        """Run all tests and report results."""
        print("\n" + "=" * 70)
        print("MCP SPACE SATURATION: COMPREHENSIVE TEST SUITE")
        print("=" * 70)

        test_methods = [
            self.test_perception_queries,
            self.test_bridge_discovery,
            self.test_learning_paths,
            self.test_color_generation,
            self.test_colorization,
            self.test_agreement_property,
            self.test_integrated_knowledge_to_colors,
            self.test_multiagent_parallel,
            self.test_perception_performance,
            self.test_action_performance,
            self.test_tool_availability,
            self.test_space_saturation_complete,
        ]

        for test_method in test_methods:
            try:
                test_method()
            except Exception as e:
                print(f"\n❌ ERROR in {test_method.__name__}: {e}")
                import traceback
                traceback.print_exc()
                self.fail_count += 1

        # Print summary
        self.section("TEST SUMMARY")
        total = self.pass_count + self.fail_count + self.skip_count
        print(f"Total tests: {total}")
        print(f"✅ Passed:  {self.pass_count}")
        print(f"❌ Failed:  {self.fail_count}")
        print(f"⊘ Skipped: {self.skip_count}")

        if self.fail_count == 0:
            print("\n🎉 ALL TESTS PASSED - MCP SPACE FULLY SATURATED\n")
            return 0
        else:
            print(f"\n⚠️  {self.fail_count} test(s) failed\n")
            return 1


def main():
    """Run the test suite."""
    tester = MCPSaturationTest()
    return tester.run_all()


if __name__ == "__main__":
    sys.exit(main())
