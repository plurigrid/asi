#!/usr/bin/env python3
"""
Test Suite: Phase 3B Multi-Agent Swarm Discovery
================================================

Comprehensive testing of:
1. Specialized agent functionality
2. Swarm coordination
3. Consensus building
4. Cross-agent learning
5. Meta-analysis
"""

from phase_3_agent_swarm import (
    AgentSwarm, SpecializedAgent, PatternConsensus,
    DepthAnalyzer, ConceptAnalyzer, ColorAnalyzer,
    TheoryAnalyzer, MetaAnalyzer
)
from phase_3_5d_patterns import PatternExtractor5D


def test_agent_initialization():
    """Test that agents initialize correctly."""
    depth_agent = DepthAnalyzer("test_depth")
    assert depth_agent.agent_id == "test_depth"
    assert depth_agent.specialization == "depth"
    assert len(depth_agent.discoveries) == 0
    print("✅ test_agent_initialization")
    return True


def test_depth_analyzer():
    """Test depth analyzer specialization."""
    extractor = PatternExtractor5D()
    concept = {
        'name': 'test',
        'theoretical_foundation': 'test',
        'related_implementations': ['impl1', 'impl2', 'impl3']
    }
    patterns = extractor.extract_from_concept(concept, depth=2)

    agent = DepthAnalyzer("test_depth")
    findings = agent.analyze(patterns)

    assert len(findings) > 0
    assert findings[0][0] == "Depth Concentration Pattern"
    assert 0 <= findings[0][1] <= 1.0
    assert len(findings[0][2]) > 0
    print("✅ test_depth_analyzer")
    return True


def test_concept_analyzer():
    """Test concept analyzer specialization."""
    extractor = PatternExtractor5D()
    concept1 = {
        'name': 'consensus',
        'theoretical_foundation': 'Byzantine',
        'related_implementations': ['Raft', 'Paxos']
    }
    concept2 = {
        'name': 'replication',
        'theoretical_foundation': 'SMR',
        'related_implementations': ['Primary', 'Quorum']
    }
    patterns = extractor.extract_from_concept(concept1, depth=1)
    patterns += extractor.extract_from_concept(concept2, depth=1)

    agent = ConceptAnalyzer("test_concept")
    findings = agent.analyze(patterns)

    assert len(findings) > 0
    assert findings[0][0] == "Concept Clustering Pattern"
    assert 0 <= findings[0][1] <= 1.0
    print("✅ test_concept_analyzer")
    return True


def test_color_analyzer():
    """Test color analyzer specialization."""
    extractor = PatternExtractor5D()
    concept = {
        'name': 'test',
        'theoretical_foundation': 'test',
        'related_implementations': ['impl1', 'impl2', 'impl3', 'impl4']
    }
    patterns = extractor.extract_from_concept(concept, depth=1)

    agent = ColorAnalyzer("test_color")
    findings = agent.analyze(patterns)

    assert len(findings) > 0
    assert findings[0][0] == "Color Dominance Pattern"
    assert 0 <= findings[0][1] <= 1.0
    print("✅ test_color_analyzer")
    return True


def test_theory_analyzer():
    """Test theory analyzer specialization."""
    extractor = PatternExtractor5D()
    concept = {
        'name': 'consensus',
        'theoretical_foundation': 'Byzantine Generals',
        'related_implementations': ['Raft', 'Paxos', 'PBFT']
    }
    patterns = extractor.extract_from_concept(concept, depth=1)

    agent = TheoryAnalyzer("test_theory")
    findings = agent.analyze(patterns)

    assert len(findings) > 0
    assert findings[0][0] == "Theory-Implementation Bridge Pattern"
    assert 0 <= findings[0][1] <= 1.0
    print("✅ test_theory_analyzer")
    return True


def test_agent_learning():
    """Test that agents can learn from peers."""
    agent = DepthAnalyzer("test_learn")
    other_discoveries = {
        'agent_b': [('pattern1', 0.8, ['evidence'])],
        'agent_c': [('pattern2', 0.9, ['evidence'])]
    }

    agent.learn(other_discoveries)
    assert len(agent.learning_history) == 1
    assert agent.learning_history[0]['peer_discoveries'] == other_discoveries
    print("✅ test_agent_learning")
    return True


def test_swarm_initialization():
    """Test swarm initialization."""
    swarm = AgentSwarm(num_agents=4)

    assert len(swarm.agents) == 4
    assert swarm.meta_analyzer is not None
    assert len(swarm.consensus_patterns) == 0
    assert len(swarm.voting_history) == 0
    print("✅ test_swarm_initialization")
    return True


def test_swarm_discovery():
    """Test swarm discovery process."""
    extractor = PatternExtractor5D()
    concept = {
        'name': 'consensus',
        'theoretical_foundation': 'Byzantine Generals',
        'related_implementations': ['Raft', 'Paxos', 'PBFT', 'PoW']
    }
    patterns = extractor.extract_from_concept(concept, depth=1)

    swarm = AgentSwarm(num_agents=4)
    consensus_patterns = swarm.discover(patterns)

    assert len(consensus_patterns) > 0
    assert len(swarm.voting_history) > 0
    assert len(swarm.swarm_learning_history) > 0
    print("✅ test_swarm_discovery")
    return True


def test_consensus_building():
    """Test consensus pattern building."""
    extractor = PatternExtractor5D()
    concept = {
        'name': 'test',
        'theoretical_foundation': 'test',
        'related_implementations': ['impl1', 'impl2']
    }
    patterns = extractor.extract_from_concept(concept, depth=1)

    swarm = AgentSwarm(num_agents=4)
    consensus_patterns = swarm.discover(patterns)

    assert len(consensus_patterns) > 0

    for cp in consensus_patterns:
        assert isinstance(cp, PatternConsensus)
        assert cp.name is not None
        assert 0 <= cp.consensus_confidence <= 1.0
        assert 0 <= cp.agreement_level <= 1.0
        assert len(cp.agent_votes) > 0
        assert len(cp.meta_evidence) > 0
    print("✅ test_consensus_building")
    return True


def test_agreement_level_calculation():
    """Test that agreement levels are calculated correctly."""
    extractor = PatternExtractor5D()
    concepts = []
    for i in range(3):
        concepts.append({
            'name': f'concept{i}',
            'theoretical_foundation': 'test',
            'related_implementations': ['impl1', 'impl2']
        })

    all_patterns = []
    for i, concept in enumerate(concepts):
        all_patterns.extend(extractor.extract_from_concept(concept, depth=i))

    swarm = AgentSwarm(num_agents=4)
    consensus_patterns = swarm.discover(all_patterns)

    for cp in consensus_patterns:
        expected_max_agreement = len(cp.agent_votes) / len(swarm.agents)
        assert cp.agreement_level <= expected_max_agreement + 0.01

    print("✅ test_agreement_level_calculation")
    return True


def test_high_consensus_detection():
    """Test detection of high-consensus patterns."""
    extractor = PatternExtractor5D()
    # Create patterns that will be analyzed by multiple agents
    concept = {
        'name': 'consensus',
        'theoretical_foundation': 'Byzantine',
        'related_implementations': ['Raft', 'Paxos', 'PBFT', 'PoW', 'PoS']
    }
    patterns = extractor.extract_from_concept(concept, depth=1)

    swarm = AgentSwarm(num_agents=4)
    consensus_patterns = swarm.discover(patterns)

    report = swarm.get_report()
    assert 'high_consensus_patterns' in report
    assert report['high_consensus_patterns'] >= 0
    assert report['total_consensus_patterns'] >= report['high_consensus_patterns']

    print("✅ test_high_consensus_detection")
    return True


def test_swarm_report_generation():
    """Test swarm report generation."""
    extractor = PatternExtractor5D()
    concept = {
        'name': 'test',
        'theoretical_foundation': 'test',
        'related_implementations': ['impl1', 'impl2']
    }
    patterns = extractor.extract_from_concept(concept, depth=1)

    swarm = AgentSwarm(num_agents=4)
    swarm.discover(patterns)

    report = swarm.get_report()

    # Check report structure
    assert 'swarm_size' in report
    assert 'total_consensus_patterns' in report
    assert 'high_consensus_patterns' in report
    assert 'average_consensus_confidence' in report
    assert 'consensus_patterns' in report
    assert 'agent_summaries' in report
    assert 'meta_analyzer_summary' in report
    assert 'learning_iterations' in report
    assert 'deterministic_agreement' in report

    # Check values
    assert report['swarm_size'] == 4
    assert report['total_consensus_patterns'] > 0
    assert 0 <= report['average_consensus_confidence'] <= 1.0
    assert len(report['agent_summaries']) == 4
    assert report['deterministic_agreement'] == "✅ Multiple agents coordinate without explicit messages"

    print("✅ test_swarm_report_generation")
    return True


def test_specialized_agents_in_swarm():
    """Test that swarm contains correct specialized agents."""
    swarm = AgentSwarm(num_agents=4)

    agent_types = {agent.specialization for agent in swarm.agents}
    expected_types = {'depth', 'concept', 'color', 'theory'}

    assert agent_types == expected_types
    assert swarm.meta_analyzer.specialization == 'meta'

    print("✅ test_specialized_agents_in_swarm")
    return True


def test_multiple_discovery_rounds():
    """Test multiple rounds of discovery and learning."""
    extractor = PatternExtractor5D()

    # Round 1
    concept1 = {
        'name': 'consensus',
        'theoretical_foundation': 'Byzantine',
        'related_implementations': ['Raft', 'Paxos']
    }
    patterns1 = extractor.extract_from_concept(concept1, depth=1)

    swarm = AgentSwarm(num_agents=4)
    swarm.discover(patterns1)

    round1_patterns = len(swarm.consensus_patterns)
    round1_learning = len(swarm.swarm_learning_history)
    round1_agent_discoveries = sum(len(a.discoveries) for a in swarm.agents)

    # Round 2
    concept2 = {
        'name': 'replication',
        'theoretical_foundation': 'SMR',
        'related_implementations': ['Primary', 'Quorum', 'Chain']
    }
    patterns2 = extractor.extract_from_concept(concept2, depth=2)

    swarm.discover(patterns2)

    round2_patterns = len(swarm.consensus_patterns)
    round2_learning = len(swarm.swarm_learning_history)
    round2_agent_discoveries = sum(len(a.discoveries) for a in swarm.agents)

    # Learning and agent discoveries should accumulate
    # Consensus patterns reset per round (correct behavior)
    assert round2_learning > round1_learning
    assert round2_agent_discoveries > round1_agent_discoveries
    assert round1_patterns > 0
    assert round2_patterns > 0

    print("✅ test_multiple_discovery_rounds")
    return True


def test_meta_analyzer_functionality():
    """Test meta-analyzer can assess consensus."""
    meta = MetaAnalyzer("test_meta")

    agent_votes = {
        'agent_a': [('pattern1', 0.8, ['evidence'])],
        'agent_b': [('pattern1', 0.9, ['evidence']), ('pattern2', 0.7, ['evidence'])],
        'agent_c': [('pattern1', 0.85, ['evidence']), ('pattern3', 0.6, ['evidence'])]
    }

    findings = meta.analyze(agent_votes)

    # Meta-analyzer should find high-consensus patterns
    assert len(findings) > 0
    assert findings[0][0] == "High-Consensus Pattern Discovery"

    print("✅ test_meta_analyzer_functionality")
    return True


def run_all_tests():
    """Run all tests."""
    tests = [
        test_agent_initialization,
        test_depth_analyzer,
        test_concept_analyzer,
        test_color_analyzer,
        test_theory_analyzer,
        test_agent_learning,
        test_swarm_initialization,
        test_swarm_discovery,
        test_consensus_building,
        test_agreement_level_calculation,
        test_high_consensus_detection,
        test_swarm_report_generation,
        test_specialized_agents_in_swarm,
        test_multiple_discovery_rounds,
        test_meta_analyzer_functionality,
    ]

    print("\n" + "=" * 70)
    print("PHASE 3B SWARM TEST SUITE")
    print("=" * 70 + "\n")

    passed = 0
    failed = 0

    for test in tests:
        try:
            if test():
                passed += 1
        except Exception as e:
            print(f"❌ {test.__name__}: {e}")
            failed += 1

    print("\n" + "=" * 70)
    print(f"RESULTS: {passed}/{len(tests)} PASSED")
    print("=" * 70)

    if failed == 0:
        print("🎉 ALL TESTS PASSING")
        return 0
    else:
        print(f"⚠️  {failed} tests failed")
        return 1


if __name__ == "__main__":
    import sys
    sys.exit(run_all_tests())
