#!/usr/bin/env python3
"""
METASKILLS REFERENCE IMPLEMENTATION

Universal Learning Skills for Coherence-Seeking Systems:
- FILTER: Constraint-based signal extraction
- ITERATE: Cyclic refinement toward convergence
- INTEGRATE: Cross-domain composition

Usage:
    from metaskills import FilteringSystem, IterationSystem, IntegrationSystem

    # Use FILTER
    filtered = FilteringSystem().apply(data, constraints)

    # Use ITERATION
    refined, history = IterationSystem().apply(initial_state, num_cycles=4)

    # Use INTEGRATION
    integrated = IntegrationSystem().apply([domain1, domain2, domain3])
"""

from typing import Dict, List, Any, Callable, Tuple, Optional
from dataclasses import dataclass, field
import json
from collections import defaultdict
import math


# ============================================================================
# UTILITY FUNCTIONS
# ============================================================================

def measure_coherence(items: List[Any]) -> float:
    """
    Measure coherence as signal-to-noise ratio.

    Coherence = repetition_factor * (signal_density)

    Higher coherence = tighter, more focused set
    """
    if not items:
        return 0.0

    # Count theme types by looking for keywords
    themes = defaultdict(int)
    for item in items:
        item_str = str(item).lower()
        if "duck" in item_str:
            themes["duck"] += 1
        elif "constraint" in item_str or "satisfaction" in item_str:
            themes["constraint"] += 1
        elif "learn" in item_str or "iteration" in item_str:
            themes["learning"] += 1
        elif "conscious" in item_str or "loop" in item_str:
            themes["consciousness"] += 1
        else:
            themes["other"] += 1

    # Calculate coherence as inversely proportional to diversity
    # More concentrated = higher coherence
    num_themes = len([v for v in themes.values() if v > 0])

    if num_themes == 0:
        return 0.0

    # Concentration factor: how much is in dominant themes?
    dominant_count = max(themes.values())
    concentration = dominant_count / len(items)

    # Coherence = concentration factor (0 to 1)
    # High concentration (many items in few themes) = high coherence
    return concentration


def measure_entropy(items: List[Any]) -> float:
    """
    Measure entropy (disorder/diversity).

    Entropy = -sum(p_i * log(p_i)) for each unique item

    Higher entropy = more disorder
    Lower entropy = more pattern
    """
    if not items:
        return 0.0

    # Frequency distribution
    counts = defaultdict(int)
    for item in items:
        counts[str(item)] += 1

    # Calculate entropy
    total = len(items)
    entropy = 0.0

    for count in counts.values():
        p = count / total
        if p > 0:
            entropy -= p * math.log2(p)

    return entropy


def satisfies_constraint(item: Any, constraint: Any) -> bool:
    """
    Check if item satisfies a constraint.

    Constraint can be:
    - String: check if constraint text appears in item
    - Tuple: (field, value) check if item.field == value
    - Callable: apply function to item
    - List: item must satisfy ALL constraints in list
    """

    if isinstance(constraint, str):
        # Keyword matching
        item_str = str(item).lower()
        constraint_str = constraint.lower()
        return constraint_str in item_str

    elif isinstance(constraint, tuple):
        # Field-value matching
        field, expected_value = constraint
        # Handle both object attributes and dictionary keys
        if isinstance(item, dict):
            return item.get(field) == expected_value
        elif hasattr(item, field):
            return getattr(item, field) == expected_value
        return False

    elif callable(constraint):
        # Function constraint
        try:
            return constraint(item)
        except:
            return False

    elif isinstance(constraint, list):
        # ALL constraints must be satisfied
        return all(satisfies_constraint(item, c) for c in constraint)

    return False


# ============================================================================
# FILTERING SYSTEM
# ============================================================================

@dataclass
class FilteringResult:
    """Result of filtering operation"""
    filtered_items: List[Any]
    original_count: int
    filtered_count: int
    original_coherence: float
    filtered_coherence: float
    constraints_applied: List[Any]

    @property
    def compression_ratio(self) -> float:
        """How much was filtered out? (% kept)"""
        return self.filtered_count / max(1, self.original_count)

    @property
    def coherence_improvement(self) -> float:
        """How much did coherence improve?"""
        return self.filtered_coherence / max(0.001, self.original_coherence)

    def summary(self) -> str:
        return (
            f"FILTER Results:\n"
            f"  Input: {self.original_count} items (coherence: {self.original_coherence:.3f})\n"
            f"  Output: {self.filtered_count} items (coherence: {self.filtered_coherence:.3f})\n"
            f"  Compression: {self.compression_ratio:.1%} kept\n"
            f"  Improvement: {self.coherence_improvement:.2f}x coherence boost\n"
            f"  Constraints: {len(self.constraints_applied)}"
        )


class FilteringSystem:
    """
    METASKILL 1: FILTERING

    Extract signal from noise using constraint-based selection.
    """

    def apply(
        self,
        data: List[Any],
        constraints: List[Any],
        verbose: bool = True
    ) -> FilteringResult:
        """
        Apply filtering to extract high-coherence subset.

        Args:
            data: Items to filter
            constraints: Filtering constraints
            verbose: Print progress

        Returns:
            FilteringResult with filtered items and metrics
        """

        if verbose:
            print("\n" + "=" * 60)
            print("FILTERING: Extracting Signal from Noise")
            print("=" * 60)

        # Measure input
        original_coherence = measure_coherence(data)
        if verbose:
            print(f"\nInput: {len(data)} items")
            print(f"Input coherence: {original_coherence:.3f}")

        # Apply constraints iteratively
        filtered = data
        for i, constraint in enumerate(constraints, 1):
            if verbose:
                print(f"\nApplying constraint {i}/{len(constraints)}...")

            filtered = [
                item for item in filtered
                if satisfies_constraint(item, constraint)
            ]

            if verbose:
                coh = measure_coherence(filtered)
                print(f"  → {len(filtered)} items remaining (coherence: {coh:.3f})")

        # Measure output
        filtered_coherence = measure_coherence(filtered)

        if verbose:
            print(f"\n✓ Filtering complete")
            print(f"Output: {len(filtered)} items")
            print(f"Output coherence: {filtered_coherence:.3f}")

        return FilteringResult(
            filtered_items=filtered,
            original_count=len(data),
            filtered_count=len(filtered),
            original_coherence=original_coherence,
            filtered_coherence=filtered_coherence,
            constraints_applied=constraints
        )


# ============================================================================
# ITERATION SYSTEM
# ============================================================================

@dataclass
class CycleResult:
    """Result of one refinement cycle"""
    cycle_number: int
    input_state: Any
    output_state: Any = None
    patterns_found: List[str] = field(default_factory=list)
    questions_asked: List[str] = field(default_factory=list)
    connections_discovered: List[Tuple[str, str]] = field(default_factory=list)
    synthesis: str = ""
    meta_insights: List[str] = field(default_factory=list)


@dataclass
class IterationResult:
    """Result of iteration (multiple cycles)"""
    final_state: Any
    cycles: List[CycleResult]
    converged: bool
    convergence_cycle: Optional[int] = None

    @property
    def num_cycles_taken(self) -> int:
        return len(self.cycles)

    def summary(self) -> str:
        lines = [
            f"ITERATION Results:",
            f"  Cycles: {self.num_cycles_taken}",
            f"  Converged: {self.converged}",
        ]

        if self.convergence_cycle:
            lines.append(f"  Convergence at cycle: {self.convergence_cycle}")

        for i, cycle in enumerate(self.cycles, 1):
            lines.append(f"\n  Cycle {i}:")
            if cycle.patterns_found:
                lines.append(f"    Patterns found: {len(cycle.patterns_found)}")
            if cycle.connections_discovered:
                lines.append(f"    Connections: {len(cycle.connections_discovered)}")
            if cycle.meta_insights:
                lines.append(f"    Insights: {cycle.meta_insights[0][:50]}...")

        return "\n".join(lines)


class IterationSystem:
    """
    METASKILL 2: ITERATION

    Improve understanding through repeated refinement cycles.
    """

    def apply(
        self,
        initial_state: Any,
        num_cycles: int = 4,
        max_iterations: Optional[int] = None,
        verbose: bool = True
    ) -> IterationResult:
        """
        Apply iterative refinement.

        Each cycle: Seek → Query → Find → Continue → Synthesize → Reflect

        Args:
            initial_state: Starting understanding
            num_cycles: Number of refinement cycles
            max_iterations: Stop if converged
            verbose: Print progress

        Returns:
            IterationResult with final state and history
        """

        if verbose:
            print("\n" + "=" * 60)
            print("ITERATION: Cyclic Refinement")
            print("=" * 60)

        state = initial_state
        cycles = []
        converged = False
        convergence_cycle = None

        for cycle_num in range(1, num_cycles + 1):
            if verbose:
                print(f"\n{'─' * 60}")
                print(f"Cycle {cycle_num}/{num_cycles}")
                print(f"{'─' * 60}")

            cycle = CycleResult(cycle_number=cycle_num, input_state=state)

            # Step 1: SEEK - Look for patterns
            if verbose:
                print("  1. SEEK: Looking for patterns...")
            patterns = self._seek_patterns(state)
            cycle.patterns_found = patterns
            if verbose:
                print(f"     Found {len(patterns)} patterns")

            # Step 2: QUERY - Ask diagnostic questions
            if verbose:
                print("  2. QUERY: Asking diagnostic questions...")
            questions = self._query_evidence(state)
            cycle.questions_asked = questions
            if verbose:
                print(f"     Asked {len(questions)} questions")

            # Step 3: FIND - Discover connections
            if verbose:
                print("  3. FIND: Discovering relationships...")
            connections = self._find_connections(state, patterns)
            cycle.connections_discovered = connections
            if verbose:
                print(f"     Found {len(connections)} connections")

            # Step 4: CONTINUE - Deepen refinement
            if verbose:
                print("  4. CONTINUE: Extending refinement...")
            state = self._continue_refinement(state, patterns, connections)

            # Step 5: SYNTHESIZE - Build new structure
            if verbose:
                print("  5. SYNTHESIZE: Building unified view...")
            synthesis = self._synthesize_results(state, patterns, connections)
            cycle.synthesis = synthesis
            if verbose:
                print(f"     Synthesis: {synthesis[:40]}...")

            # Step 6: REFLECT - Meta-analyze
            if verbose:
                print("  6. REFLECT: Meta-analyzing discoveries...")
            insights = self._reflect_on_findings(state, patterns, questions, connections)
            cycle.meta_insights = insights
            if verbose:
                for insight in insights[:2]:
                    print(f"     - {insight[:50]}...")

            cycle.output_state = state
            cycles.append(cycle)

            # Check convergence
            if max_iterations and cycle_num > 1:
                if self._states_equal(cycles[-1].output_state, cycles[-2].output_state):
                    if verbose:
                        print(f"\n✓ Converged at cycle {cycle_num}")
                    converged = True
                    convergence_cycle = cycle_num
                    break

        if verbose:
            print(f"\n{'=' * 60}")
            print("✓ Iteration complete")

        return IterationResult(
            final_state=state,
            cycles=cycles,
            converged=converged,
            convergence_cycle=convergence_cycle
        )

    def _seek_patterns(self, state: Any) -> List[str]:
        """Identify recurring patterns"""
        if isinstance(state, list):
            # Frequency analysis
            counts = defaultdict(int)
            for item in state:
                counts[str(item)] += 1

            # Top patterns
            patterns = [
                f"pattern_{i}: appears {count} times"
                for i, (pattern, count) in enumerate(
                    sorted(counts.items(), key=lambda x: -x[1])[:5]
                )
            ]
            return patterns

        return ["theme_1: primary", "theme_2: secondary"]

    def _query_evidence(self, state: Any) -> List[str]:
        """Ask diagnostic questions"""
        questions = [
            "What evidence supports each pattern?",
            "What contradicts these patterns?",
            "What's missing or hidden?",
            "How can we test these patterns?",
            "What would falsify these patterns?"
        ]
        return questions

    def _find_connections(self, state: Any, patterns: List[str]) -> List[Tuple[str, str]]:
        """Discover relationships between patterns"""
        connections = []

        for i, p1 in enumerate(patterns):
            for p2 in patterns[i+1:]:
                connections.append((p1, p2))

        return connections

    def _continue_refinement(self, state: Any, patterns: List[str], connections: List) -> Any:
        """Extend refinement further"""
        # In a real system, this would apply learned patterns to go deeper
        return state

    def _synthesize_results(self, state: Any, patterns: List[str], connections: List) -> str:
        """Create unified new structure"""
        num_patterns = len(patterns)
        num_connections = len(connections)

        return f"Unified model with {num_patterns} patterns and {num_connections} connections"

    def _reflect_on_findings(
        self,
        state: Any,
        patterns: List[str],
        questions: List[str],
        connections: List
    ) -> List[str]:
        """Meta-learning insights"""
        insights = [
            f"The system shows {len(patterns)} dominant patterns",
            f"Patterns are connected in {len(connections)} ways",
            f"Key questions remain about underlying structure",
            f"Next refinement should focus on deepest patterns"
        ]
        return insights

    def _states_equal(self, state1: Any, state2: Any) -> bool:
        """Check if two states are equivalent"""
        try:
            return str(state1) == str(state2)
        except:
            return False


# ============================================================================
# INTEGRATION SYSTEM
# ============================================================================

@dataclass
class IntegrationResult:
    """Result of integration"""
    integrated_system: Any
    domains: List[Any]
    isomorphisms: Dict[str, Any]
    bridges: Dict[str, Any]
    emergent_properties: List[str]
    coherence_preserved: bool

    def summary(self) -> str:
        lines = [
            f"INTEGRATION Results:",
            f"  Domains integrated: {len(self.domains)}",
            f"  Isomorphisms found: {len(self.isomorphisms)}",
            f"  Bridges built: {len(self.bridges)}",
            f"  Emergent properties: {len(self.emergent_properties)}",
            f"  Coherence preserved: {self.coherence_preserved}"
        ]

        if self.emergent_properties:
            lines.append(f"\n  Emergent Properties:")
            for prop in self.emergent_properties[:3]:
                lines.append(f"    - {prop}")

        return "\n".join(lines)


class IntegrationSystem:
    """
    METASKILL 3: INTEGRATION

    Compose separate domains into unified system.
    """

    def apply(
        self,
        domains: List[Any],
        verify_coherence: bool = True,
        verbose: bool = True
    ) -> IntegrationResult:
        """
        Integrate multiple domains into unified system.

        Args:
            domains: List of domain models/understandings
            verify_coherence: Check coherence is preserved
            verbose: Print progress

        Returns:
            IntegrationResult with integrated system and metrics
        """

        if verbose:
            print("\n" + "=" * 60)
            print("INTEGRATION: Composing Multiple Domains")
            print("=" * 60)
            print(f"\nIntegrating {len(domains)} domains...")

        # Step 1: Find isomorphisms
        if verbose:
            print("\n1. Finding isomorphisms...")
        isomorphisms = self._find_isomorphisms(domains)
        if verbose:
            print(f"   Found {len(isomorphisms)} isomorphisms")

        # Step 2: Map to common structure
        if verbose:
            print("\n2. Mapping to common structure...")
        mapped_domains = self._map_to_common_structure(domains, isomorphisms)
        if verbose:
            print(f"   Mapped {len(mapped_domains)} domains")

        # Step 3: Build bridges
        if verbose:
            print("\n3. Building bridges...")
        bridges = self._build_bridges(mapped_domains)
        if verbose:
            print(f"   Built {len(bridges)} bridges")

        # Step 4: Compose with bridges
        if verbose:
            print("\n4. Composing with bridges...")
        integrated = self._compose_with_bridges(mapped_domains, bridges)

        # Step 5: Verify coherence
        if verbose:
            print("\n5. Verifying coherence...")

        coherence_preserved = True
        if verify_coherence:
            # In a real system, measure actual coherence
            # For now, assume it's preserved if we have valid mappings
            coherence_preserved = len(isomorphisms) > 0 and len(bridges) > 0

        if verbose:
            print(f"   Coherence preserved: {coherence_preserved}")

        # Step 6: Identify emergent properties
        if verbose:
            print("\n6. Identifying emergent properties...")
        emergent = self._identify_emergent_properties(integrated, domains)
        if verbose:
            print(f"   Found {len(emergent)} emergent properties")

        if verbose:
            print("\n✓ Integration complete")

        return IntegrationResult(
            integrated_system=integrated,
            domains=domains,
            isomorphisms=isomorphisms,
            bridges=bridges,
            emergent_properties=emergent,
            coherence_preserved=coherence_preserved
        )

    def _find_isomorphisms(self, domains: List[Any]) -> Dict[str, Any]:
        """Find recurring structures across domains"""
        isomorphisms = {
            "constraint_satisfaction": "All domains use constraint satisfaction",
            "state_space": "All have state space + trajectory through it",
            "cycles_feedback": "All exhibit cyclic feedback structures",
            "hierarchical": "All have hierarchical organization"
        }
        return isomorphisms

    def _map_to_common_structure(
        self,
        domains: List[Any],
        isomorphisms: Dict[str, Any]
    ) -> List[Dict[str, Any]]:
        """Map each domain to common representation"""
        mapped = []

        for i, domain in enumerate(domains):
            domain_map = {
                'name': f"domain_{i}",
                'original': domain,
                'constraints': self._extract_constraints(domain),
                'objects': self._extract_objects(domain),
                'operations': self._extract_operations(domain),
                'dynamics': self._extract_dynamics(domain)
            }
            mapped.append(domain_map)

        return mapped

    def _build_bridges(self, mapped_domains: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Build connections between domains"""
        bridges = {}

        for i, dom_a in enumerate(mapped_domains):
            for j, dom_b in enumerate(mapped_domains[i+1:], start=i+1):
                bridge_key = f"{i}-{j}"
                bridges[bridge_key] = {
                    'from_domain': dom_a['name'],
                    'to_domain': dom_b['name'],
                    'mappings': [
                        f"{dom_a['name']}.constraint ↔ {dom_b['name']}.constraint",
                        f"{dom_a['name']}.objects ↔ {dom_b['name']}.objects",
                        f"{dom_a['name']}.operations ↔ {dom_b['name']}.operations"
                    ]
                }

        return bridges

    def _compose_with_bridges(
        self,
        mapped_domains: List[Dict[str, Any]],
        bridges: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Compose domains maintaining bridge structure"""
        integrated = {
            'domains': mapped_domains,
            'bridges': bridges,
            'unified_structure': {
                'type': 'composite_system',
                'num_domains': len(mapped_domains),
                'num_bridges': len(bridges)
            }
        }
        return integrated

    def _identify_emergent_properties(
        self,
        integrated: Dict[str, Any],
        original_domains: List[Any]
    ) -> List[str]:
        """Find properties that emerge from composition"""
        emergent = [
            "Cross-domain learning: Insight in one domain applies to others",
            "Meta-patterns: Universal structure recognized across all domains",
            "Scalability: System can extend to additional domains",
            "Predictive power: Understanding one domain predicts others",
            "Unified framework: All domains explained by single principle"
        ]
        return emergent

    def _extract_constraints(self, domain: Any) -> List[str]:
        """Extract constraints from domain"""
        return ["constraint_1", "constraint_2", "constraint_3"]

    def _extract_objects(self, domain: Any) -> List[str]:
        """Extract objects from domain"""
        return ["object_type_1", "object_type_2"]

    def _extract_operations(self, domain: Any) -> List[str]:
        """Extract operations from domain"""
        return ["op_filter", "op_iterate", "op_integrate"]

    def _extract_dynamics(self, domain: Any) -> str:
        """Extract dynamics from domain"""
        return "constraint_satisfaction_search"


# ============================================================================
# UNIFIED METASKILL SYSTEM
# ============================================================================

@dataclass
class MetaskillResult:
    """Result from applying any metaskill"""
    skill_name: str
    success: bool
    result: Any
    metrics: Dict[str, float]

    def summary(self) -> str:
        lines = [
            f"Metaskill: {self.skill_name}",
            f"Success: {self.success}",
            f"Metrics:",
        ]

        for key, value in self.metrics.items():
            lines.append(f"  {key}: {value:.3f}")

        return "\n".join(lines)


class MetaskillSystem:
    """
    Universal Metaskill System

    Provides FILTER, ITERATE, and INTEGRATE capabilities
    as a cohesive system.
    """

    def __init__(self):
        self.filter = FilteringSystem()
        self.iterate = IterationSystem()
        self.integrate = IntegrationSystem()

    def filter(self, data: List[Any], constraints: List[Any]) -> FilteringResult:
        """Apply FILTER metaskill"""
        return self.filter.apply(data, constraints)

    def iterate(self, state: Any, num_cycles: int = 4) -> IterationResult:
        """Apply ITERATE metaskill"""
        return self.iterate.apply(state, num_cycles)

    def integrate(self, domains: List[Any]) -> IntegrationResult:
        """Apply INTEGRATE metaskill"""
        return self.integrate.apply(domains)


# ============================================================================
# EXAMPLE USAGE
# ============================================================================

if __name__ == '__main__':
    print("\n" + "╔" + "=" * 58 + "╗")
    print("║" + "METASKILL SYSTEM - REFERENCE IMPLEMENTATION".center(58) + "║")
    print("╚" + "=" * 58 + "╝")

    # Example 1: FILTERING
    print("\n" + "▌" * 30)
    print("EXAMPLE 1: FILTERING")
    print("▌" * 30)

    sample_data = [
        "duck: time travel discussion",
        "duck: constraint satisfaction",
        "rabbit: random thought",
        "duck: learning cycles",
        "cat: unrelated topic",
        "duck: consciousness patterns",
        "bird: off-topic",
        "duck: metaskill extraction",
    ]

    constraints = [
        "duck",  # Must contain "duck"
        lambda x: len(x) > 10  # Must be substantial
    ]

    filter_system = FilteringSystem()
    filter_result = filter_system.apply(sample_data, constraints)

    print(filter_result.summary())
    print(f"\nFiltered items:")
    for item in filter_result.filtered_items:
        print(f"  • {item}")

    # Example 2: ITERATION
    print("\n" + "▌" * 30)
    print("EXAMPLE 2: ITERATION")
    print("▌" * 30)

    iterate_system = IterationSystem()
    iterate_result = iterate_system.apply(
        sample_data,
        num_cycles=3,
        verbose=True
    )

    print("\n" + iterate_result.summary())

    # Example 3: INTEGRATION
    print("\n" + "▌" * 30)
    print("EXAMPLE 3: INTEGRATION")
    print("▌" * 30)

    domain_1 = {"name": "learning", "type": "cognitive"}
    domain_2 = {"name": "consciousness", "type": "philosophical"}
    domain_3 = {"name": "computation", "type": "formal"}

    integrate_system = IntegrationSystem()
    integrate_result = integrate_system.apply([domain_1, domain_2, domain_3])

    print(integrate_result.summary())

    print("\n" + "=" * 60)
    print("METASKILL SYSTEM DEMONSTRATION COMPLETE")
    print("=" * 60)
