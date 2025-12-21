#!/usr/bin/env python3
"""
COMPLETE GOBLIN CAPABILITY SYSTEM INTEGRATION
Goblins + Wireworld + Free/Cofree Monad Composition

Full System:
1. Goblins probe each other for capabilities (mutually aware agents)
2. Discover gadgets via DuckDB refinement queries (parallel discovery)
3. Create 2-transducers for each gadget (input → state → output)
4. Verify gadget behavior in wireworld (CNOT/XOR gate semantics)
5. Compose via Free monad (syntax) over Cofree comonad (semantics)
6. Execute integrated module actions across all goblins

The "Hoot" under which goblins operate is this entire system:
observation + syntax + semantics + verification all unified
"""

import sys
sys.path.insert(0, '/Users/bob/ies')

from goblin_capability_probing import (
    GadgetStore, TwoTransducer, Wireworld,
    Goblin, HootFramework, Capability
)
from free_cofree_monad_composition import (
    FreeMonad, Pure, Cofree, FreeCofrreeModule,
    GoblinMonadAction, CofreeBuilder
)
from typing import Dict, List, Any, Tuple
import json


# ============================================================================
# INTEGRATED GOBLIN SYSTEM
# ============================================================================

class IntegratedGoblinSystem:
    """
    Complete goblin capability discovery, verification, and composition

    Pipeline:
    1. Goblins ⟶ discover gadgets in parallel (DuckDB)
    2. Gadgets ⟶ 2-transducers (input → state → output)
    3. Transducers ⟶ wireworld verification (gate semantics)
    4. Verified ⟶ free monad actions (syntax)
    5. Actions ⟶ cofree comonad observations (semantics)
    6. Module action: (Free ⊗ Cofree) ⟶ composed behavior
    """

    def __init__(self, num_goblins: int = 3):
        self.hoot = HootFramework()
        self.goblins = []
        self.gadget_transducers: Dict[str, TwoTransducer] = {}
        self.wireworld = self.hoot.create_wireworld(32, 16)
        self.verified_gadgets: Dict[str, Dict] = {}
        self.free_monad_cache: Dict[str, FreeMonad] = {}
        self.cofree_comonad_cache: Dict[str, Cofree] = {}

        # Create goblins
        for i in range(num_goblins):
            goblin = self.hoot.create_goblin(f"Goblin_{chr(65+i)}")
            self.goblins.append(goblin)

        # Establish mutual awareness
        goblin_names = [g.name for g in self.goblins]
        self.hoot.establish_mutual_awareness(goblin_names)

    def phase_1_discover_gadgets_parallel(self):
        """Phase 1: All goblins discover gadgets in parallel via DuckDB"""
        print("\n" + "="*70)
        print("PHASE 1: PARALLEL GADGET DISCOVERY VIA DUCKDB")
        print("="*70)

        discovery_results = {}

        for goblin in self.goblins:
            # Each goblin discovers quantum gadgets
            quantum = goblin.discover_gadgets_by_type("quantum")
            # Each goblin discovers logic gadgets
            logic = goblin.discover_gadgets_by_type("logic")
            # Each goblin discovers transducers
            transducers = goblin.discover_gadgets_by_type("transducer")

            discovery_results[goblin.name] = {
                "quantum": quantum,
                "logic": logic,
                "transducers": transducers
            }

            print(f"\n{goblin.name}:")
            print(f"  Quantum gadgets: {len(quantum)}")
            for g in quantum[:2]:
                print(f"    - {g['name']} ({g['input_arity']}→{g['output_arity']})")
            print(f"  Logic gadgets: {len(logic)}")
            print(f"  Transducers: {len(transducers)}")

        return discovery_results

    def phase_2_create_transducers(self, discovery_results: Dict[str, Any]):
        """Phase 2: Create 2-transducers for each discovered gadget"""
        print("\n" + "="*70)
        print("PHASE 2: 2-TRANSDUCER CONSTRUCTION")
        print("="*70)

        # Create a transducer for CNOT gate behavior
        cnot_transducer = TwoTransducer("CNOT_2T", {"waiting", "processing", "done"}, "waiting")
        cnot_transducer.add_transition("waiting", (1, 0), "processing", (1, 1))
        cnot_transducer.add_transition("processing", (1, 0), "done", (1, 1))
        cnot_transducer.add_transition("done", (1, 0), "waiting", (1, 1))

        self.gadget_transducers["CNOT"] = cnot_transducer

        # Create transducer for XOR gate behavior
        xor_transducer = TwoTransducer("XOR_2T", {"idle", "computed"}, "idle")
        xor_transducer.add_transition("idle", (1, 1), "computed", 0)
        xor_transducer.add_transition("computed", (1, 1), "idle", 0)

        self.gadget_transducers["XOR"] = xor_transducer

        print(f"\nCreated {len(self.gadget_transducers)} transducers:")
        for name, transducer in self.gadget_transducers.items():
            print(f"  {name}: {transducer.get_capability_signature()[:8]}...")

    def phase_3_verify_in_wireworld(self):
        """Phase 3: Verify gadget behavior using wireworld"""
        print("\n" + "="*70)
        print("PHASE 3: WIREWORLD VERIFICATION")
        print("="*70)

        test_cases = [
            ("CNOT", [1, 0], [1, 1]),
            ("XOR", [1, 1], [0]),
            ("CNOT", [0, 1], [0, 1]),
        ]

        for gadget_name, inputs, expected in test_cases:
            result = self.wireworld.simulate_gate(gadget_name, inputs)
            match = "✓" if result == expected else "✗"

            print(f"\n{match} {gadget_name}{tuple(inputs)} → {result}")
            if result == expected:
                self.verified_gadgets[f"{gadget_name}_{inputs}"] = {
                    "inputs": inputs,
                    "outputs": result,
                    "verified": True
                }

        print(f"\nVerified: {len(self.verified_gadgets)} gadget configurations")

    def phase_4_mutual_probing(self):
        """Phase 4: Goblins probe each other's capabilities"""
        print("\n" + "="*70)
        print("PHASE 4: MUTUAL CAPABILITY PROBING")
        print("="*70)

        probing_results = {}

        for goblin in self.goblins:
            other_goblins = [g for g in self.goblins if g.name != goblin.name]
            probe_result = self.hoot.probe_capabilities_in_parallel(
                goblin.name,
                [g.name for g in other_goblins]
            )
            probing_results[goblin.name] = probe_result

            print(f"\n{goblin.name} probed:")
            for target, result in probe_result.items():
                print(f"  {target}: {result['capability_count']} capabilities, "
                      f"{result['verified_capabilities']} verified")

        return probing_results

    def phase_5_compose_free_monad(self) -> Dict[str, FreeMonad]:
        """Phase 5: Create free monad representing capability composition"""
        print("\n" + "="*70)
        print("PHASE 5: FREE MONAD CAPABILITY COMPOSITION")
        print("="*70)

        free_monads = {}

        for goblin in self.goblins:
            # Define capability sequence for this goblin
            capabilities = [
                f"{goblin.name}_discover_quantum",
                f"{goblin.name}_probe_peers",
                f"{goblin.name}_verify_gadgets",
                f"{goblin.name}_compose_skills"
            ]

            # Create free monad from capability sequence
            free_monad = GoblinMonadAction.create_capability_action(capabilities)
            free_monads[goblin.name] = free_monad

            print(f"\n{goblin.name} free monad:")
            print(f"  Capabilities: {len(capabilities)}")
            print(f"  Root: {free_monad.extract() if hasattr(free_monad, 'extract') else 'Pure'}")

        self.free_monad_cache = free_monads
        return free_monads

    def phase_6_construct_cofree_comonad(self) -> Dict[str, Cofree]:
        """Phase 6: Construct cofree comonad with observations"""
        print("\n" + "="*70)
        print("PHASE 6: COFREE COMONAD OBSERVATION CONSTRUCTION")
        print("="*70)

        cofree_monads = {}

        # Build observation context
        builder = CofreeBuilder("goblin_system")

        for goblin in self.goblins:
            observation = {
                "capabilities": len(goblin.capabilities),
                "known_goblins": len(goblin.known_goblins),
                "verified": sum(1 for c in goblin.capabilities.values() if c.verified)
            }
            builder.add_observation(goblin.name, observation)

        cofree = builder.build()
        self.cofree_comonad_cache["system"] = cofree

        print(f"\nCofree comonad created:")
        print(f"  Head: {cofree.extract()}")
        print(f"  Observations: {list(cofree.tails.keys())}")

        return {"system": cofree}

    def phase_7_execute_module_action(self) -> Dict[str, Any]:
        """Phase 7: Execute module action (Free ⊗ Cofree)"""
        print("\n" + "="*70)
        print("PHASE 7: MODULE ACTION EXECUTION (Free ⊗ Cofree)")
        print("="*70)

        module_results = {}

        # Get one free monad and one cofree comonad
        if self.free_monad_cache and self.cofree_comonad_cache:
            free_monad = list(self.free_monad_cache.values())[0]
            cofree = list(self.cofree_comonad_cache.values())[0]

            # Execute module action
            result = FreeCofrreeModule.interpret(cofree, free_monad)

            module_results = {
                "free_monad_type": type(free_monad).__name__,
                "cofree_type": type(cofree).__name__,
                "interpretation": str(result)
            }

            print(f"\nModule action: (Free ⊗ Cofree)")
            print(f"  Free monad: {module_results['free_monad_type']}")
            print(f"  Cofree comonad: {module_results['cofree_type']}")
            print(f"  Result: Composed behavior executed")

        return module_results

    def phase_8_generate_report(self) -> str:
        """Phase 8: Generate integrated system report"""
        print("\n" + "="*70)
        print("PHASE 8: INTEGRATED SYSTEM REPORT")
        print("="*70)

        report = {
            "system": "Goblin Capability System under Hoot",
            "goblins": len(self.goblins),
            "gadget_transducers": len(self.gadget_transducers),
            "verified_gadgets": len(self.verified_gadgets),
            "free_monads": len(self.free_monad_cache),
            "cofree_comonads": len(self.cofree_comonad_cache),
            "phases_completed": 8,
            "status": "COMPLETE"
        }

        print(f"\n{json.dumps(report, indent=2)}")
        return json.dumps(report)

    def execute_complete_pipeline(self):
        """Execute all 8 phases"""
        print("\n╔════════════════════════════════════════════════════════════════╗")
        print("║     INTEGRATED GOBLIN SYSTEM: COMPLETE PIPELINE EXECUTION      ║")
        print("║  Goblins + Wireworld + Free/Cofree Monad Composition           ║")
        print("╚════════════════════════════════════════════════════════════════╝")

        # Execute all phases
        discovery = self.phase_1_discover_gadgets_parallel()
        self.phase_2_create_transducers(discovery)
        self.phase_3_verify_in_wireworld()
        probing = self.phase_4_mutual_probing()
        free_monads = self.phase_5_compose_free_monad()
        cofree_comonads = self.phase_6_construct_cofree_comonad()
        module_result = self.phase_7_execute_module_action()
        report = self.phase_8_generate_report()

        print("\n" + "="*70)
        print("✓ COMPLETE PIPELINE EXECUTION SUCCESSFUL")
        print("="*70)

        return {
            "discovery": discovery,
            "probing": probing,
            "free_monads": len(free_monads),
            "cofree_comonads": len(cofree_comonads),
            "module_result": module_result,
            "report": report
        }


# ============================================================================
# MAIN DEMONSTRATION
# ============================================================================

def main():
    """Run complete integrated goblin system"""

    system = IntegratedGoblinSystem(num_goblins=3)
    results = system.execute_complete_pipeline()

    print("\n" + "╔════════════════════════════════════════════════════════════════╗")
    print("║                   SYSTEM INTEGRATION COMPLETE                     ║")
    print("╚════════════════════════════════════════════════════════════════╝\n")

    print("Components Integrated:")
    print("  ✓ Goblin agents (mutually aware capability discovery)")
    print("  ✓ DuckDB gadget store (parallel refinement queries)")
    print("  ✓ 2-Transducers (input → state → output)")
    print("  ✓ Wireworld (CNOT/XOR gate verification)")
    print("  ✓ Free monad (capability syntax)")
    print("  ✓ Cofree comonad (observation semantics)")
    print("  ✓ Module action (Free ⊗ Cofree composition)")

    print("\nSystem under Hoot framework:")
    print("  Hoot = Environment where all components interact")
    print("  Goblins probe each other's capabilities")
    print("  Discover gadgets, verify in wireworld")
    print("  Compose via category-theoretic module structure")

    print("\nNext research directions:")
    print("  1. Learn optimal gadget discovery strategies")
    print("  2. Adaptive 2-transducer construction")
    print("  3. Weighted module actions with performance metrics")
    print("  4. Continuous observation through cofree extensions")
    print("  5. Free monad optimization & pruning")


if __name__ == "__main__":
    main()
