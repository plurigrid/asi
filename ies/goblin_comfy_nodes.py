import torch
import sys
import os

# Add the IES directory to python path to import existing modules
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

# Import core Goblin logic (mocked or actual imports)
try:
    from goblin_capability_probing import GoblinProbe, GadgetStore
    from free_cofree_monad_composition import FreeMonad, CofreeComonad
    from goblin_integrated_system import WireworldVerification
except ImportError:
    print("Goblin modules not found. Running in mock mode.")
    class GoblinProbe: 
        def probe(self, query): return {"capability": "mock_cap", "score": 0.9}
    class GadgetStore: pass
    class FreeMonad:
        def bind(self, cap): return f"Bound({cap})"
    class WireworldVerification:
        def verify(self, action): return True

class GoblinSourceNode:
    """
    Queries the DuckDB Gadget Store to initiate a capability search.
    """
    def __init__(self):
        self.store = GadgetStore()

    @classmethod
    def INPUT_TYPES(s):
        return {
            "required": {
                "query": ("STRING", {"multiline": True, "default": "SELECT * FROM gadgets WHERE arity > 0"}),
            }
        }

    RETURN_TYPES = ("CONTEXT",)
    RETURN_NAMES = ("LATENT_CONTEXT",)
    FUNCTION = "search"
    CATEGORY = "Goblin/Core"

    def search(self, query):
        print(f"GoblinSource: Executing {query}")
        # In a real run, this returns the DuckDB cursor/context
        context = {"query": query, "db_state": "ready"}
        return (context,)

class CapabilityProberNode:
    """
    Uses Thompson Sampling or other strategies to probe for the best capability.
    """
    def __init__(self):
        self.prober = GoblinProbe()

    @classmethod
    def INPUT_TYPES(s):
        return {
            "required": {
                "context": ("CONTEXT",),
                "strategy": (["ThompsonSampling", "Random", "Greedy"],),
            }
        }

    RETURN_TYPES = ("CAPABILITY",)
    RETURN_NAMES = ("PROBED_CAPABILITY",)
    FUNCTION = "probe"
    CATEGORY = "Goblin/Core"

    def probe(self, context, strategy):
        print(f"CapabilityProber: Probing with {strategy}")
        result = self.prober.probe(context["query"])
        return (result,)

class MonadBinderNode:
    """
    Composes a capability into a Free Monad action.
    """
    @classmethod
    def INPUT_TYPES(s):
        return {
            "required": {
                "capability": ("CAPABILITY",),
            }
        }

    RETURN_TYPES = ("ACTION",)
    RETURN_NAMES = ("COMPOSED_ACTION",)
    FUNCTION = "bind"
    CATEGORY = "Goblin/Logic"

    def bind(self, capability):
        print(f"MonadBinder: Binding {capability}")
        monad = FreeMonad()
        action = monad.bind(capability)
        return (action,)

class WireworldVerifierNode:
    """
    Verifies the composed action using Wireworld cellular automata.
    """
    def __init__(self):
        self.verifier = WireworldVerification()

    @classmethod
    def INPUT_TYPES(s):
        return {
            "required": {
                "action": ("ACTION",),
                "cycles": ("INT", {"default": 100, "min": 1, "max": 1000}),
            }
        }

    RETURN_TYPES = ("RESULT",)
    RETURN_NAMES = ("VERIFIED_RESULT",)
    FUNCTION = "verify"
    CATEGORY = "Goblin/Verification"

    def verify(self, action, cycles):
        print(f"WireworldVerifier: Simulating {cycles} cycles for {action}")
        is_valid = self.verifier.verify(action)
        return ({"valid": is_valid, "action": action},)

# Node Export
NODE_CLASS_MAPPINGS = {
    "GoblinSource": GoblinSourceNode,
    "CapabilityProber": CapabilityProberNode,
    "MonadBinder": MonadBinderNode,
    "WireworldVerifier": WireworldVerifierNode
}

NODE_DISPLAY_NAME_MAPPINGS = {
    "GoblinSource": "👹 Goblin Source",
    "CapabilityProber": "🔍 Capability Prober",
    "MonadBinder": "🔗 Monad Binder",
    "WireworldVerifier": "⚡ Wireworld Verifier"
}
