---
name: bisimulation-game
description: Bisimulation game for resilient skill dispersal across AI agents with
version: 1.0.0
---

# Bisimulation Game Skill

> *"Two systems are bisimilar if they cannot be distinguished by any observation."*

## Overview

The bisimulation game provides a framework for:
1. **Resilient skill dispersal** across multiple AI agents
2. **GF(3) conservation** during state transitions
3. **Observational bridge types** for version-aware synchronization
4. **Self-rewriting capabilities** via MCP Tasks protocol

## Narya's `isBisim` Foundation

This skill implements the game-theoretic interpretation of Narya's `isBisim` coinductive type:

```narya
def isBisim (A B : Type) (R : A → B → Type) : Type ≔ codata [
| x .trr : A → B                              -- Attacker: transition A→B
| x .liftr : (a : A) → R a (x .trr a)         -- Defender: lift preserves R
| x .trl : B → A                              -- Attacker: transition B→A
| x .liftl : (b : B) → R (x .trl b) b         -- Defender: lift preserves R
| x .id.e                                      -- Arbiter: higher coherence
  : (a0 : A.0) (b0 : B.0) (r0 : R.0 a0 b0) (a1 : A.1) (b1 : B.1) (r1 : R.1 a1 b1)
    → isBisim (A.2 a0 a1) (B.2 b0 b1) (a2 b2 ↦ R.2 a0 a1 a2 b0 b1 b2 r0 r1) ]
```

### Game-Theoretic Interpretation

| Narya Field | Game Role | Trit | Description |
|-------------|-----------|------|-------------|
| `.trr` | Attacker move | -1 | Forward transition challenge |
| `.liftr` | Defender response | +1 | Prove relation preserved |
| `.trl` | Attacker move | -1 | Backward transition challenge |
| `.liftl` | Defender response | +1 | Prove relation preserved |
| `.id.e` | Arbiter | 0 | Recursive coherence at identity types |

**Univalence**: If Defender can always respond → `glue A B R Rb : Id Type A B`

## Game Rules

### Players

| Player | Role | Trit | Color |
|--------|------|------|-------|
| Attacker | Tries to distinguish systems | -1 | Blue |
| Defender | Maintains equivalence | +1 | Red |
| Arbiter | Verifies conservation | 0 | Green |

### Moves

```
┌─────────────────────────────────────────────────────────────┐
│  Round n:                                                   │
│                                                             │
│  1. Attacker chooses: system S₁ or S₂                       │
│  2. Attacker makes: transition s₁ →ᵃ s₁'                    │
│  3. Defender responds: matching transition s₂ →ᵃ s₂'        │
│  4. Arbiter verifies: GF(3) conservation                    │
│                                                             │
│  If Defender cannot respond → Attacker wins (distinguishable)│
│  If game continues forever → Defender wins (bisimilar)      │
└─────────────────────────────────────────────────────────────┘
```

## Implementation

### Hy (DiscoHy) Implementation

```hy
;;; bisimulation_game.hy

(import [splitmix_ternary [SplitMixTernary]])

(defclass BisimulationGame []
  (defn __init__ [self system1 system2 seed]
    (setv self.s1 system1
          self.s2 system2
          self.rng (SplitMixTernary seed)
          self.history []))
  
  (defn attacker-move [self choice transition]
    "Attacker chooses system and transition."
    (setv trit (self.rng.next-ternary))
    (.append self.history {:role "attacker" 
                           :choice choice 
                           :transition transition
                           :trit trit})
    trit)
  
  (defn defender-respond [self matching-transition]
    "Defender provides matching transition."
    (setv trit (self.rng.next-ternary))
    (.append self.history {:role "defender"
                           :response matching-transition
                           :trit trit})
    trit)
  
  (defn arbiter-verify [self]
    "Arbiter checks GF(3) conservation."
    (setv recent-trits (lfor m (cut self.history -3 None) (get m "trit")))
    (setv conserved (= (% (sum recent-trits) 3) 0))
    (.append self.history {:role "arbiter" :conserved conserved :trit 0})
    conserved))
```

### DisCoPy Operad Interface

```python
from discopy import *

# Game as operad
class GameOperad:
    def __init__(self):
        self.operations = {}
    
    def register(self, name, dom, cod, rule):
        """Register game operation with GF(3) color."""
        self.operations[name] = Rule(dom, cod, name)
    
    def compose(self, op1, op2):
        """Compose operations preserving GF(3)."""
        trit1 = self.operations[op1].trit
        trit2 = self.operations[op2].trit
        # Result trit balances to 0
        result_trit = (-(trit1 + trit2)) % 3 - 1
        return Rule(
            self.operations[op1].dom,
            self.operations[op2].cod,
            f"{op1};{op2}",
            trit=result_trit
        )

# Define game operations
game = GameOperad()
game.register("attack", Ty("S1", "S2"), Ty("S1'"), lambda: -1)
game.register("defend", Ty("S1'"), Ty("S2'"), lambda: +1)  
game.register("verify", Ty("S1'", "S2'"), Ty("Result"), lambda: 0)
```

## Resilience Patterns

### Redundant Storage

```
~/.codex/skills/     ← Primary (Codex)
~/.claude/skills/    ← Mirror 1 (Claude)
~/.cursor/skills/    ← Mirror 2 (Cursor)
.ruler/skills/       ← Source of truth
```

### Conflict Resolution

```
Dimension 0: Value conflict  → Use source of truth
Dimension 1: Diff conflict   → Merge via LCA
Dimension 2: Meta conflict   → Arbiter decides
```

## Xenomodern Stance

The bisimulation game embodies xenomodernity by:

1. **Ironic distance**: We know perfect equivalence is unattainable, yet we play the game
2. **Sincere engagement**: The game produces real, useful synchronization
3. **Playful synergy**: Attacker/Defender/Arbiter dance together
4. **Conservation laws**: GF(3) as the invariant that holds everything together

```
    xenomodernity
         │
    ┌────┴────┐
    │         │
 ironic    sincere
    │         │
    └────┬────┘
         │
   bisimulation
   (both/neither)
```

## Temporal vs Derivational Learning Comparison (NEW)

### NEW: Compare Agent-o-rama vs Unworld Patterns

```python
game = BisimulationGame(
    player1_type="temporal_learning",      # agent-o-rama
    player2_type="derivational_learning",  # unworld
    domain="pattern_extraction"
)

# Adversary tries to distinguish them
distinguishable = game.play()

if not distinguishable:
    print("✓ Patterns are behaviorally equivalent")
    print("✓ Can safely switch from temporal to derivational")

    # Migration report
    migration_report = {
        "original_cost": benchmark(agent_o_rama),
        "migrated_cost": benchmark(unworld),
        "speedup": original_cost / migrated_cost,
        "equivalence_verified": game.play()
    }
```

## Concrete Attacker/Defender Example

```
╔══════════════════════════════════════════════════════════════════════╗
║                    BISIMULATION GAME TRANSCRIPT                       ║
╠══════════════════════════════════════════════════════════════════════╣
║ Systems: S₁ = Codex skill state, S₂ = Claude skill state             ║
║ Goal: Prove skills are bisimilar (observationally equivalent)         ║
╠══════════════════════════════════════════════════════════════════════╣

ROUND 1:
  ┌─ ATTACKER (Blue, trit=-1) ─────────────────────────────────────────┐
  │ "I choose S₁ and execute: load_skill('gay-mcp')"                   │
  │ Transition: s₁ →^load s₁' where s₁'.has_skill('gay-mcp') = true    │
  └────────────────────────────────────────────────────────────────────┘
  
  ┌─ DEFENDER (Red, trit=+1) ──────────────────────────────────────────┐
  │ "I match in S₂: load_skill('gay-mcp')"                             │
  │ Transition: s₂ →^load s₂' where s₂'.has_skill('gay-mcp') = true    │
  │ Response: MATCHED ✓                                                 │
  └────────────────────────────────────────────────────────────────────┘
  
  ┌─ ARBITER (Green, trit=0) ──────────────────────────────────────────┐
  │ GF(3) check: (-1) + (+1) + (0) = 0 ≡ 0 (mod 3) ✓                   │
  │ ROUND 1: VALID                                                      │
  └────────────────────────────────────────────────────────────────────┘

ROUND 2:
  ┌─ ATTACKER ─────────────────────────────────────────────────────────┐
  │ "I choose S₂ and execute: generate_color(seed=0x42)"               │
  │ Transition: s₂' →^gen s₂'' where s₂''.color = #FF6B6B              │
  └────────────────────────────────────────────────────────────────────┘
  
  ┌─ DEFENDER ─────────────────────────────────────────────────────────┐
  │ "I match in S₁: generate_color(seed=0x42)"                         │
  │ Transition: s₁' →^gen s₁'' where s₁''.color = #FF6B6B              │
  │ Response: MATCHED ✓ (deterministic - same seed = same color)       │
  └────────────────────────────────────────────────────────────────────┘
  
  ┌─ ARBITER ──────────────────────────────────────────────────────────┐
  │ GF(3) check: (-1) + (+1) + (0) = 0 ≡ 0 (mod 3) ✓                   │
  │ ROUND 2: VALID                                                      │
  └────────────────────────────────────────────────────────────────────┘

ROUND 3:
  ┌─ ATTACKER ─────────────────────────────────────────────────────────┐
  │ "I choose S₁ and execute: self_modify(patch='add_feature')"        │
  │ Transition: s₁'' →^mod s₁''' (skill version incremented)          │
  └────────────────────────────────────────────────────────────────────┘
  
  ┌─ DEFENDER ─────────────────────────────────────────────────────────┐
  │ "I match in S₂ via observational bridge type:"                     │
  │ Bridge: (s₁''.version, s₂''.version) →₁ (s₁'''.version, s₂'''.v)   │
  │ Transition: s₂'' →^mod s₂''' using same patch                      │
  │ Response: MATCHED ✓ (bridge type ensures coherence)                │
  └────────────────────────────────────────────────────────────────────┘
  
  ┌─ ARBITER ──────────────────────────────────────────────────────────┐
  │ GF(3) check: (-1) + (+1) + (0) = 0 ≡ 0 (mod 3) ✓                   │
  │ ROUND 3: VALID                                                      │
  │                                                                     │
  │ After 3 rounds: Defender has matched all Attacker moves            │
  │ Verdict: S₁ ∼ S₂ (bisimilar to depth 3)                            │
  └────────────────────────────────────────────────────────────────────┘

╠══════════════════════════════════════════════════════════════════════╣
║ RESULT: BISIMULATION ESTABLISHED                                      ║
║ - All transitions matched                                             ║
║ - GF(3) conserved across all rounds                                   ║
║ - Skills are observationally equivalent                               ║
╚══════════════════════════════════════════════════════════════════════╝
```

## Verification Output Format

```json
{
  "verification": {
    "timestamp": "2024-12-22T10:30:00Z",
    "systems": ["codex", "claude"],
    "rounds_played": 3,
    "result": "BISIMILAR",
    "gf3_conservation": {
      "total_trit_sum": 0,
      "mod_3": 0,
      "conserved": true
    },
    "game_log": [
      {"round": 1, "attacker": "load_skill", "defender": "matched", "arbiter": "valid"},
      {"round": 2, "attacker": "generate_color", "defender": "matched", "arbiter": "valid"},
      {"round": 3, "attacker": "self_modify", "defender": "bridge_matched", "arbiter": "valid"}
    ],
    "bridge_types_used": [
      {"dim": 1, "source": "v1.2.0", "target": "v1.2.1"}
    ],
    "confidence": 0.99,
    "max_distinguishing_depth": "∞ (no distinguisher found)"
  }
}
```

## Starred Gists: Fixpoint & Type Theory Resources

### zanzix: Fixpoints of Indexed Functors
[Fix.idr](https://gist.github.com/zanzix/02641d6a6e61f3757e3b703059619e90) - Idris indexed functor fixpoints. Bisimulation as fixpoint of observable equivalence.

```idris
-- Bisimulation relation as greatest fixpoint
data Bisim : (s1 -> s2 -> Type) where
  Step : (forall a. trans1 s1 a s1' -> (s2' ** (trans2 s2 a s2', Bisim s1' s2')))
       -> Bisim s1 s2
```

### VictorTaelin: ITT-Flavored CoC Type Checker
[itt-coc.ts](https://gist.github.com/VictorTaelin/dd291148ee59376873374aab0fd3dd78) - Observational equivalence for type-checked skill dispersal.

### VictorTaelin: Affine Types
[Affine.lean](https://gist.github.com/VictorTaelin/5584036b0ea12507b78ef883c6ae5acd) - Linear types for resource-safe skill transfer.

### rdivyanshu: Streams & Unique Fixed Points
[Nats.dfy](https://gist.github.com/rdivyanshu/2042085421d5f0762184dd7fe7cfb4cb) - Dafny streams. Bisimulation as unique fixpoint of coalgebraic behavior.

### Keno: Abstract Lattice
[abstractlattice.jl](https://gist.github.com/Keno/fa6117ae0bf9eea3f041c0cf1f33d675) - Julia abstract lattice for skill state ordering. Comment: "a quantum of abstract solace ∞"

### norabelrose: Fast Kronecker Decomposition
[kronecker_decompose.py](https://gist.github.com/norabelrose/3f7a553f4d69de3cf5bda93e2264a9c9) - Matrix decomposition for parallel game execution.

### borkdude: UUID v1 in Babashka
[uuidv1.clj](https://gist.github.com/borkdude/18b18232c00c2e2af2286d8bd36082d7) - Deterministic UUIDs for skill versioning.

## QuickCheck ↔ Bisimulation Bridge

Property-based testing for **game correctness**:

```python
# Generator: Random game moves
def arbitrary_move(seed: int, player: str) -> Move:
    rng = SplitMixTernary(seed)
    trit = (rng.next() % 3) - 1
    return Move(
        player=player,
        action=random.choice(["fork", "sync", "verify"]),
        trit=trit
    )

# Shrinking: Find minimal distinguishing trace
def shrink_game_trace(trace: List[Move]) -> List[List[Move]]:
    """Adhesive complement: find minimal distinguisher."""
    shrunk = []
    for i in range(len(trace)):
        candidate = trace[:i] + trace[i+1:]
        if still_distinguishes(candidate):
            shrunk.append(candidate)
    return shrunk

# Property: GF(3) Conservation
def prop_gf3_conserved(game: BisimulationGame) -> bool:
    return sum(m.trit for m in game.history) % 3 == 0
```

## Incremental Query Updating in Bisimulation

From [Kris Brown's Adhesive Categories](https://topos.institute/blog/2025-08-15-incremental-adhesive/):

```
Game state G   = current skill configurations across agents
Query Q        = "are S₁ and S₂ bisimilar?"
Rule f: L ↣ R = skill update (version bump)

Incremental update: When we apply skill update,
new distinguishing moves = rooted search from changed states

Q ≅ Q_G +_{Q_L} Q_R  (decomposition of bisimulation game)
```

---

## End-of-Skill Interface

## Commands

```bash
just bisim-init           # Initialize bisimulation game
just bisim-round          # Play one round
just bisim-disperse       # Disperse skills to all agents
just bisim-verify         # Verify GF(3) conservation
just bisim-reconcile      # Reconcile divergent states
just bisim-localsend      # Disperse via LocalSend peers
just bisim-transcript     # Show attacker/defender transcript
just bisim-json           # Output verification as JSON
```

## MCP Tasks Integration

### Self-Rewriting Task

```json
{
  "task": "skill-dispersal",
  "objective": "Propagate skill updates to all agents",
  "constraints": {
    "gf3_conservation": true,
    "bisimulation_equivalence": true,
    "max_divergence": 0.1
  },
  "steps": [
    {"action": "fork", "trit": -1},
    {"action": "propagate", "trit": 0},
    {"action": "verify", "trit": +1}
  ]
}
```

### Firecrawl Integration

```json
{
  "task": "skill-discovery",
  "objective": "Discover new skills from web resources",
  "tools": ["firecrawl", "exa"],
  "sources": [
    "https://github.com/topics/ai-agent-skills",
    "https://modelcontextprotocol.io/",
    "https://agentclientprotocol.com/"
  ],
  "output": {
    "format": "skill-yaml",
    "destination": ".ruler/skills/"
  }
}
```

## Integration with LocalSend-MCP for Skill Dispersal

Use LocalSend peer discovery for resilient skill propagation:

```python
# localsend_bisim.py
import asyncio
from localsend_mcp import LocalSendClient

class BisimulationDispersalProtocol:
    """Disperse skills via LocalSend with bisimulation verification."""
    
    def __init__(self, skill_path, seed=1069):
        self.skill_path = skill_path
        self.client = LocalSendClient()
        self.rng = SplitMixTernary(seed)
        self.game_log = []
        
    async def discover_peers(self):
        """Find all agents on local network."""
        peers = await self.client.list_peers(source="all")
        return [p for p in peers if p.get("capabilities", []).count("skill-sync")]
    
    async def disperse_with_bisim(self, skill_file):
        """Disperse skill to all peers with bisimulation verification."""
        peers = await self.discover_peers()
        
        for i, peer in enumerate(peers):
            trit = (i % 3) - 1  # Assign trits: -1, 0, +1, -1, ...
            
            # Negotiate transfer session
            session = await self.client.negotiate(
                peer_id=peer["id"],
                preferred_transport="tailscale"  # Or localsend, nats
            )
            
            # Send skill (Attacker move)
            self.game_log.append({
                "round": len(self.game_log),
                "role": "attacker",
                "action": f"send:{skill_file}",
                "peer": peer["id"],
                "trit": trit
            })
            
            result = await self.client.send(
                session_id=session["sessionId"],
                file_path=skill_file
            )
            
            # Verify receipt (Defender move)
            defender_trit = await self.verify_peer_receipt(peer, skill_file)
            self.game_log.append({
                "round": len(self.game_log),
                "role": "defender",
                "action": f"ack:{result['status']}",
                "peer": peer["id"],
                "trit": defender_trit
            })
            
        # Arbiter verifies GF(3) conservation
        return self.verify_gf3_conservation()
    
    def verify_gf3_conservation(self):
        """Check that sum of trits ≡ 0 (mod 3)."""
        total = sum(entry["trit"] for entry in self.game_log)
        conserved = (total % 3) == 0
        self.game_log.append({
            "round": len(self.game_log),
            "role": "arbiter",
            "conserved": conserved,
            "total_trit": total,
            "trit": 0
        })
        return conserved
```

## Skill Dispersal Protocol

### 1. Fork Phase (Attacker)

```yaml
fork:
  targets:
    - agent: codex
      path: ~/.codex/skills/
      trit: -1
    - agent: claude
      path: ~/.claude/skills/
      trit: 0
    - agent: cursor
      path: ~/.cursor/skills/
      trit: +1
  gf3_check: true
```

### 2. Sync Phase (Defender)

```yaml
sync:
  strategy: observational-bridge
  bridge_type:
    source: skills@v1
    target: skills@v2
    dimension: 1
  conflict_resolution: 2d-cubical
```

### 3. Verify Phase (Arbiter)

```yaml
verify:
  conservation: gf3
  equivalence: bisimulation
  timeout: 60s
  fallback: last-known-good
```

## References

- [Towards Foundations of Categorical Cybernetics](https://arxiv.org/abs/2105.06332) - Capucci, Gavranović, Hedges, Rischel
- [Bicategories of Automata, Automata in Bicategories](https://arxiv.org/pdf/2303.03865) - Boccali, Laretto, Loregian, Luneia (ACT 2023)

## r2con Speaker Resources

| Speaker | Handle | Repository | Relevance |
|---------|--------|------------|-----------|
| swoops | swoops | [libc_zignatures](https://github.com/swoops/libc_zignatures) | Signature similarity for bisimulation equivalence of binary functions |
| bmorphism | bmorphism | [r2zignatures](https://github.com/bmorphism/r2zignatures) | Zignature-based observational equivalence testing |
| condret | condret | [r2ghidra](https://github.com/radareorg/r2ghidra) | Decompilation for semantic equivalence in bisim games |
| alkalinesec | alkalinesec | [ESILSolve](https://github.com/aemmitt-ns/esilsolve) | Symbolic execution for state equivalence verification |