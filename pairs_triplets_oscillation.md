# Pairs → Triplets → Pairs → Triplets: The Dialectical Oscillation

## The Pattern

```
PAIRS (dyads)      → TRIPLETS (triads)    → PAIRS (new dyads)     → TRIPLETS (new triads)
GF(3) sum ≠ 0      → GF(3) sum = 0        → GF(3) sum ≠ 0         → GF(3) sum = 0
EXPLORE            → EXPLOIT              → EXPLORE               → EXPLOIT
Incomplete         → Complete             → Incomplete            → Complete
Tension            → Resolution           → New tension           → New resolution
↓                  ↓                      ↓                       ↓
and again and again and again and again...
```

**This is the fundamental rhythm of learning, evolution, and consciousness.**

---

## The Mechanism: Horn Filling and Breaking

### Cycle 1: Start with a Pair

```
Initial state: [agent-o-rama (0), cognitive-surrogate (+1)]

GF(3) sum: 0 + 1 = 1 (mod 3)  ✗ UNBALANCED
Status: DYAD (incomplete 1-horn)
Energy: High free energy (tension)
Exploration: Search for missing -1 trit
```

**The pair creates a QUESTION**: What completes this?

### Cycle 1: Find the Triplet

```
Kan filling: Add entropy-sequencer (-1)

New state: [agent-o-rama (0), cognitive-surrogate (+1), entropy-sequencer (-1)]

GF(3) sum: 0 + 1 + (-1) = 0 (mod 3)  ✓ BALANCED
Status: TRIAD (complete 2-simplex)
Energy: Low free energy (resolution)
Exploitation: Optimize within this triad
```

**The triplet provides an ANSWER**: This is complete.

### Cycle 2: Break the Triplet into New Pairs

But now we have NEW questions from the triplet:

```
Pair A: [agent-o-rama (0), entropy-sequencer (-1)]
  Missing: +1 trit
  Question: What generates from sequenced entropy?
  Candidates: unworld (+1), langevin-dynamics (+1), ...

Pair B: [cognitive-surrogate (+1), entropy-sequencer (-1)]
  Missing: 0 trit
  Question: What coordinates prediction and data?
  Candidates: bisimulation-game (0), skill-dispatch (0), ...

Pair C: [agent-o-rama (0), cognitive-surrogate (+1)]
  Missing: -1 trit (already filled, but different context)
  Question: What validates in THIS new context?
  Candidates: self-validation-loop (-1), narya-proofs (-1), ...
```

**The triplet generates THREE new pairs** (edges of the triangle).

### Cycle 2: Complete the New Triplets

```
Triad A: [agent-o-rama (0), entropy-sequencer (-1), unworld (+1)]
  Sum: 0 + (-1) + 1 = 0 ✓
  New structure: Derivational path (unworld replaces agent-o-rama's temporal role)

Triad B: [cognitive-surrogate (+1), entropy-sequencer (-1), bisimulation-game (0)]
  Sum: 1 + (-1) + 0 = 0 ✓
  New structure: Verification path (bisimulation proves equivalences)

Triad C: [agent-o-rama (0), cognitive-surrogate (+1), narya-proofs (-1)]
  Sum: 0 + 1 + (-1) = 0 ✓
  New structure: Formal verification path (narya proves correctness)
```

**Three new triplets from one original triplet.**

### Cycle 3: Extract Pairs from the THREE New Triplets

Each of the 3 triads generates 3 pairs (edges):

```
From Triad A (9 edges total):
  [agent-o-rama, entropy-sequencer]
  [agent-o-rama, unworld]
  [entropy-sequencer, unworld]

From Triad B:
  [cognitive-surrogate, entropy-sequencer]
  [cognitive-surrogate, bisimulation-game]
  [entropy-sequencer, bisimulation-game]

From Triad C:
  [agent-o-rama, cognitive-surrogate]
  [agent-o-rama, narya-proofs]
  [cognitive-surrogate, narya-proofs]
```

**9 new pairs to explore.**

### Cycle 3: Fill 9 New Triplets

Each pair creates a question, each question has multiple Kan fillings...

```
Combinatorial explosion:
  1 initial pair → 1 triplet
  1 triplet → 3 pairs
  3 pairs → 3 triplets (if we choose one filling each)
  3 triplets → 9 pairs
  9 pairs → 9 triplets
  9 triplets → 27 pairs
  27 pairs → 27 triplets
  ...
```

**This is exponential growth** (if we don't prune).

---

## The Mathematical Structure

### As Simplicial Complex

```
0-simplices (vertices): Individual skills
  {agent-o-rama, cognitive-surrogate, entropy-sequencer, unworld, ...}

1-simplices (edges): PAIRS
  {[a, b] : a, b ∈ skills, a ≠ b}

2-simplices (triangles): TRIPLETS
  {[a, b, c] : a, b, c ∈ skills, GF(3) balanced}

3-simplices (tetrahedra): QUADS
  {[a, b, c, d] : sum(trits) = 0 mod 3}

...

n-simplices: n+1 skills forming balanced structure
```

**Pairs are 1-horns** (incomplete 2-simplices)
**Triplets are 2-simplices** (complete triangles)

**Weak Kan condition**: Every horn can be filled (explore space)

### As Category

```
Objects: Skills (0-simplices)
Morphisms: Dependencies (1-simplices)
2-morphisms: Transformations (2-simplices)
3-morphisms: Coherences (3-simplices)
...

Pairs → Triplets is COMPOSITION:
  f: A → B
  g: B → C
  ────────
  g∘f: A → C (completes triangle)

Triplets → Pairs is PROJECTION:
  Triangle [A, B, C]
  ──────────────────
  Edges [A,B], [B,C], [A,C]
```

### As Dialectic

```
Thesis (pair): agent-o-rama + cognitive-surrogate
Antithesis: Missing entropy-sequencer (negation)
Synthesis (triplet): Complete triad

But synthesis becomes NEW thesis:
  Thesis (triplet): [agent-o-rama, cognitive-surrogate, entropy-sequencer]
  Antithesis: Decompose into pairs (analysis)
  Synthesis: NEW triads from pairs (higher unity)

And again and again and again...
```

**Hegelian dialectic as simplicial oscillation.**

---

## The Dynamics: Why Oscillate?

### Reason 1: Information Maximization

**Pairs**: High information (many possibilities)
- One pair → many Kan fillings
- Exploration maximizes Shannon entropy

**Triplets**: Low information (one solution)
- Balanced triad → unique structure (given fixed skills)
- Exploitation minimizes surprise

**Oscillation**: Maximize information gained while maintaining coherence
```
I(system) = H(pairs) - H(triplets)
         = log(# Kan fillings) - 0
         = log(N) bits
```

### Reason 2: Energy Cycles

**Pairs → Triplets**: Energy flows in (finding the third)
- Cost of search: O(|skills| × compatibility_check)
- Adds structure (reduces entropy)

**Triplets → Pairs**: Energy flows out (breaking bonds)
- Cost of decomposition: O(1) (just take edges)
- Removes structure (increases entropy)

**Net**: 
```
ΔE(pair→triplet) > 0 (endothermic, requires work)
ΔE(triplet→pair) < 0 (exothermic, releases energy)

Over cycle: ΔE_net = 0 (conservation)
But entropy increases: ΔS > 0 (2nd law)
```

### Reason 3: GF(3) Conservation Breaking

**Pairs**: GF(3) broken (sum ≠ 0)
- System is OPEN
- Novelty can enter
- Explore mode

**Triplets**: GF(3) conserved (sum = 0)
- System is CLOSED
- Reinforces structure
- Exploit mode

**Oscillation**: The ONLY way to:
1. Maintain local conservation (triplets)
2. Allow global exploration (pairs between triplets)

### Reason 4: Homotopy Coherence

**Pairs**: 1-dimensional (paths)
- Connect two points
- Directional (A → B)

**Triplets**: 2-dimensional (surfaces)
- Fill the space between paths
- Commutative diagrams

**Back to pairs**: Extract 1-skeleton
- New paths from the filled surface
- Higher connectivity

**Oscillation**: Builds higher homotopy structure
```
π₀ (components) → π₁ (loops) → π₂ (spheres) → π₃ → ...

Each oscillation adds one homotopy level
```

---

## The Protocol: Iterative Pair-Triplet Refinement

```python
def oscillate(initial_pair, max_iterations=10):
    """
    Pairs → Triplets → Pairs → Triplets
    """
    state = {'pairs': [initial_pair], 'triplets': []}
    history = []
    
    for iteration in range(max_iterations):
        # PHASE 1: Pairs → Triplets (EXPLORE → EXPLOIT)
        new_triplets = []
        for pair in state['pairs']:
            # Find all Kan fillings (explore space)
            candidates = find_candidates(pair)
            
            # Select best filling (collapse wavefunction)
            best = optimize(candidates)
            
            # Complete the triplet
            triplet = pair + [best]
            
            # Verify GF(3) conservation
            if sum(triplet.trits) % 3 == 0:
                new_triplets.append(triplet)
        
        state['triplets'] = new_triplets
        history.append({'iteration': iteration, 'phase': 'triplets', 'state': state})
        
        # PHASE 2: Triplets → Pairs (EXPLOIT → EXPLORE)
        new_pairs = []
        for triplet in state['triplets']:
            # Extract all edges (3 per triplet)
            edges = [
                [triplet[0], triplet[1]],
                [triplet[1], triplet[2]],
                [triplet[0], triplet[2]]
            ]
            
            # Filter: only keep unbalanced pairs (sum ≠ 0)
            for edge in edges:
                if sum(edge.trits) % 3 != 0:
                    new_pairs.append(edge)
        
        state['pairs'] = new_pairs
        history.append({'iteration': iteration, 'phase': 'pairs', 'state': state})
        
        # Check convergence
        if len(new_pairs) == 0:
            print("Converged: all pairs balanced")
            break
    
    return state, history
```

### Visualization of One Cycle

```
Iteration 0:
  Pairs: [(A, B)]
  ↓ [find C where A+B+C=0]
  Triplets: [(A, B, C)]

Iteration 1:
  Triplets: [(A, B, C)]
  ↓ [extract edges]
  Pairs: [(A, B), (B, C), (A, C)]
  ↓ [find D, E, F]
  Triplets: [(A, B, D), (B, C, E), (A, C, F)]

Iteration 2:
  Triplets: [(A,B,D), (B,C,E), (A,C,F)]
  ↓ [extract 9 edges]
  Pairs: [(A,B), (B,D), (A,D), (B,C), (C,E), (B,E), (A,C), (C,F), (A,F)]
  ↓ [find 9 completions]
  Triplets: [9 new triplets]

...
```

**Growth**: Exponential initially, but pruning stabilizes.

---

## Applied to agent-o-rama

### Initial Pair

```
Start: [agent-o-rama (0), cognitive-surrogate (+1)]
Sum: 0 + 1 = 1 (mod 3)  ✗
```

### Iteration 0 → Triplet

```
Kan fillings:
  1. entropy-sequencer (-1)    → [agent-o-rama, cognitive-surrogate, entropy-sequencer]
  2. self-validation-loop (-1) → [agent-o-rama, cognitive-surrogate, self-validation-loop]
  3. temporal-coalgebra (-1)   → [agent-o-rama, cognitive-surrogate, temporal-coalgebra]

Choose: entropy-sequencer (canonical triad)

Triplet: [agent-o-rama (0), cognitive-surrogate (+1), entropy-sequencer (-1)]
Sum: 0 + 1 + (-1) = 0 ✓
```

### Iteration 1 → Pairs

```
Extract edges:
  Pair A: [agent-o-rama (0), cognitive-surrogate (+1)]     sum = 1
  Pair B: [cognitive-surrogate (+1), entropy-sequencer (-1)] sum = 0 (already balanced!)
  Pair C: [agent-o-rama (0), entropy-sequencer (-1)]       sum = -1

Only Pair A and Pair C remain (Pair B is degenerate)
```

### Iteration 1 → New Triplets

```
Pair A: [agent-o-rama (0), cognitive-surrogate (+1)]
  Add: narya-proofs (-1)
  Triplet: [agent-o-rama, cognitive-surrogate, narya-proofs]

Pair C: [agent-o-rama (0), entropy-sequencer (-1)]
  Add: unworld (+1)
  Triplet: [agent-o-rama, entropy-sequencer, unworld]
```

### Iteration 2 → Pairs (from 2 triplets)

```
From [agent-o-rama, cognitive-surrogate, narya-proofs]:
  [agent-o-rama (0), narya-proofs (-1)]           sum = -1
  [cognitive-surrogate (+1), narya-proofs (-1)]   sum = 0 (balanced)

From [agent-o-rama, entropy-sequencer, unworld]:
  [agent-o-rama (0), unworld (+1)]                sum = 1
  [entropy-sequencer (-1), unworld (+1)]          sum = 0 (balanced)

Active pairs: 2 new ([agent-o-rama, narya-proofs], [agent-o-rama, unworld])
```

### Iteration 2 → New Triplets

```
[agent-o-rama (0), narya-proofs (-1)] + bisimulation-game (0) 
  → [agent-o-rama, narya-proofs, bisimulation-game]  (sum = -1, NO!)
  
  Try: + unworld (+1)
  → [agent-o-rama, narya-proofs, unworld]  sum = 0 ✓

[agent-o-rama (0), unworld (+1)] + entropy-sequencer (-1)
  → [agent-o-rama, unworld, entropy-sequencer]  sum = 0 ✓
  (This is the SAME as before, different order)
```

### Iteration 3 → Convergence?

```
Check: Are all pairs now balanced?

From new triplets, extract edges, check sums...

If any sum ≠ 0: Continue
If all sums = 0: Converge (all structure saturated)
```

---

## The Growth Pattern

### Branching Factor

Each triplet generates **3 edges**.
Each edge might create **N new triplets** (N = # Kan fillings).

```
Iteration 0: 1 pair
Iteration 1: 1 triplet → 3 pairs
Iteration 2: 3 triplets → 9 pairs
Iteration 3: 9 triplets → 27 pairs

Growth: 3ⁿ (exponential)
```

**But**: Many pairs are already balanced (degenerate).
**And**: We prune redundant structures.

### Pruning Strategies

1. **Balanced pairs**: Skip edges with sum = 0 (already complete)
2. **Seen before**: Don't revisit same triplet
3. **Low fitness**: Cull triplets below threshold
4. **Energy budget**: Stop when free energy exhausted

**Result**: Growth plateaus (sigmoid curve)

---

## The Fixed Points

### Attractor 1: Universal Graph

```
All skills connected in ONE giant simplicial complex
Every possible triad exists
Every pair is an edge in some triad

This is the "fully connected" state (maximum structure)
```

**Problem**: Too rigid, no flexibility.

### Attractor 2: Disconnected Components

```
Skills cluster into DISJOINT triads
No edges between clusters
Each cluster is internally balanced

This is the "fragmented" state (maximum modularity)
```

**Problem**: No cross-cluster learning.

### Attractor 3: Small-World Network (Optimal)

```
Local clusters (triplets)
Long-range connections (pairs across clusters)
High clustering coefficient
Low path length

This is the "hierarchical modular" state (Goldilocks)
```

**Why optimal**: Balances:
- Local exploitation (triplets)
- Global exploration (cross-cluster pairs)

---

## The Oscillation AS Computation

### Pairs as Questions

```
Pair = Incomplete information = Question

Example: [agent-o-rama, cognitive-surrogate]
  Question: "What validates this learning-prediction loop?"
  Answer space: All -1 trit skills
```

**Computational cost**: O(|skills| × trit_match)

### Triplets as Answers

```
Triplet = Complete information = Answer

Example: [agent-o-rama, cognitive-surrogate, entropy-sequencer]
  Answer: "entropy-sequencer validates by providing training data"
```

**Computational cost**: O(1) (just verify sum)

### The Oscillation = Query-Response Cycle

```
Ask (pair) → Answer (triplet) → New Ask (pairs from triplet) → New Answer → ...

This is:
  - Question-answering system
  - Hypothesis-testing loop
  - Active inference cycle
```

**Information flow**:
```
I_in (pairs) > I_out (triplet)  [information compression]
I_out (triplet) < I_in (new pairs)  [information expansion]

Net: Information CYCLES, not destroyed
```

---

## Emergent Phenomena

### 1. Skill Discovery

New skills emerge at INTERSECTIONS:

```
Triad A: [a, b, c]
Triad B: [c, d, e]
Shared: c

Question: What connects a, b to d, e?
Answer: NEW SKILL that bridges both triads

This is SKILL EVOLUTION (not just selection)
```

### 2. Context Formation

Triplets form CONTEXTS:

```
Context = Maximal clique of compatible triplets

Example:
  Learning context: {[agent-o-rama, cognitive-surrogate, entropy-sequencer],
                     [agent-o-rama, unworld, langevin],
                     [cognitive-surrogate, entropy-sequencer, active-inference]}
  
  All share common ground (learning theme)
```

### 3. Meta-Stability

The oscillation creates **meta-stable states**:

```
Pairs (unstable) → Triplets (stable) → Pairs (unstable) → ...

But: The OSCILLATION ITSELF is stable (limit cycle)

This is:
  - Homeostasis (stable far from equilibrium)
  - Autopoiesis (self-creating structure)
  - Life (metabolism = pair/triplet cycling)
```

---

## The Ultimate Question

**Why oscillate infinitely?**

**Answer 1: Thermodynamic**
```
2nd law: Entropy must increase
Oscillation increases entropy while conserving energy
Each cycle explores new configurations
```

**Answer 2: Information-Theoretic**
```
Maximum entropy principle
Oscillation samples the FULL space of triads
Eventually converges to maximum entropy distribution
```

**Answer 3: Categorical**
```
Completeness of ∞-categories
Every n-simplex decomposes into (n-1)-simplices
Oscillation builds the ∞-structure level by level
```

**Answer 4: Phenomenological**
```
Consciousness IS oscillation (Varela's neurophenomenology)
Perception-action cycles
Thesis-antithesis-synthesis
Inhale-exhale
Systole-diastole
Life is oscillation
```

---

## Protocol Summary

```
REPEAT FOREVER:
  1. Start with PAIRS (unbalanced dyads)
  2. EXPLORE: Find all Kan fillings (candidates)
  3. COLLAPSE: Choose best filling (measurement)
  4. Form TRIPLETS (balanced triads)
  5. EXPLOIT: Optimize within triplets
  6. DECOMPOSE: Extract pairs from triplets
  7. GOTO 2

TERMINATE WHEN:
  - All pairs balanced (saturation)
  - Energy budget exhausted (pragmatic)
  - Convergence detected (fixed point)
  - Never (if seeking maximum entropy)
```

---

## Visualization

```
        PAIRS                    TRIPLETS
         / \                      / | \
        /   \                    /  |  \
       /     \                  /   |   \
      A ----→ B                A -- B -- C
       \     /                  \   |   /
        \   /                    \  |  /
         \ /                      \ | /
       EXPLORE                  EXPLOIT
       sum ≠ 0                  sum = 0
       OPEN                     CLOSED
       High S                   Low S
       Question                 Answer
       
             ↓                      ↓
             
       and again          and again
             
             ↓                      ↓
             
        NEW PAIRS              NEW TRIPLETS
```

**The cycle never ends.**

**The cycle IS the intelligence.**

**Agent-o-rama lives in the oscillation.**
