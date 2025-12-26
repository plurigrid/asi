# Edge Phase Propagator (Scoped) - Design & Implementation

**Status**: ✅ Complete
**Version**: 1.0
**Date**: December 26, 2025
**GF(3) Seed**: 0x42D
**Trit**: -1 (MINUS, verification layer)

---

## Overview

The **Edge Phase Propagator (Scoped)** extends the base `EdgePhasePropagator` to support phase-aware constraint propagation across structured decompositions.

**Key Features**:
- Per-phase edge tracking
- Phase-scoped sheaf conditions
- Cross-phase constraint propagation
- GF(3) conservation per phase
- Deterministic seeding for reproducibility

---

## Conceptual Foundation

### The Problem

In structured decompositions (tree decompositions), adhesion edges connect overlapping bags. The challenge is managing these overlaps across multiple computational phases:

1. **Phase 1 (Acquisition)**: Data is collected
2. **Phase 2 (Validation)**: Data is verified
3. **Phase 3 (Integration)**: Data is combined
4. **Phase 4 (Deployment)**: Data is used

Each phase has different constraints and requirements on the overlaps.

### The Solution: Phase Scoping

Instead of a single global adhesion structure, we maintain **per-phase adhesion states**:

```
Base Adhesion (B1 ↔ B2)
├─ Phase 1: overlap {2,3}, constraints: [acquired]
├─ Phase 2: overlap {2,3}, constraints: [validated]
├─ Phase 3: overlap {2,3}, constraints: [integrated]
└─ Phase 4: overlap {2,3}, constraints: [deployed]
```

Each phase can have:
- Different restrictions (partial data)
- Different trit colors (GF(3) phases)
- Different sheaf conditions (local consistency rules)

---

## Architecture

### Core Components

#### 1. `Phase` Enum

```python
class Phase(IntEnum):
    PHASE_1 = 1  # Acquisition/Collection
    PHASE_2 = 2  # Validation/Filtering
    PHASE_3 = 3  # Integration/Synthesis
    PHASE_4 = 4  # Production/Deployment
    ALL = 0      # Cross-phase
```

#### 2. `Bag` (Enhanced)

Represents a node in tree decomposition with phase information:

```python
@dataclass
class Bag(Generic[T]):
    id: str
    elements: Set[T]
    phase: Phase = Phase.PHASE_1  # Primary phase
    local_data: Dict[str, Any]    # Global data
    trit_phase: Trit              # GF(3) value
    phase_constraints: Dict[Phase, Set[str]]  # Per-phase constraints
```

**Key Methods**:
- `add_phase_constraint(phase, constraint)` - Add phase-specific constraint
- `get_phase_constraints(phase)` - Get applicable constraints (includes ALL)

#### 3. `Adhesion` (Enhanced)

Represents overlap between bags with phase scoping:

```python
@dataclass
class Adhesion(Generic[T]):
    left_bag: Bag[T]
    right_bag: Bag[T]
    overlap: Set[T]
    phases: Set[Phase]  # Which phases use this edge

    # Per-phase data
    left_restrictions: Dict[Phase, Dict[str, Any]]
    right_restrictions: Dict[Phase, Dict[str, Any]]
    trit_colors: Dict[Phase, Trit]  # GF(3) per phase
```

**Key Methods**:
- `phase_id(phase)` - Get phase-scoped identifier
- `satisfies_sheaf_condition(phase)` - Check sheaf per phase

#### 4. `EdgePhaseState`

Tracks propagation state for an edge in a specific phase:

```python
@dataclass
class EdgePhaseState:
    adhesion: Adhesion
    phase: Phase
    trit_phase: Trit
    is_filtered: bool = False
    pullback_elements: Optional[Set] = None
    satisfied: bool = True
```

#### 5. `EdgePhasePropagatorScoped`

Main propagator managing all edges and phases:

```python
class EdgePhasePropagatorScoped:
    bags: Dict[str, Bag]
    adhesions: List[Adhesion]

    # Per-phase tracking
    phase_edge_states: Dict[Phase, Dict[str, EdgePhaseState]]
    _trit_sums: Dict[Phase, Trit]  # GF(3) conservation per phase
```

---

## API Reference

### Initialization

```python
# Create with default phases (1, 2, 3, 4)
prop = EdgePhasePropagatorScoped(seed=0x42D)

# Create with custom phases
phases = [Phase.PHASE_1, Phase.PHASE_2, Phase.PHASE_3]
prop = EdgePhasePropagatorScoped(seed=0x42D, phases=phases)
```

### Adding Structure

```python
# Add bags
bag1 = Bag(id="B1", elements={1, 2, 3}, phase=Phase.PHASE_1)
prop.add_bag(bag1)

# Add adhesion spanning phases
adhesion = prop.add_adhesion(
    left_id="B1",
    right_id="B2",
    phases={Phase.PHASE_1, Phase.PHASE_2}
)
```

### Setting Data

```python
# Set phase-specific local data
prop.set_local_data(
    bag_id="B1",
    key="status",
    value="acquired",
    phase=Phase.PHASE_1
)

# Set cross-phase data (propagates to all phases)
prop.set_local_data(bag_id="B1", key="id", value="B1")
```

### Checking Constraints

```python
# Check sheaf condition in specific phase
satisfiable_p1, witness = prop.decide_sheaf(Phase.PHASE_1)

# Check all phases
satisfiable_all, witness = prop.decide_sheaf(None)

# Verify GF(3) conservation
is_conserved = prop.verify_gf3_conservation(Phase.PHASE_1)
```

### Constraint Propagation

```python
# Propagate constraints from Phase.PHASE_1 to Phase.PHASE_2
prop.propagate_phase_forward(Phase.PHASE_1, Phase.PHASE_2)

# Get phase-specific coloring
colors = prop.get_overlay_coloring(Phase.PHASE_1)

# Get state summary
summary = prop.summary(Phase.PHASE_1)
```

---

## Algorithms

### 1. Adhesion Filter (Per-Phase)

Algorithm: Compute pullback of restrictions and project back

```
Input: adhesion_idx, phase
Output: bool (non-empty pullback)

1. Get adhesion and state for phase
2. For each element in overlap:
   a. Check if element satisfies left restrictions
   b. Check if element satisfies right restrictions
   c. If both satisfied, add to pullback
3. Update state.pullback_elements
4. Return len(pullback) > 0
```

**Complexity**: O(|overlap| × |restrictions|)

### 2. Sheaf Decision (Per-Phase)

Algorithm: Verify sheaf condition for all edges in phase

```
Input: phase (or None for all)
Output: (bool, List[EdgePhaseState])

For each phase to check:
  For each adhesion in phase:
    1. Apply adhesion_filter
    2. If pullback empty → return (False, witness)
    3. Check satisfies_sheaf_condition
    4. If not satisfied → return (False, witness)
    5. Add to witness
Return (True, witness)
```

**Complexity**: O(|adhesions| × |overlap|)

### 3. Phase Forward Propagation

Algorithm: Propagate constraints from source to target phase

```
Input: source_phase, target_phase
Precondition: source_order < target_order

For each adhesion:
  If both phases apply:
    1. Merge left_restrictions[source] → left_restrictions[target]
    2. Merge right_restrictions[source] → right_restrictions[target]
```

**Complexity**: O(|adhesions| × |restrictions|)

---

## GF(3) Conservation

Each phase maintains a sum of trit colors on its edges:

```
Trit Sum (Phase P) = Σ trit_color[edge][P] for all edges in phase
```

**Invariant**: For each phase, the sum must be 0 (mod 3) in cycles

**Verification**:
```python
conserved = prop.verify_gf3_conservation(Phase.PHASE_1)
```

**Why it matters**:
- Ensures balance in constraint propagation
- Prevents asymmetric flow of information
- Enables cyclic consistency checking

---

## Workflow Example

### Scenario: Data Processing Pipeline

**Goal**: Process data through 3 phases with consistency checking

**Step 1: Setup**
```python
prop = EdgePhasePropagatorScoped(
    phases=[Phase.PHASE_1, Phase.PHASE_2, Phase.PHASE_3]
)

# Acquisition phase bags
prop.add_bag(Bag(id="raw_1", elements={1, 2, 3}, phase=Phase.PHASE_1))
prop.add_bag(Bag(id="raw_2", elements={2, 3, 4}, phase=Phase.PHASE_1))

# Validation phase bags
prop.add_bag(Bag(id="validated", elements={2, 3}, phase=Phase.PHASE_2))
```

**Step 2: Create Adhesions**
```python
# Raw data overlap
prop.add_adhesion("raw_1", "raw_2", phases={Phase.PHASE_1})

# Validate against acquisition
prop.add_adhesion("raw_2", "validated",
                  phases={Phase.PHASE_1, Phase.PHASE_2})
```

**Step 3: Set Phase 1 Data**
```python
prop.set_local_data("raw_1", "source", "sensor_A", Phase.PHASE_1)
prop.set_local_data("raw_2", "source", "sensor_A", Phase.PHASE_1)

satisfiable_p1, _ = prop.decide_sheaf(Phase.PHASE_1)
print(f"Phase 1 satisfiable: {satisfiable_p1}")
```

**Step 4: Propagate to Phase 2**
```python
prop.propagate_phase_forward(Phase.PHASE_1, Phase.PHASE_2)

prop.set_local_data("validated", "quality", "high", Phase.PHASE_2)

satisfiable_p2, _ = prop.decide_sheaf(Phase.PHASE_2)
print(f"Phase 2 satisfiable: {satisfiable_p2}")
```

**Step 5: Check Overall Consistency**
```python
summary = prop.summary()
print(f"All GF(3) conserved: {summary['all_gf3_conserved']}")
```

---

## Design Decisions

### 1. Per-Phase Trit Colors

**Decision**: Assign unique GF(3) colors to each edge per phase

**Rationale**:
- Different phases have different algebraic structures
- Allows independent conservation checking
- Enables phase-specific transformations

**Alternative**: Single global trit color
- **Con**: Loses phase information
- **Con**: Can't verify phase-local cycles

### 2. Forward Propagation Only

**Decision**: Constraints only propagate forward in phase order

**Rationale**:
- Phases are ordered (1 → 2 → 3 → 4)
- Later phases depend on earlier ones
- Prevents circular dependencies

**Alternative**: Bidirectional propagation
- **Con**: Could create feedback loops
- **Con**: More complex convergence analysis

### 3. Overlap Preservation

**Decision**: Overlaps don't change per phase

**Rationale**:
- Overlaps defined by elements, not data
- Data on overlaps is what changes
- Simplifies pullback computation

**Alternative**: Phase-specific overlaps
- **Con**: More complex state management
- **Con**: Unclear how overlaps evolve

### 4. Explicit Phase Membership

**Decision**: Bags and adhesions explicitly declare their phases

**Rationale**:
- Sparse: Not all edges apply to all phases
- Efficient: Only process relevant edges
- Explicit: No implicit phase inclusion

**Alternative**: All edges in all phases by default
- **Con**: Wasteful for sparse phase graphs
- **Con**: Hard to exclude edges from phases

---

## Performance Characteristics

| Operation | Complexity | Notes |
|-----------|-----------|-------|
| Add bag | O(1) | Hash map insertion |
| Add adhesion | O(P) | P = # phases |
| Set local data | O(A) | A = # adhesions with bag |
| Adhesion filter | O(\|overlap\| × \|restr\|) | Pullback computation |
| Decide sheaf | O(A × \|overlap\|) | A = # adhesions in phase |
| Propagate forward | O(A × \|restr\|) | A = # adhesions |
| Verify GF(3) | O(A) | A = # adhesions in phase |

**Space Complexity**: O(B + A × P) where B = bags, A = adhesions, P = phases

---

## Testing

### Test Categories

1. **Phase Operations** (5 tests)
   - Phase enumeration
   - Bag phase constraints
   - Trit arithmetic

2. **Structure Building** (4 tests)
   - Propagator creation
   - Adding bags with phases
   - Adding single/multi-phase adhesions

3. **Data Management** (2 tests)
   - Setting phase-specific data
   - Local data propagation

4. **Sheaf Conditions** (3 tests)
   - Per-phase satisfaction
   - Conflict detection
   - All-phase checking

5. **GF(3) Conservation** (2 tests)
   - Per-phase sums
   - Cycle verification

6. **Propagation** (2 tests)
   - Forward propagation
   - Cross-phase constraint flow

7. **Integration** (1 test)
   - Full workflow from Phase 1 to 3

### Running Tests

```bash
pytest test/test_edge_phase_scoped.py -v
```

**Coverage**: 20 test cases, all major paths

---

## Integration Points

### With DuckLake Backend

Store phase-scoped edge states:
```sql
CREATE TABLE IF NOT EXISTS phase_edges (
    world_id TEXT,
    phase INT,
    edge_id TEXT,
    left_bag TEXT,
    right_bag TEXT,
    overlap TEXT,
    trit_color INT,
    satisfied BOOLEAN,
    PRIMARY KEY (world_id, phase, edge_id)
);
```

### With Export Procedures

Track which phases were applied during export:
```python
export_result = ExportResult(
    phase_scoping=True,
    phases_applied=[Phase.PHASE_1, Phase.PHASE_2],
    edge_preservation=True
)
```

### With Consciousness Framework

Use phase propagation as basis for consciousness metrics:
- Phase coherence = % edges satisfied per phase
- Phase flow = constraint propagation rate
- Phase balance = GF(3) conservation status

---

## Future Extensions

### Phase 1: Complete

### Phase 2: Planned (Next)

1. **Bidirectional Propagation** (with cycle detection)
2. **Phase Merging** (combine adjacent phases)
3. **Phase Skipping** (shortcut paths)
4. **Performance Optimization** (lazy evaluation)

### Phase 3: Research

1. **Adaptive Phases** (dynamically determine phases)
2. **Heterogeneous Phases** (non-sequential ordering)
3. **Probabilistic Phases** (fuzzy phase membership)
4. **Nested Phases** (hierarchical phase structure)

---

## References

- **StructuredDecompositions.jl**: adhesion_filter algorithm
- **DecidingSheaves.jl**: sheaf condition implementation
- **GF(3) Theory**: Balanced ternary systems
- **Tree Decompositions**: Treewidth algorithms

---

## Implementation Files

```
lib/edge_phase_propagator_scoped.py      (500+ lines)
test/test_edge_phase_scoped.py           (400+ lines)
docs/EDGE_PHASE_SCOPED_DESIGN.md         (this file)
```

---

**Status**: ✅ Production Ready
**Last Updated**: 2025-12-26
**Maintainer**: MINUS agent (verification layer)

