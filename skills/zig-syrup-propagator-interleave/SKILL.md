---
name: zig-syrup-propagator-interleave
description: >
  Bridge connecting zig-syrup advanced computational modules (propagator networks,
  homotopy continuation, AGM belief revision, QRTP air-gapped transport,
  passport.gay identity, geo.zig spatial, xev_io async) to the ASI skill graph.
  Use when wiring Radul-Sussman propagators, implementing CellValue lattice
  merge, running homotopy continuation for polynomial solving, performing AGM
  belief revision, or building air-gapped identity verification via QRTP.
---

# zig-syrup Advanced Modules x ASI Interleave

Bridge connecting 7 zig-syrup computational modules to the ASI skill graph.

## Module Anatomy

### 1. propagator.zig -- Radul-Sussman Propagator Networks

```zig
// CellValue: partial information lattice
// Ordering: Nothing < Value < Contradiction
pub fn CellValue(comptime T: type) type {
    return union(enum) {
        nothing,
        value: T,
        contradiction: struct { a: T, b: T },
    };
}

// latticeMerge: the join operation
// Nothing -> adopts incoming
// same Value -> idempotent
// different Value -> Contradiction
// Contradiction absorbs all
pub fn latticeMerge(existing: CellValue(T), incoming: CellValue(T)) CellValue(T) { ... }
```

- **Cell**: holds CellValue + list of Propagator neighbors; alerts neighbors on change
- **Propagator**: inputs from Cells, applies function, sets output Cells
- Bidirectional constraint propagation throughout the network
- Special functions: `neurofeedback_gate` (BCI), `adjacency_gate` (spatial), `focus_brightness`

### 2. homotopy.zig -- Polynomial Homotopy Continuation

```
H(x, t) = (1 - t) * G(x) + t * F(x)
```

- Deformation from start system G (known solutions) to target system F
- Complex number polynomial root tracking along paths
- Integrates with syrup serialization (paths are Syrup-serializable)
- Integrates with continuation.zig for resumable pipeline execution

### 3. continuation.zig -- AGM Belief Revision + Trit Arithmetic

```zig
const Belief = struct { proposition: []const u8, entrenchment: f64 };
const BeliefSet = struct {
    beliefs: std.ArrayList(Belief),
    fn expand(self, b: Belief) void { ... }     // add without consistency check
    fn contract(self, prop: []const u8) void { ... }  // remove belief + negation
    fn revise(self, b: Belief) void {            // Levi identity: (K - !p) + p
        self.contract(negate(b.proposition));
        self.expand(b);
    }
};

const Trit = enum { minus, zero, plus };  // -1, 0, +1
```

### 4. QRTP -- QR Transfer Protocols (Air-Gapped Identity)

- Fountain-coded QR codes for data transfer across air gaps
- Each source block = Cell, each encoded block = Propagator
- Contradiction = transmission error detection
- Scoped propagators applied to erasure decoding

### 5. passport.gay -- Identity Protocol

- Homotopy continuity for liveness detection (deformation must be continuous)
- Generates trit trajectories as identity fingerprints
- Identity proofs fountain-encoded into QR frames via QRTP for air-gapped verification

### 6. geo.zig -- Geographic Integration

- OLC (Open Location Code / Plus Codes) encoding/decoding
- Syrup serialization for geographic types: CodeArea, Coordinate, PlusCode
- Zero-copy coordinate handling with CID determinism for coordinates
- Spatial propagation via adjacency_gate in propagator.zig

### 7. xev_io -- Completion-Based Async I/O

- Async I/O for Syrup protocol via libxev
- Completion-based (not readiness-based): aligns with propagator "alert on change" model
- Drives the wire protocol layer for zig-syrup OCapN transport

## ASI Integration Points

### propagator.zig <-> propagators skill
Direct match. ASI `propagators` skill provides the Radul-Sussman theory; `propagator.zig` is the Zig implementation.

### neurofeedback_gate <-> reafference-corollary-discharge
The neurofeedback_gate IS a corollary discharge: predicts brightness from focus. Wire to `unified-reafference` skill.

### continuation.zig <-> abductive-monte-carlo
AGM belief revision IS abductive reasoning:
- `expand` = add hypothesis without consistency check (abduction)
- `contract` = remove refuted hypothesis (contraction)
- `revise` = Levi identity: contract negation, then expand (belief update)

### homotopy.zig <-> crn-topology, polynomial-dynamics
- Polynomial system solving for CRN equilibria
- Solution path tracking with classification
- Liveness detection for passport.gay (continuous deformation = alive)

### QRTP <-> proof-of-frog, merkle-proof-validation
- Fountain coding = erasure-resilient data transport
- QR air-gap verification = merkle proof without network connectivity
- Propagator-based decoder: each frame incrementally resolves Cells toward proof completion

### geo.zig <-> osm-topology, geohash-coloring, duckdb-spatial
- OLC Plus Codes = spatial addressing for propagator networks
- Syrup-serialized coordinates feed adjacency_gate
- CID-deterministic coordinates enable content-addressed spatial data

### xev_io <-> nashator, zig-syrup wire protocol
- libxev completion-based I/O drives zig-syrup OCapN transport layer
- Nashator (:9999) uses same wire format: 4-byte BE + JSON-RPC 2.0

## Gap Registry

| Gap | Module | Missing Capability |
|---|---|---|
| G1 | propagator.zig | No dependent type checking on CellValue lattice |
| G2 | homotopy.zig | No GPU-accelerated path tracking |
| G3 | continuation.zig | No persistent belief revision log (only in-memory) |
| G4 | QRTP | No forward error correction beyond fountain coding |
| G5 | passport.gay | No revocation mechanism for compromised identities |
| G6 | geo.zig | No H3 hexagonal indexing (only OLC) |
| G7 | xev_io | No TLS layer on async transport |
| G8 | cross-module | No unified test harness across all 7 modules |

## Cross-Connection Map

```
propagator.zig
  +-- neurofeedback_gate -> bci-phenomenology, reafference-corollary-discharge
  +-- adjacency_gate     -> osm-topology, geohash-coloring (via geo.zig)
  +-- QRTP fountain      -> air-gapped identity (passport.gay)
  +-- scoped propagators -> abductive-monte-carlo constraint networks

homotopy.zig
  +-- polynomial solving  -> crn-topology, chemical-organization-theory
  +-- liveness detection  -> passport.gay identity proof

continuation.zig
  +-- AGM belief revision -> abductive-monte-carlo, dynamic-sufficiency
  +-- resumable pipelines -> duckdb-timetravel, time-travel-crdt

geo.zig
  +-- OLC encoding        -> osm-topology, duckdb-spatial
  +-- Syrup coordinates   -> adjacency_gate spatial propagation
  +-- CID determinism     -> merkle-proof-validation

xev_io
  +-- libxev async        -> nashator event loop, zig-syrup wire protocol
  +-- completion model    -> propagator "alert on change" alignment
```
