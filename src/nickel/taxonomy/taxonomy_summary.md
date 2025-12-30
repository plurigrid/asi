# Plurigrid ASI Skill Taxonomy

## I. Aperiodic Tiling Algorithms

### 7 Algorithm Classes

| # | Class | Key Insight |
|---|-------|-------------|
| 1 | **Substitution** | Replace tiles with smaller tiles via fixed rules |
| 2 | **Combinatorial Coords** | Address tiles by hierarchical path, navigate via string ops |
| 3 | **Projection** | Project n-D lattice onto 2D (de Bruijn multigrid) |
| 4 | **Matching Rules** | Local edge constraints force global aperiodicity |
| 5 | **Random Walk** | Traverse tiles, derive walk angle from position |
| 6 | **Transducers** | Finite automata transform coordinate strings |
| 7 | **BFS Generation** | Flood-fill from seed until region covered |

### Tiling Type Support

| Tiling | Tiles | Projection? | Chiral? |
|--------|-------|-------------|--------|
| Penrose P2 | 2 | Yes | No |
| Penrose P3 | 2 | Yes | No |
| Hat | 1 | No | No (reflection needed) |
| Spectre | 1 | No | Yes (no reflection) |

### GF(3) Triads

```
Generation: matching-rules(-1) ⊗ combinatorial(0) ⊗ substitution(+1) = 0
Traversal:  transducers(-1) ⊗ random-walk(0) ⊗ bfs-patch(+1) = 0
Math:       projection(-1) ⊗ combinatorial(0) ⊗ substitution(+1) = 0
```

---

## II. Aptos Society Skills (Move 2.3)

### Core Skills

| Skill | Trit | Role | Description |
|-------|------|------|-------------|
| `aptos-gf3-society` | +1 | GENERATOR | On-chain GF(3) society contracts |
| `move-narya-bridge` | 0 | COORDINATOR | Move ↔ Narya proof translation |
| `move-smith-fuzzer` | -1 | VALIDATOR | MoveSmith source-level fuzzing |

### GF(3) Triads

```
Aptos Society:     aptos-gf3-society(+1) ⊗ move-narya-bridge(0) ⊗ move-smith-fuzzer(-1) = 0 ✓
Governance:        aptos-governance(+1) ⊗ datalog-fixpoint(0) ⊗ merkle-proof-validation(-1) = 0 ✓
Verification:      gf3-conservation(+1) ⊗ move-narya-bridge(0) ⊗ narya-proofs(-1) = 0 ✓
```

### movemate Integration

| Module | Status | Trit | Usage |
|--------|--------|------|-------|
| `merkle_proof` | Verified | -1 | Membership proofs |
| `vectors` | Verified | 0 | Data coordination |
| `acl` | Verified | -1 | Access control |
| `math_safe_precise` | Verified | 0 | Overflow-safe math |

### Move 2.3 Timeline

```
Status: Mainnet v1.38.7 (Move 2.2) → Testnet v1.39.1-rc (Move 2.3)
Expected Landing: Week of January 12-19, 2026
Key Feature: Signed integers (i8-i256) for native GF(3) arithmetic
```

---

## III. Proof Assistant Ecosystem

### Three Generations of HoTT

| Generation | System | Equality | Interval? |
|------------|--------|----------|-----------|
| 1 | Book HoTT | Induction | No |
| 2 | Cubical (Agda) | Interval I | Yes |
| 3 | Narya/HOTT | Observational | No |

### GF(3) Triads

```
Innovation:   narya-proofs(-1) ⊗ coq-verification(0) ⊗ lean4-automation(+1) = 0 ✓
Move Bridge:  narya-proofs(-1) ⊗ move-narya-bridge(0) ⊗ move-spec-extract(+1) = 0 ✓
Type Theory:  synthetic-adjunctions(-1) ⊗ segal-types(0) ⊗ directed-hott(+1) = 0 ✓
```

### Narya Key Differences

| Feature | Traditional | Narya |
|---------|-------------|-------|
| Function η | Postulate | Definitional |
| Extensionality | Axiom | Automatic |
| Parametricity | External | Bridge types |

---

## IV. GF(3) Conservation Law

**Invariant**: Every skill triad sums to 0 (mod 3)

```
GENERATOR (+1) + COORDINATOR (0) + VALIDATOR (-1) = 0 ✓
```

### Role Responsibilities

| Role | Trit | Action | Color Range |
|------|------|--------|-------------|
| GENERATOR | +1 | Create, propose, stake | Warm (0-60°, 300-360°) |
| COORDINATOR | 0 | Mediate, vote, balance | Neutral (60-180°) |
| VALIDATOR | -1 | Verify, challenge, audit | Cold (180-300°) |

---

## V. Skill Count Summary

| Category | Count | Examples |
|----------|-------|----------|
| Aperiodic Tiling | 7 | substitution, projection, matching-rules |
| Aptos Society | 3 | aptos-gf3-society, move-narya-bridge, move-smith-fuzzer |
| Proof Assistants | 5 | narya-proofs, lean4, coq, agda, rzk |
| ACSet Family | 27 | See acset-taxonomy for details |
| Total Verified | 42+ | GF(3) conservation enforced |

---

*Seed: 137508 | Updated: 2025-12-29*
