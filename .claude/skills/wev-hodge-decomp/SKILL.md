# World Extractable Value via Pair-Graph Hodge Decomposition

**Status**: 🧪 Draft — K₃/K₄/K₅ verified
**Type**: Discrete cohomology / optimal transport / market microstructure
**Principle**: WEV = non-exactness of the world, measured in L^p over H₁
**Frame**: Antisymmetric 1-cochain on pair graph → Hodge splits into coboundary (potential) + harmonic (residue)
**GF(3)/GF(5)**: Both required — GF(3) collapses uniform-sign RPS cycles; GF(5) witnesses orientation-H¹

---

## Core Construction

Given pair graph `G = (V, E)` observed at epoch `t` with signed 1-cochain `α : E → ℝ` satisfying `α(i,j) = −α(j,i)`:

1. Form incidence matrix `B : ℝ^|E| × ℝ^|V|`, `B[e=(u,v), u] = −1`, `B[e, v] = +1`.
2. Solve normal equations `BᵀB φ = Bᵀα` (Tikhonov-damped if graph has isolated components). `L := BᵀB` is the graph Laplacian on vertices.
3. Decompose `α = δφ* + harmonic` where `δφ*(e=(u,v)) = φ*(v) − φ*(u)`.
4. `WEV := ‖harmonic‖_p` — edge-space `p`-norm. Common choices:
   - `WEV_L¹` = min trade volume to close harmonic under uniform cost per trade.
   - `WEV_L²` = min trade energy under quadratic price-impact cost.

The coboundary part `δφ*` is explained by a vertex potential `φ*` — this is the Kantorovich dual / "type price" / clearing prices. The harmonic part is what no potential can explain — the **extractable residue**.

---

## 5-Instance Unification

Antisymmetric α required. Semantics splits into extractive (closure = transaction) vs diagnostic (observational):

| Layer | Vertex | α (edge signal) | WEV semantics |
|---|---|---|---|
| RPS / games | agent | regret-sign | gap-to-Nash |
| Hough MM harness | trader / MM | PnL-asymmetry | arb budget [extractive] |
| MEV | tx | ordering-regret | MEV bound [extractive] |
| Wardrop / Braess | road segment | travel-time-Δ | Braess cost [extractive] |
| MAC RF observer | device | `sgn(RSSI_i − RSSI_j)` | flock evidence [diagnostic] |
| Passport sybil | address | `sgn(first_stamp_t_i − t_j)` under scorer C | sybil evidence [diagnostic] |
| Face-patch fMRI | patch | partial-correlation precedence under stimulus | prosopagnosia index [diagnostic] |

**Warning**: symmetric edge measures (RSSI correlation, stamp Jaccard) violate antisymmetry and are the wrong shape. Use **temporal precedence**, not co-presence magnitude. Co-presence is the *filter on which edges exist*; precedence is the *edge value*.

---

## Reference implementation (Guile, verified 2026-04-23)

Pure core — no goblins, no actors, no cells. Pair-graph Hodge in `~80` lines of Scheme:

```scheme
;; solve BᵀBφ = Bᵀα via damped Gauss-Jordan
(define (hodge alpha E V)
  (let* ((B (incidence E V))
         (Bt (transpose B))
         (BtB (mat*mat Bt B))
         (Bta (mat*vec Bt alpha))
         (phi (solve BtB Bta 1e-6))
         (delta-phi (mat*vec B phi))
         (harmonic (vec-sub alpha delta-phi)))
    (values phi delta-phi harmonic)))

(define (WEV-L1 alpha E V)
  (call-with-values
    (lambda () (hodge alpha E V))
    (lambda (_ _ h) (vec-norm1 h))))
```

Forj/Clojure port drops naturally into `propagator-nash.clj` — the pair graph is already there from the Čech H¹ extension.

---

## K₅ Worked Example (RPS tournament, σ=(R P S R P))

```
V = (a b c d e)
E = ((a b) (a c) (a d) (a e) (b c) (b d) (b e) (c d) (c e) (d e))
α = ( 1  -1   0   1   1  -1   0   1  -1   1)
```

Hodge:
- `φ* = (R:−0.2, P:+0.2, S:0, R:−0.2, P:+0.2)` — the strategy-type potential emerges automatically
- `δφ* = (0.4, 0.2, 0, 0.4, -0.2, -0.4, 0, -0.2, 0.2, 0.4)`
- `harmonic = (0.6, -1.2, 0, 0.6, 1.2, -0.6, 0, 1.2, -1.2, 0.6)`
- `WEV_L¹ = 7.2`, `WEV_L² = 2.68`
- Coboundary energy = 0.8

**Basis-cycle sum was basis-dependent undercount:** BFS-star fundamental cycles give `Σ |⟨α,γ⟩| = 6`, but edges in the harmonic carry non-zero mass on edges whose basis-cycle circulations cancel. Edge-L¹ (7.2) is the correct basis-free invariant.

**Greedy cycle-by-cycle closure with uniform flow bleeds residue** into previously-zero cycles because BFS-star cycles share edges. To close cleanly, subtract the *L²-orthogonal projection* onto span(γ), not the uniform-t projection.

---

## Connections

- **Kantorovich duality**: duals exist ⇔ `harmonic = 0` ⇔ `α ∈ B¹` ⇔ clearing prices exist
- **Martingale OT** (Beiglböck–Henry-Labordère–Penkner): dynamic no-arb = sheaf-H¹ = 0 across time-epochs
- **Sinkhorn / entropic OT**: `^best-response-propagator`'s softmax at temperature `1/β` IS the Schrödinger-bridge iteration; its convergence monitor is `WEV → 0`
- **Kyle's λ**: `∂WEV/∂(market depth)` — Kyle is the marginal of WEV
- **Tsao face-patch system** (Chang-Tsao 2017, Bao-She-Tsao 2020): 6-patch face cover is a sheaf; prosopagnosia and Thatcher illusion predicted as non-trivial H¹ on the cover. fMRI pair-graph + Hodge = **prosopagnosia index**. StyleGAN alignment = sybil attack at the axis-code identity layer.

---

## Open probes

- **Weighted Hodge**: replace `L = BᵀB` with `BᵀWB` where `W` weights edges by observation confidence / inverse-variance.
- **Dynamic (sheaf over epochs)**: persistent harmonic across time → alert, transient → noise. Dynamic-WEV / static-WEV ratio as alert scalar.
- **Cost-of-closure optimization**: given per-edge costs `c_ij`, minimum-cost closure is an LP over edge flows; extractable fraction depends on cost structure.
- **Directed-graph Hodge**: for intrinsically asymmetric interactions (e.g. MM-vs-flow where MM doesn't attack trader back), use directed combinatorial Hodge (Jiang-Lim-Yao-Ye 2011 `HodgeRank`).

---

## Verification trail

- Pure Guile K₃ (RPS): `triangle-trit = 0` in GF(3) [collapse], `= 3` in GF(5) [witness] ✓
- Pure Guile K₄ (σ_d = σ_a): only RPS sub-triangle circulation −3; others 0 ✓
- Pure Guile K₅ (σ = R P S R P): two active cycles ±3, WEV_L¹ = 7.2, WEV_L² = 2.68 ✓
- Memory trail: `world-extractable-value.md`, `propagator-nash-cocycle.md`

---

## GF(3) triadic balance

- **+1 Play**: constructions (incidence, Laplacian, Hodge solve, WEV computation)
- **0 Witness**: audit (antisymmetry check, basis-independence check, extract-vs-diagnose split)
- **−1 Coplay**: applications (MM harness, MAC observer, Passport sybil, face-patch fMRI)

Triadic sum over this skill = 0 (mod 3) ✓
