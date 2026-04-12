# Extensions — Closing the Unconnected

Three threads flagged in SKILL.md as "unconnected (yet)". Each is a concrete next step with a decidable integration point.

## E1 — HyperNEM / PoincaréBall embedding of the 6-world seed

**Current state.** `world-hopping` materializes 6 worlds from seed `0x626d6f727068` with GF(3)-balanced trits `(-1,0,+1,-1,0,+1)`. Each world is a discrete point; distances between worlds are undefined.

**Extension.** Embed the 6 worlds in a PoincaréBall so trit neighborhoods are continuous. Hyperbolic geometry is the natural home for tree-structured skill chains — negative curvature matches branching factor of ASI skill graph (out-degree 5 observed for narya-proofs, bisimulation-game, etc.).

**Integration point.** Add `world_position: [f64; 3]` to each world's JSON alongside existing `trit: i8`. The bisimulation-oracle Merkle leaf can include the position without changing the root-recovery algorithm — new leaf schema, backwards-compatible via versioned proof_uri.

**Decidable test.** Nearest-neighbor queries on the 6-world embedding should recover the GF(3) balance: for each world `w`, its closest world in Poincaré distance should have complementary trit (sum ≡ 0 mod 3).

## E2 — VCGAuction over quest bounties

**Current state.** `quest::create_quest` uses first-come-first-served: first valid `submit_solution` drains the 2 APT escrow. This is a Dutch auction at t=0, trivial Nash.

**Extension.** Wrap the quest in a Vickrey–Clarke–Groves mechanism: sealed bids on solution quality (e.g., proof size, gas cost, skill chain length), winner pays second-highest bid, escrow split by VCG payments. Matches the EIP-1559 open game pattern already in memory (game-theory.md).

**Integration point.** New Move module `quest_auction.move` sitting above `kolmogorov_codex_quest.move`. Existing `submit_solution` becomes the *claim* phase after auction settles. Reuses IdentityProof unchanged.

**Decidable test.** With 3 simulated bidders (honest, bluffer, free-rider), VCG settlement should reveal honest bidder as winner and charge them the second-price — truthful bidding as dominant strategy, verified via a Python simulation that runs `submit_solution` only for the declared winner.

## E3 — Retrocausal scheduling

**Current state.** `proof_timestamp` must satisfy `now - proof_timestamp <= 3600` (1 hour window). Sessions are scheduled *before* proof generation; the timestamp is an accepted-in-the-past.

**Extension.** Post-solve retrocausal scheduling: use the distribution of `proof_timestamp` values across successful claims to schedule *future* BCI sessions in the Pareto-optimal windows (time-of-day, ambient light from VÄRMBLIXT, thread-border-router load).

**Integration point.** Off-chain analyzer reads Aptos events for `SolutionSubmitted`, fits a kernel density estimate over `(proof_timestamp mod 86400, gf3_sum, skill_count)`, outputs a schedule heuristic consumable by `world-hopping`'s seed selection.

**Decidable test.** Hold out 20% of historical `SolutionSubmitted` events as validation; the KDE-driven schedule should predict submission success (yes/no within ±3h window) at AUC > 0.7 on the held-out set. If AUC ≤ 0.5, retrocausal signal is absent and we drop the thread.

## Priority order

E1 (HyperNEM) is prerequisite for the other two:
- E2's VCG quality metric benefits from hyperbolic distance between proof structures
- E3's KDE kernel benefits from curved ambient geometry for `gf3_sum × skill_count`

Start E1. Ship as `world-hopping-hyperbolic` SKILL.md addendum.

## Cross-references (already in memory)
- `game-theory.md`: VCG over EIP-1559 open game (E2 blueprint)
- `ico-causal-order.md`: det(S(-1))=-1 perfect parity (E3 retrocausal validity check)
- `bci-device-ecosystem.md`: fNIRS HbO/HbR modality = natural 2-axis for E1 embedding
