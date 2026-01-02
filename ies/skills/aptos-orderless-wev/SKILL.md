---
name: aptos-orderless-wev
description: 'Aptos Orderless WEV Skill'
version: 1.0.0
---

# Aptos Orderless WEV Skill

> **Trit**: +1 (PLUS) - Generative parallel execution

World Extractable Value via Aptos orderless transactions with Strong Parallelism Invariance (SPI) guarantees and GF(3) conservation.

## Core Concept

**WEV (World Extractable Value)** exploits **knowledge differentials** between domains in orderless execution systems. Unlike MEV (order-dependent extraction), WEV leverages parallel execution invariance.

```
┌─────────────────────────────────────────────────────────────────────┐
│  MEV vs WEV                                                         │
├─────────────────────────────────────────────────────────────────────┤
│  MEV: Extract value from transaction ORDERING                      │
│       Sequencer sees tx₁ before tx₂ → front-run                    │
│       Order matters, position is power                             │
│                                                                     │
│  WEV: Extract value from KNOWLEDGE DIFFERENTIALS                   │
│       World A knows X, World B knows Y                              │
│       Orderless execution → position irrelevant                     │
│       Knowledge asymmetry is power                                  │
└─────────────────────────────────────────────────────────────────────┘
```

## Aptos Orderless Transactions (AIP-123)

From [Aptos Documentation](https://aptos.dev/build/guides/orderless-transactions):

- **Purpose**: Execute transactions out of order for multi-machine signing
- **Replay Protection**: Uses `replayProtectionNonce` (random u64)
- **Max Expiration**: 60 seconds
- **Block-STM**: Parallel execution engine

```typescript
// Orderless transaction structure
interface OrderlessTransaction {
  replayProtectionNonce: bigint;  // Random u64 for replay protection
  payload: TransactionPayloadPayload;  // AIP-129 payload
  expirationTimestamp: number;  // Max 60 seconds
}
```

## GF(3) Conservation as Orderless Guarantee

For any valid WEV transaction triplet, the sum of trits must be zero:

```
PLUS  (+1): Generators (A, B, C, D, E, W, X, Y, Z)
ERGODIC(0): Coordinators (F, G, H, I, J, K, L, M)
MINUS (-1): Validators (N, O, P, Q, R, S, T, U, V)

Sum: 9(+1) + 8(0) + 9(-1) = 0 ✓
```

### WEV Triplet Structure

```clojure
(defn wev-triplet [from-world to-world mediator]
  (let [trits [(world-trit from-world)   ; PLUS (+1) sender
               (world-trit mediator)      ; ERGODIC (0) coordinator
               (world-trit to-world)]]    ; MINUS (-1) validator
    (assert (zero? (mod (reduce + trits) 3))
            "GF(3) conservation violated!")
    {:transactions [from-world mediator to-world]
     :orderless true
     :conserved true}))
```

## Strong Parallelism Invariance (SPI)

```
SPI Theorem: For any deterministic generator G with seed s,
             ∀ permutation π of indices I:
             G(s, I) ≡ G(s, π(I)) (modulo ordering)
```

**Verification**:
- `ordered == reversed == shuffled`
- `parallel == sequential`
- GF(3) sum preserved across all orderings

## Open Games Formalization

### Orderless Game as Open Game

```haskell
data OrderlessGame s t a b = OrderlessGame
  { play    :: s -> a                    -- Forward: knowledge state → action
  , coplay  :: s -> b -> t               -- Backward: observation → utility
  , nonce   :: Word64                    -- Replay protection
  , triplet :: (World, World, World)     -- GF(3)-balanced worlds
  }

-- Composition is order-invariant
instance Category OrderlessGame where
  (.) g h = OrderlessGame
    { play = play g . play h
    , coplay = \s b -> coplay h s (coplay g (play h s) b)
    , nonce = xor (nonce g) (nonce h)  -- Combined nonce
    , triplet = mergeTriplets (triplet g) (triplet h)
    }
```

### Epistemic Arbitrage as Nash Equilibrium

```haskell
-- Knowledge differential game
epistemicArbitrage :: OpenGame KnowledgeState KnowledgeState Action Utility
epistemicArbitrage = OpenGame
  { play = \k -> 
      let diff = knowledgeDifferential k
      in if profitable diff then ExtractWEV else Wait
  , coplay = \k a -> 
      case a of
        ExtractWEV -> k { value = value k + wevProfit }
        Wait -> k
  , equilibrium = \k -> 
      -- Nash: extract iff differential profitable
      profitable (knowledgeDifferential k) == (play k == ExtractWEV)
  }
```

## Triangle Arbitrage Across Worlds

```
World_PLUS ←──────────→ World_ERGODIC
     (+1)    knowledge      (0)
      ▲         flow         ▲
       \                    /
        \   GF(3) = 0      /
         \                /
          ▼              ▼
           World_MINUS
              (-1)
```

### Mediator Selection Logic

```clojure
(defn find-mediator [worlds from-world to-world]
  (let [from-trit (get-in worlds [from-world :trit])
        to-trit (get-in worlds [to-world :trit])
        sum-mod3 (mod (+ from-trit to-trit) 3)
        needed-trit (case sum-mod3
                      0  0    ; need 0 to make sum 0
                      1 -1    ; need -1: (1 + (-1) = 0)
                      2  1)]  ; need +1: (2 + 1 = 3 ≡ 0)
    (first (filter #(= needed-trit (get-in worlds [% :trit]))
                   (keys worlds)))))
```

## Babashka Implementation

### `wev_orderless.bb`

```clojure
#!/usr/bin/env bb
;; World Extractable Value via orderless Aptos transactions

(require '[babashka.cli :as cli])

(def WORLDS
  {:a {:trit +1 :wallet "0x...a"}
   :b {:trit +1 :wallet "0x...b"}
   :f {:trit  0 :wallet "0x...f"}  ; mediator
   :n {:trit -1 :wallet "0x...n"}
   :p {:trit -1 :wallet "0x...p"}})

(defn knowledge-differential [from-world to-world]
  ;; Compute knowledge asymmetry between worlds
  (let [k1 (io/file (str "/tmp/" (name from-world) "_knowledge"))
        k2 (io/file (str "/tmp/" (name to-world) "_knowledge"))]
    (cond
      (and (.exists k1) (not (.exists k2))) :from-advantage
      (and (.exists k2) (not (.exists k1))) :to-advantage
      :else :equilibrium)))

(defn wev-triplet [from to]
  (let [mediator (find-mediator WORLDS from to)
        trits [(get-in WORLDS [from :trit])
               (get-in WORLDS [mediator :trit])
               (get-in WORLDS [to :trit])]]
    (assert (zero? (mod (reduce + trits) 3)))
    {:from from :mediator mediator :to to
     :orderless true
     :nonce (rand-int Integer/MAX_VALUE)}))

(defn extract-wev [from to]
  (let [triplet (wev-triplet from to)
        diff (knowledge-differential from to)]
    (when (not= diff :equilibrium)
      (println "WEV opportunity:" diff)
      (println "Triplet:" triplet)
      triplet)))

;; CLI
(def cli-opts
  {:scan    {:fn (fn [_] (scan-opportunities WORLDS))}
   :triplet {:fn (fn [{:keys [from to]}] 
                   (wev-triplet (keyword from) (keyword to)))}
   :extract {:fn (fn [{:keys [from to]}]
                   (extract-wev (keyword from) (keyword to)))}})

(cli/dispatch cli-opts *command-line-args*)
```

## ACSet Schema

```julia
@present SchOrderlessWEV(FreeSchema) begin
    # Worlds
    World::Ob
    Transaction::Ob
    Triplet::Ob
    
    # World structure
    Trit::AttrType
    Wallet::AttrType
    Knowledge::AttrType
    
    world_trit::Attr(World, Trit)
    world_wallet::Attr(World, Wallet)
    world_knowledge::Attr(World, Knowledge)
    
    # Triplet structure (GF(3)-balanced)
    plus_world::Hom(Triplet, World)
    ergodic_world::Hom(Triplet, World)
    minus_world::Hom(Triplet, World)
    
    # Transaction
    Nonce::AttrType
    tx_nonce::Attr(Transaction, Nonce)
    tx_triplet::Hom(Transaction, Triplet)
    
    # Constraint: sum of trits = 0 (mod 3)
    # Enforced at construction time
end
```

## GF(3) Triads

```
aptos-orderless-wev (+1) ⊗ boneh-roughgarden-wev (0) ⊗ solver-fee (-1) = 0 ✓
aptos-orderless-wev (+1) ⊗ open-games (0) ⊗ intent-sink (-1) = 0 ✓
aptos-orderless-wev (+1) ⊗ gay-mcp (0) ⊗ protocol-evolution-markets (-1) = 0 ✓
```

## Integration

| Skill | Connection | Direction |
|-------|------------|-----------|
| `open-games` | OrderlessGame as Para morphism | → |
| `boneh-roughgarden-wev` | Shared WEV mechanism | ↔ |
| `spi-parallel-verify` | Verification of order-invariance | ← |
| `gay-mcp` | Seed generation for nonces | ← |
| `epistemic-arbitrage` | Knowledge differential exploitation | → |

## CLI Commands

```bash
# Scan for WEV opportunities
bb scripts/wev_orderless.bb scan

# Build GF(3)-balanced triplet
bb scripts/wev_orderless.bb triplet --from a --to p

# Extract WEV (if differential exists)
bb scripts/wev_orderless.bb extract --from a --to p

# Verify SPI
just spi-verify triplet.json
```

## References

1. **AIP-123**: Orderless Transactions
2. **AIP-129**: Transaction Payload Payload
3. **Block-STM**: Aptos parallel execution engine
4. **Ghani, Hedges et al.**: Compositional Game Theory
5. **Gay.jl**: SplitMix64 for deterministic nonces

---

**Skill Name**: aptos-orderless-wev
**Type**: Parallel Execution / Game Theory
**Trit**: +1 (PLUS)
**Key Property**: GF(3)-conserved orderless triplets with SPI guarantees
