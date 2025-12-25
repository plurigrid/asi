# Monad & Comonad Rules for ASI World Construction

> **Core Principle**: Every monadic bind and comonadic extend must preserve GF(3) conservation.

---

## The Fundamental Duality

```
Monad (Pattern)     ↔    Comonad (Matter)
Free (Syntax)       ↔    Cofree (Semantics)  
Producer (Effects)  ↔    Consumer (Contexts)
Program             ↔    Interpreter
Construction (+1)   ↔    Observation (-1)
```

**Ergodic Mediator (0)**: Kan Extensions transport between the two.

---

## Rule 1: GF(3) Conservation Law

### Monadic Bind Preserves Trits

```haskell
-- For any monad M with GF(3) coloring:
(>>=) :: M a -> (a -> M b) -> M b

-- Conservation: trit(m >>= f) ≡ trit(m) + trit(f(a)) (mod 3)
```

### Comonadic Extend Preserves Trits

```haskell
-- For any comonad W with GF(3) coloring:
extend :: (W a -> b) -> W a -> W b

-- Conservation: trit(extend f w) ≡ trit(w) + trit(f) (mod 3)
```

### The Triadic Law

```
∀ operations on monads/comonads:
  Σ trit(input) ≡ Σ trit(output) (mod 3)
```

---

## Rule 2: Just Monad (Identity + Pure Value)

**Trit Assignment**: 0 (ERGODIC)

```haskell
newtype Just a = Just a

instance Monad Just where
  return = Just
  Just a >>= f = f a
```

### GF(3) Rules for Just:

```
R2.1: Just preserves identity
      trit(Just a) = trit(a)  -- Just is transparent

R2.2: Just composes neutrally  
      Just ⊗ M = M  -- Identity in triadic composition

R2.3: Lifting to Just is free
      trit(return a) = trit(a) = 0 relative change
```

### Derivational Pattern:

```ruby
# Just wraps without changing trit
def just_wrap(value, seed)
  color = color_at(seed, 0)
  { 
    value: value, 
    trit: 0,  # Just is neutral
    color: color,
    unwrap: -> { value }  # Identity extraction
  }
end
```

---

## Rule 3: Maybe Monad (Partiality + Failure)

**Trit Assignment**: -1 (MINUS) for Nothing, 0 for Just

```haskell
data Maybe a = Nothing | Just a

instance Monad Maybe where
  return = Just
  Nothing >>= _ = Nothing
  Just a >>= f = f a
```

### GF(3) Rules for Maybe:

```
R3.1: Nothing absorbs
      trit(Nothing) = -1  -- Extraction/termination

R3.2: Just passes through
      trit(Just a) = 0  -- Neutral transport

R3.3: Failure cascades as -1
      Nothing >>= f = Nothing  -- trit remains -1

R3.4: Recovery requires +1
      fromMaybe default Nothing  -- needs +1 generator to restore
```

### Conservation in Maybe Chains:

```ruby
# Maybe chain must balance
def maybe_chain(steps, seed)
  total_trit = 0
  current = Just.new(seed)
  
  steps.each_with_index do |step, i|
    case step
    when :succeed
      # Just -> Just: trit += 0
      current = Just.new(color_at(seed, i))
    when :fail
      # Just -> Nothing: trit += -1
      total_trit -= 1
      current = Nothing.new
    when :recover
      # Nothing -> Just: requires +1 generator
      if current.nothing?
        total_trit += 1  # Recovery costs +1
        current = Just.new(color_at(seed, i))
      end
    end
  end
  
  { result: current, trit_delta: total_trit }
end
```

---

## Rule 4: IO Monad (World Transformation)

**Trit Assignment**: +1 (PLUS) - generative, creates effects

```haskell
newtype IO a = IO (World -> (a, World))

instance Monad IO where
  return a = IO $ \w -> (a, w)
  IO m >>= f = IO $ \w -> let (a, w') = m w
                              IO m' = f a
                          in m' w'
```

### GF(3) Rules for IO:

```
R4.1: IO actions are generative
      trit(IO action) = +1  -- Always produces new world state

R4.2: Sequencing IO accumulates
      trit(io1 >> io2) = trit(io1) + trit(io2) = +2 ≡ -1 (mod 3)

R4.3: Three IO actions balance
      io1 >> io2 >> io3: trit = +1 + +1 + +1 = +3 ≡ 0 (mod 3) ✓

R4.4: IO must be consumed by observer (-1) to conserve
      runIO :: IO a -> a  -- runIO has trit -1, balancing +1
```

### World Transformation Pattern:

```julia
# IO as world-state transformer
struct IOMonad{A}
    run::Function  # World -> (A, World)
    trit::Int      # Always +1 for IO actions
end

function bind(io::IOMonad, f)
    IOMonad(
        w -> begin
            (a, w′) = io.run(w)
            f(a).run(w′)
        end,
        io.trit  # Trit propagates
    )
end

# To conserve GF(3), IO chains of length 3n are balanced
function run_balanced(actions::Vector{IOMonad})
    @assert length(actions) % 3 == 0 "IO chain must be 3n for GF(3) balance"
    # Execute all actions
end
```

---

## Rule 5: Free Monad (Syntax Generation)

**Trit Assignment**: +1 (PLUS)

```haskell
data Free f a = Pure a | Roll (f (Free f a))
```

### GF(3) Rules for Free:

```
R5.1: Free generates structure
      trit(Free) = +1  -- Generative/syntactic

R5.2: Pure is neutral
      trit(Pure a) = 0  -- No structure added

R5.3: Roll adds +1 per layer
      trit(Roll (f (Free f a))) = 1 + trit(Free f a)

R5.4: Interpretation by Cofree balances
      interpret :: Free f a -> Cofree f a -> a
      trit(interpret) = +1 + (-1) = 0 ✓
```

### Pattern Runs on Matter:

```
Free f a  ─────runs-on─────→  Cofree f a
  (+1)                           (-1)
Program                      Environment
Syntax                       Semantics
                   ↓
              Result (0)
```

---

## Rule 6: Cofree Comonad (Semantic Context)

**Trit Assignment**: -1 (MINUS)

```haskell
data Cofree f a = a :< f (Cofree f a)
-- Head (extract) :< Tail (extend)
```

### GF(3) Rules for Cofree:

```
R6.1: Cofree observes/consumes
      trit(Cofree) = -1  -- Extractive/semantic

R6.2: Extract is observation
      extract :: Cofree f a -> a
      trit(extract) = -1  -- Pure extraction

R6.3: Duplicate creates observation context
      duplicate :: Cofree f a -> Cofree f (Cofree f a)
      trit(duplicate) = -1 (same, just restructured)

R6.4: Cofree interprets Free
      When Free f (+1) runs on Cofree f (-1), result is (0)
```

### Infinite Observer Stream:

```ruby
# Cofree as infinite observation context
class Cofree
  attr_reader :head, :tail, :trit
  
  def initialize(seed, functor)
    @head = color_at(seed, 0)        # Current observation
    @tail = -> { Cofree.new(splitmix64(seed), functor) }  # Lazy tail
    @trit = -1                        # Always -1 (observer)
  end
  
  def extract
    @head
  end
  
  def extend(&f)
    Cofree.new(@head, -> { @tail.call.extend(&f) })
  end
end
```

---

## Rule 7: Store Comonad (Focused Context)

**Trit Assignment**: -1 (MINUS)

```haskell
data Store s a = Store (s -> a) s
-- (lookup function, current position)
```

### GF(3) Rules for Store:

```
R7.1: Store observes from position
      trit(Store) = -1  -- Contextual observation

R7.2: pos extracts focus
      pos :: Store s a -> s
      trit(pos) = 0  -- Just returns position

R7.3: peek observes at position
      peek :: s -> Store s a -> a
      trit(peek) = -1  -- Observation operation

R7.4: seek moves focus
      seek :: s -> Store s a -> Store s a
      trit(seek) = 0  -- Neutral movement
```

### World-Position Observation:

```julia
# Store for world-state observation
struct Store{S,A}
    lookup::Function  # S -> A
    pos::S            # Current focus
    trit::Int         # -1 (observer)
end

function extract(s::Store)
    s.lookup(s.pos)
end

function extend(f, s::Store)
    Store(
        pos′ -> f(Store(s.lookup, pos′, s.trit)),
        s.pos,
        s.trit
    )
end
```

---

## Rule 8: Reader Monad (Environment Access)

**Trit Assignment**: 0 (ERGODIC)

```haskell
newtype Reader r a = Reader { runReader :: r -> a }
```

### GF(3) Rules for Reader:

```
R8.1: Reader transports environment
      trit(Reader) = 0  -- Pure transport, no generation/extraction

R8.2: ask is neutral observation
      ask :: Reader r r
      trit(ask) = 0

R8.3: local modifies neutrally
      local :: (r -> r) -> Reader r a -> Reader r a
      trit(local) = 0

R8.4: Reader composes neutrally
      Reader ⊗ M = M  -- No trit contribution
```

---

## Rule 9: Writer Monad (Output Accumulation)

**Trit Assignment**: +1 (PLUS)

```haskell
newtype Writer w a = Writer { runWriter :: (a, w) }
```

### GF(3) Rules for Writer:

```
R9.1: Writer generates output
      trit(Writer) = +1  -- Productive accumulation

R9.2: tell adds to log
      tell :: w -> Writer w ()
      trit(tell) = +1  -- Generation

R9.3: listen observes without consuming
      listen :: Writer w a -> Writer w (a, w)
      trit(listen) = 0  -- Just restructures

R9.4: Writer needs Reader to balance
      Writer (+1) ⊗ Reader (0) ⊗ Observer (-1) = 0 ✓
```

---

## Rule 10: State Monad (Bidirectional Transformation)

**Trit Assignment**: Composite (can be any, depends on operation)

```haskell
newtype State s a = State { runState :: s -> (a, s) }
```

### GF(3) Rules for State:

```
R10.1: get is observation
       get :: State s s
       trit(get) = -1  -- Extracts state

R10.2: put is generation
       put :: s -> State s ()
       trit(put) = +1  -- Produces new state

R10.3: modify is neutral
       modify :: (s -> s) -> State s ()
       trit(modify) = 0  -- Transforms without net change

R10.4: Balanced state operations
       get >> put x >> modify f: trit = -1 + 1 + 0 = 0 ✓
```

### Unworld State Threading:

```ruby
# State threading with GF(3) tracking
class UnworldState
  def initialize(seed)
    @seed = seed
    @trit_accumulator = 0
  end
  
  def get
    @trit_accumulator -= 1  # Observation
    @seed
  end
  
  def put(new_seed)
    @trit_accumulator += 1  # Generation
    @seed = new_seed
  end
  
  def modify(&f)
    # trit += 0 (neutral)
    @seed = f.call(@seed)
  end
  
  def conserved?
    @trit_accumulator % 3 == 0
  end
end
```

---

## Rule 11: Continuation Monad (Control Flow)

**Trit Assignment**: 0 (ERGODIC) - pure control, no data effect

```haskell
newtype Cont r a = Cont { runCont :: (a -> r) -> r }
```

### GF(3) Rules for Cont:

```
R11.1: Cont is pure control
       trit(Cont) = 0  -- No data generation/extraction

R11.2: callCC is control inversion
       callCC :: ((a -> Cont r b) -> Cont r a) -> Cont r a
       trit(callCC) = 0  -- Control only

R11.3: shift/reset are neutral
       Control flow changes don't affect trit balance
```

---

## Rule 12: List Monad (Nondeterminism)

**Trit Assignment**: Variable based on length mod 3

```haskell
instance Monad [] where
  return x = [x]
  xs >>= f = concatMap f xs
```

### GF(3) Rules for List:

```
R12.1: List length determines trit
       trit([a,b,c]) = length mod 3 = 0
       trit([a,b]) = 2 ≡ -1 (mod 3)
       trit([a]) = 1 ≡ +1 (mod 3)

R12.2: Empty list is -1
       trit([]) = -1  -- Failure/extraction

R12.3: concat preserves trit sum
       trit(xs ++ ys) = (trit(xs) + trit(ys)) mod 3

R12.4: Balanced lists have length 3n
       [a,b,c,d,e,f] has trit = 0 ✓
```

---

## Rule 13: Identity Comonad

**Trit Assignment**: 0 (ERGODIC)

```haskell
newtype Identity a = Identity { runIdentity :: a }

instance Comonad Identity where
  extract (Identity a) = a
  extend f w = Identity (f w)
```

### GF(3) Rules:

```
R13.1: Identity is transparent
       trit(Identity) = 0  -- Pure wrapper

R13.2: Identity ⊗ W = W for any comonad W
```

---

## Rule 14: Env Comonad (Tagged Context)

**Trit Assignment**: -1 (MINUS)

```haskell
data Env e a = Env e a

instance Comonad (Env e) where
  extract (Env _ a) = a
  extend f w@(Env e _) = Env e (f w)
```

### GF(3) Rules:

```
R14.1: Env carries context for observation
       trit(Env) = -1

R14.2: ask extracts environment
       ask :: Env e a -> e
       trit(ask) = -1

R14.3: Env is dual to Reader
       Reader (+ask → 0) ↔ Env (-ask → -1)
```

---

## Rule 15: Traced Comonad (Accumulated History)

**Trit Assignment**: -1 (MINUS)

```haskell
data Traced m a = Traced (m -> a)

instance Monoid m => Comonad (Traced m) where
  extract (Traced f) = f mempty
  extend g (Traced f) = Traced $ \m -> g (Traced $ \m' -> f (m <> m'))
```

### GF(3) Rules:

```
R15.1: Traced observes history
       trit(Traced) = -1  -- Historical observation

R15.2: trace adds to history
       trace :: m -> Traced m a -> a
       trit(trace) = -1  -- Observation via trace

R15.3: Dual to Writer
       Writer (+1, produces log) ↔ Traced (-1, observes history)
```

---

## Composition Rules (Meta-Rules)

### M1: Monad Transformer Stacking

```
trit(MT₁(MT₂(...(MTₙ(M))...))) = Σᵢ trit(MTᵢ) + trit(M)

For GF(3) conservation:
  Σ trit(stack) ≡ 0 (mod 3)
```

### M2: Adjunction Balance

```
If F ⊣ G (F left adjoint to G), then:
  trit(F) + trit(G) = 0
  
Examples:
  Free ⊣ Forgetful:  +1 + (-1) = 0 ✓
  Cofree ⊣ Forget:   -1 + (+1) = 0 ✓
```

### M3: Kan Extension Transport

```
Lan_K F has trit 0 (ergodic transport)
Ran_K F has trit 0 (ergodic transport)

Kan extensions are neutral transporters between categories.
```

### M4: Dialectica Decomposition

```
A ⊢ B becomes ∃x.∀y.R(x,y)

trit(∃) = +1 (existential witness generation)
trit(∀) = -1 (universal challenge observation)
trit(R) = 0  (atomic check)

Total: +1 + (-1) + 0 = 0 ✓
```

---

## World Hopping with Monads/Comonads

### W1: World as State Monad

```haskell
type World s = State s

hop :: World s a -> Event -> World s a
hop w event = do
  current <- get
  let new_seed = xor current.seed (hash event)
  put (world_from_seed new_seed)
  w
```

### W2: World Observation as Store Comonad

```haskell
type WorldObserver = Store Seed

observe :: WorldObserver Color
observe = Store color_at current_seed
```

### W3: Unworld Derivation as Free + Cofree

```
Derivation = Free DerivationF Seed      -- Syntax of derivation
Matter     = Cofree DerivationF Color   -- Semantics of color

run_derivation :: Derivation -> Matter -> [Color]
run_derivation program environment = 
  -- Free runs on Cofree
  -- +1 runs on -1 = 0 (conserved)
```

---

## Integration with Skills

| Skill | Monad/Comonad | Trit |
|-------|---------------|------|
| free-monad-gen | Free | +1 |
| temporal-coalgebra | Cofree | -1 |
| kan-extensions | (transport) | 0 |
| unworld | State + Free | +1 |
| dialectica | Cont + Reader | 0 |
| gay-mcp | IO (color gen) | +1 |
| bisimulation-game | Store | -1 |
| world-hopping | State | ±1 |

### Valid Triads:

```
free-monad-gen (+1) ⊗ kan-extensions (0) ⊗ temporal-coalgebra (-1) = 0 ✓
unworld (+1) ⊗ dialectica (0) ⊗ bisimulation-game (-1) = 0 ✓
gay-mcp (+1) ⊗ world-hopping (0*) ⊗ temporal-coalgebra (-1) = 0 ✓
```

---

## Implementation Checklist

- [ ] Every `>>=` call checks trit conservation
- [ ] Every `extend` call checks trit conservation
- [ ] Monad transformer stacks sum to 0 (mod 3)
- [ ] Free/Cofree pairs are used together
- [ ] IO actions come in groups of 3n
- [ ] State operations balance get/put
- [ ] List operations target length 3n

---

## References

- Uustalu & Vene, "The Essence of Dataflow Programming"
- Kmett, "Free Monads for Less"
- de Paiva, "Dialectica Categories"
- Spivak, "Poly: An abundant categorical setting"
- Riehl, "Categorical Homotopy Theory" (Kan extensions)
