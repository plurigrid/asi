# AGENTS.md - QuickCheck↔Autopoiesis + Anoma Solver Bootstrap

## Immediate Context
```
Seed: 1069
Palette[3]: #1316BB (cold, trit=-1)
DuckDB: dendroidal.duckdb (10 rows, GF(3) CONSERVED)
Anoma: 5,900 LOC, 92.3% threat mitigation, TESTNET READY
```

## Active Threads (amp threads)
```
T-019b5df7 QuickCheck autopoiesis    T-019b5ddc Nickel REPL (102 msgs)
T-019b5df0 GF(3) open games          T-019b5dd1 RAMAN spectral
T-019b5dea Property-based fuzzing    T-019b5dc4 Color port interfaces
T-019b5de3 Plurigrid skill sampling  T-019b5db5 Mutually reinforcing
```

## Commands
```bash
# Activate environment
cd ~/iii && flox activate

# Gay MCP (if available)
# gay_seed 1069 → deterministic colors

# Run practice
julia --project=@Gay -e 'using Gay; seed!(1069); println(color_at(3))'
```

## QuickCheck Generator Pattern
```julia
function autopoietic_gen(seed, depth)
    rng = SplitMix64(seed)
    trit = mod(next!(rng), 3) - 1
    depth == 0 || trit == -1 ? Leaf(color_at(seed)) :
        Node(trit, autopoietic_gen(split(rng)[1], depth-1),
                   autopoietic_gen(split(rng)[2], depth-1))
end
```

## Reafference Test
```python
def test_reafference(seed, idx):
    predicted = color_at(seed, idx)
    observed = color_at(seed, idx)  # same seed = same color
    assert predicted == observed, "Exafference: external attack!"
```

## GF(3) Conservation Check
```python
def verify_gf3(trits): 
    return sum(trits) % 3 == 0
```

## Skills to Load
1. `cybernetic-immune` - Self/Non-Self discrimination
2. `bisimulation-game` - Attacker/Defender/Arbiter
3. `topos-adhesive-rewriting` - Shrinking as ∼Q_G
4. `narya-proofs` - 4 verifiers

## DuckDB Target
```sql
CREATE TABLE dendroidal (
    seed UBIGINT, idx INT, hex VARCHAR(7),
    hue FLOAT, trit TINYINT, depth INT,
    parent_seed UBIGINT, PRIMARY KEY (seed, idx)
);
```

## References
- Varela: Principles of Biological Autonomy (1979)
- Powers: Behavior: The Control of Perception (1973)
- Kris Brown: Incremental Query Updating in Adhesive Categories
- bmorphism gists: Fix.idr, itt-coc.ts, abstractlattice.jl

## Anoma Solver Testnet
```bash
bb demonstrate-framework.bb          # 9-stage demo
bb multi-solver-tournament.bb        # 3-solver privacy
bb threat-model-analyzer.bb          # 92.3% mitigation
docker-compose up -d                 # Local stack
```

## Bridge: Juvix → narya-proofs
- solverStrategyPrivacyUnderTEE theorem
- Queue consistency via diagram commutativity
- GF(3) conservation across settlement

