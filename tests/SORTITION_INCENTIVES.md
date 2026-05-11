# Sortition Incentives: Plurigrid Repos into Letter-Worlds

> Sortition: deterministic assignment via SplitMix64(seed=1069 XOR SHA256(repo_name)) mod 26
> 99 repos -> 26 worlds, all populated, max 7 repos per world (world-o)

## The Sortition Table

| World | Trit | Stratum | Repos | Count |
|---|---|---|---|---|
| a | -1 | games | RxInferClient.py, forest | 2 |
| b | 0 | substrate | notsoswift-evolution, duck-kanban, srfi-69, tree-sitter-wit, oni | 5 |
| c | -1 | type | causal, lmao, hoot, clopen-hypergraphs, ember | 5 |
| d | -1 | physics | digital_wra_data_standard | 1 |
| e | 0 | games | properadness, ripgrep | 2 |
| f | +1 | substrate | MolotovRibbentropKrylovKit.jl, paper-worlds, oterm | 3 |
| g | -1 | type | U-Void-Synthesizer, duckCloud, ies | 3 |
| h | 0 | physics | gay-rs, skillz, swe-rl | 3 |
| i | 0 | type | properon, scat | 2 |
| j | 0 | money | gemini-agent, magenc, inverso, bd3lms | 4 |
| k | +1 | games | agent-o-rama, acp.el, forester.el, babooka, base-mcp | 5 |
| l | -1 | substrate | UncutGem, oxcaml-lsp, DeepSeek-Prover-V2, csm, MindEyeV2 | 5 |
| m | -1 | physics | CatColab, IsUMap, clrs | 3 |
| n | -1 | type | kuzu-mcp-server | 1 |
| o | -1 | games | asi, zig-syrup, goblinshare, ArkhaiPufferEnv, agi-tools, oxcaml-playground, panda | 7 |
| p | 0 | substrate | shepherd, lazybjj, UnwiringDiagrams.jl, sprintathon | 4 |
| q | -1 | type | lazygay, ifl2025-liquidhaskell, llms-txt-hub, tree-sitter-julia, infinity-cosmos, paperproof, r1_diagram | 7 |
| r | +1 | money | graded-optic, ladyworm, catwalk | 3 |
| s | +1 | physics | madonna | 1 |
| t | 0 | games | formal-conjectures | 1 |
| u | +1 | substrate | aaif-landscape, saopaulo, flox-vscode, hevm-games | 4 |
| v | -1 | type | asi-skills, gay-tofu, windIO, wasi-testsuite, immobile-mcp | 5 |
| w | 0 | money | gay-terminal, gay-go, quizx, CGT4NN, ontology, dysts, mcp-golang | 7 |
| x | -1 | physics | awesome-neural-geometry, spritely-semantic-colors, Reference-FMUs, gpui-component | 4 |
| y | 0 | games | lolita, gay, Goedel-Prover-V2, lean-abc-true-almost-always, arbor, dollar | 6 |
| z | 0 | money | json-canvas, u-crane, leprechauns, froggo, underestimates, pepepedia | 6 |

## Why Sortition Works

Sortition is **not** curation. Nobody chose which repo goes where. The
assignment is deterministic from seed 1069 + repo name hash. This means:

1. **No politics**: You can't lobby for your repo to be in a favorable world
2. **Verifiable**: Anyone can recompute the assignment
3. **Stable**: Adding a new repo doesn't reshuffle existing assignments
4. **Balanced**: SplitMix64 is uniform -- repos distribute evenly

The sortition IS the extitution. It comes from below (the hash), not
from above (a committee).

## Incentive Structure: Three Layers

### Layer 1: JailDAO Confinement (the stick)

Each repo inherits its world's Seatbelt profile. A repo in world-o (-1, games)
gets `(deny default)` + `(allow file-write* (subpath ~/worlds/o))`. If
the repo tries to write outside its world, the kernel denies it.

**Incentive**: Fix your repo's issues so the Seatbelt profile can be relaxed.
The more compliant your repo, the broader your write permissions within the
world's scope.

The JBT is automatic: your repo lands in a world via sortition, and the
world's profile IS the JBT. You didn't opt in. But you can opt in to the
atonement (fixing issues) to get the profile relaxed.

### Layer 2: Trit Role (the structure)

Your repo's world determines your role:

- **MINUS (-1) repos** (44 repos across 11 worlds): You validate. Your
  incentive is to find bugs in repos in PLUS worlds and file issues.
  Each valid bug report is a MetaFine that earns your world reputation.

- **ERGODIC (0) repos** (36 repos across 10 worlds): You coordinate.
  Your incentive is to bridge MINUS and PLUS repos. Write adapters,
  glue code, integration tests. Each successful bridge earns your world
  coordination credit.

- **PLUS (+1) repos** (19 repos across 5 worlds): You generate. Your
  incentive is to ship features, fix bugs filed by MINUS repos, and
  produce artifacts that pass ERGODIC coordination. Each merged PR
  earns your world generation credit.

The triad must complete: a MINUS repo files a bug (-1), an ERGODIC repo
coordinates the fix (0), a PLUS repo ships the patch (+1). Sum = 0.
All three worlds earn credit.

### Layer 3: Stratum Affinity (the bonus)

Repos in the same stratum have natural affinity:

| Stratum | Worlds | Repos | Affinity bonus |
|---|---|---|---|
| physics | d, h, m, s, x | 12 repos | Hardware, simulation, signals |
| substrate | b, f, l, p, u | 21 repos | Build tools, runtimes, infra |
| type | c, g, i, n, q, v | 23 repos | Type theory, verification, identity |
| games | a, e, k, o, t, y | 23 repos | Agents, games, policy, UX |
| money | j, r, w, z | 20 repos | Finance, governance, treasury |

Cross-stratum collaboration (e.g., a type-stratum repo fixing a
money-stratum bug) earns extra credit because it crosses the
conservation boundary.

## Concrete Incentives

### For Individual Contributors

1. **PR to a repo in your world** = standard contribution
2. **PR to a repo in a different world, same stratum** = 1.5x credit
3. **PR to a repo in a different world, different stratum** = 2x credit
4. **Filing a valid bug across worlds (MINUS role)** = MetaFine credit
5. **Writing a bridge between worlds (ERGODIC role)** = coordination credit
6. **Shipping a fix for a cross-world bug (PLUS role)** = generation credit

### For Repos

1. **Zero open MetaFines** = world's Seatbelt profile is relaxed (broader write)
2. **Active in triad completions** = priority in asi skill catalog
3. **Cross-stratum collaboration** = featured in REVIEW_GUIDE.md
4. **All .scm files actually run** = gold star (currently only seatbelt-bridge.scm passes)

### For Worlds

1. **All repos in your world pass CI** = world-level conservation bonus
2. **Your world participates in triads with other worlds** = intertwiner credit
3. **Your world's boxing test passes** = Seatbelt profile verified at kernel level
4. **GF(3) conservation maintained** = the world stays in the ecosystem

## The JailDAO Optionality

Every repo has the choice:

**Opt in** (extitutional): Acknowledge your world assignment. Participate
in triads. File MetaFines against repos that break conservation. Earn
credit by fulfilling your trit role. The JBT (Seatbelt profile) relaxes
as you contribute.

**Ignore** (institutional): The sortition stands anyway. Your repo is
still in its world. The Seatbelt profile still confines it. Other repos
can still file MetaFines against yours. But you earn no credit.

**Contest** (neojustice): If you believe the sortition is wrong, you can
propose a re-sortition with a different seed. But you need a complete
triad (MINUS validator + ERGODIC coordinator + PLUS generator) to approve
the change. The conservation law doesn't bend for one repo.

## Verification

```bash
# Verify sortition is deterministic
python3 -c "
import hashlib
GOLDEN=0x9E3779B97F4A7C15; MIX1=0xBF58476D1CE4E5B9; MIX2=0x94D049BB133111EB; MASK=0xFFFFFFFFFFFFFFFF
def sm(s):
    s=(s+GOLDEN)&MASK; z=s; z=((z^(z>>30))*MIX1)&MASK; z=((z^(z>>27))*MIX2)&MASK; return z^(z>>31),s
def assign(repo, seed=1069):
    h=int(hashlib.sha256(repo.encode()).hexdigest()[:16],16)
    v,_=sm(seed^h); return chr(ord('a')+(v%26))
print(assign('asi'))  # should be 'o'
print(assign('leprechauns'))  # should be 'z'
print(assign('gay-rs'))  # should be 'h'
"
```
