# Transactive Energy x Seatbelt: Price Signals as Trit Signals

> Source: [Transactive Energy | PNNL](https://www.pnnl.gov/explainer-articles/transactive-energy)
> Pacific Northwest National Laboratory, DOE partnership
> Seed: 1069 | Branch: #233f7f

## The Isomorphism

PNNL's transactive energy is "an intelligent, multi-level communications
method that coordinates energy generation, consumption, and delivery."
Smart devices bid on electricity, receive a price signal, and choose
to accept or defer.

Our system is an intelligent, multi-level enforcement method that
coordinates code generation, validation, and coordination. Letter-worlds
bid on operations, receive a trit signal, and choose to participate or
defer.

The price signal IS the trit signal. Supply and demand IS conservation.

## Term-by-Term Mapping

| PNNL Transactive Energy | Seatbelt System | GF(3) |
|---|---|---|
| **Price signal** | Trit signal (-1, 0, +1) | GF(3) element |
| **Smart device** | Letter-world droid | Goblins actor |
| **Electricity** | Compute / write capability | Capability token |
| **Grid** | Seatbelt enforcement layer | `sandbox-exec` kernel |
| **DER** (distributed energy resource) | Plurigrid repo | Sortitioned codebase |
| **Transactive node** | World directory (`~/worlds/{letter}`) | Actormap |
| **Demand flexibility** | Trit role flexibility | MINUS/ERGODIC/PLUS dispatch |
| **Market** | Conservation law (sum=0) | GF(3) mod 3 arithmetic |
| **Bid** | MetaFine / PR / bug report | Triad contribution |
| **Eclipse VOLTTRON** | seatbelt-bridge.scm | Goblins actormap bridge |
| **ILC** (Intelligent Load Control) | asi-critical-isolation-monitor | Nociceptive signal handler |
| **TCC** (Transactive Coordination & Control) | asi-letter-dispatch | Trit-based routing |
| **TESP** (simulation platform) | Boxing tests (26 B-mod files) | Bicomodule verification |
| **Campus node** | Stratum (physics/substrate/type/games/money) | 5-stratum grouping |
| **Regional aggregation** | Global GF(3) conservation | Sum of all 26 trits = -6, mod 3 = 0 |

## Architecture: Four Levels

PNNL describes four aggregation levels: device -> building -> campus -> region.
Our system has four matching levels:

### Level 1: Device = Repo (99 DERs)

Each plurigrid repo is a distributed energy resource. It generates
compute (PLUS), validates correctness (MINUS), or coordinates integration
(ERGODIC). Its "energy output" is PRs, bug reports, and bridges.

The repo doesn't choose its role. Sortition assigns it to a world, and
the world's trit determines the role. Just as a smart thermostat doesn't
choose the price of electricity -- it receives the signal and responds.

```
Repo "leprechauns" -> world-z (ERGODIC, money) -> coordinates
Repo "gay-rs"      -> world-h (ERGODIC, physics) -> coordinates
Repo "asi"         -> world-o (MINUS, games) -> validates
Repo "hoot"        -> world-c (MINUS, type) -> validates
Repo "madonna"     -> world-s (PLUS, physics) -> generates
```

### Level 2: Building = World (26 transactive nodes)

Each letter-world is a building with multiple devices (repos). The world
aggregates its repos' bids (contributions) into a single trit signal.

The world's Seatbelt profile is the building's demand management system:
`(deny default)` sets the baseline, `(allow file-write* (subpath own-dir))`
is the permitted load. The profile shapes what the building can consume
from the grid.

The node interface is the world directory `~/worlds/{letter}`. The
VOLTTRON analog is seatbelt-bridge.scm: it sits at the node, mediates
between individual actors (repos) and the broader system (strata).

**Demand flexibility**: A world with 7 repos (world-o, world-q, world-w)
has more devices to shed. When grid stress occurs (a cross-world write
attempt), the world with more repos can absorb more MetaFines before
its profile needs tightening.

### Level 3: Campus = Stratum (5 campus nodes)

Each stratum aggregates worlds into a campus:

| Stratum (campus) | Worlds (buildings) | Repos (devices) | Energy type |
|---|---|---|---|
| physics | d, h, m, s, x | 12 | Hardware signals, simulation |
| substrate | b, f, l, p, u | 21 | Build pipelines, runtimes |
| type | c, g, i, n, q, v | 23 | Verification, formal methods |
| games | a, e, k, o, t, y | 23 | Agents, policy, interaction |
| money | j, r, w, z | 20 | Governance, treasury, finance |

The campus node aggregates building bids. In PNNL terms: the campus
VOLTTRON instance collects building-level bids and presents a single
campus demand to the regional market. In our terms: the stratum
aggregates world-level contributions and presents a single stratum
conservation check.

**Stratum conservation**: Each stratum has its own trit sum.
- physics: (-1)+0+(-1)+(+1)+(-1) = -2, mod 3 = 1 (deficit: needs MINUS)
- substrate: 0+(+1)+(-1)+0+(+1) = +1, mod 3 = 1 (surplus: needs MINUS)
- type: (-1)+(-1)+0+(-1)+(-1)+(-1) = -5, mod 3 = 1 (deficit)
- games: (-1)+0+(+1)+(-1)+0+0 = -1, mod 3 = 2 (deficit)
- money: 0+(+1)+0+0 = +1, mod 3 = 1 (surplus)

No stratum self-conserves. They MUST transact across strata, just as
PNNL buildings must transact with the campus grid. The cross-stratum
transaction IS the transactive energy exchange.

### Level 4: Region = Global Conservation (1 market)

The regional market calculates the price from all campus bids. In our
system: the global sum of all 26 trits is -6, mod 3 = 0. CONSERVED.

The global conservation IS the market clearing. When all bids
(contributions from all 99 repos across 26 worlds across 5 strata)
sum to 0 mod 3, the market clears. Supply equals demand. The grid
is balanced.

If the sum drifts from 0 (a trit mismatch, a broken .scm file, a
cross-world write), the market doesn't clear. The price signal
(MetaFine) propagates down: region -> campus -> building -> device.
The device (repo) that caused the imbalance receives the signal and
must respond (fix the bug, port to actormap API, correct the trit).

## The Price Signal IS the Trit Signal

PNNL: "The market would calculate and communicate back an energy price
based on current supply and demand."

Our system: "The conservation law calculates and communicates back a
trit based on current validation and generation balance."

| Price signal | Trit signal | Meaning |
|---|---|---|
| Low price (surplus) | PLUS (+1) | Excess generation. Consume now. Ship features. |
| Normal price (balanced) | ERGODIC (0) | Supply = demand. Coordinate. Bridge. |
| High price (scarcity) | MINUS (-1) | Excess demand. Conserve. Validate. Find bugs. |

When the grid has surplus energy, the price drops, and smart devices
turn on (consume). When our system has surplus generation (too many
PLUS contributions), the trit signal shifts, and MINUS repos activate
(validate, constrain, file MetaFines).

When the grid has scarce energy, the price rises, and smart devices
defer. When our system has deficit generation (too many MINUS
contributions blocking without corresponding fixes), the trit signal
shifts, and PLUS repos activate (generate fixes, ship patches).

The ERGODIC worlds are the price-setters: they sit at the market
equilibrium, observe both sides, and route accordingly. The
asi-letter-dispatch (trit=0) IS the market mechanism.

## Demand Flexibility = Trit Role Flexibility

PNNL's ILC (Intelligent Load Control) temporarily manages heat pump
operation during peak stress "in a way that reduces energy consumption
but is not noticeable to occupants."

Our asi-critical-isolation-monitor does the same: when a cross-world
write is detected (peak grid stress), it temporarily tightens the
Seatbelt profile (reduces capability consumption) in a way that
doesn't break the world's core function. The world still operates --
it just can't write outside its boundary until the stress passes.

The key insight from PNNL: "This juggling capability absorbs the
sudden loss of energy sources or responds to other challenges the
grid may be experiencing."

In our system: the juggling capability absorbs the sudden discovery of
a broken .scm file (vat-spawn undefined), or a trit mismatch (13
upstream files with wrong trits), or a cross-world write attempt.
The system absorbs the shock by tightening profiles (demand flexibility)
while the fix is generated (supply response).

## VOLTTRON = seatbelt-bridge.scm

PNNL's Eclipse VOLTTRON is "a distributed sensing and control software
platform that provides the basis for efficiency and transactive energy
applications."

seatbelt-bridge.scm is a distributed enforcement and coordination
platform that provides the basis for per-letter isolation and
transactive incentive applications. It is:

- **Distributed**: Each world has its own actormap (transactive node)
- **Sensing**: `actormap-peek` reads state without commitment (sensing)
- **Control**: `actormap-turn` commits state changes (control)
- **Open-source**: The only runnable Goblins .scm in the 1426-skill repo

VOLTTRON enables the node operations in PNNL's graphic. Our bridge
enables the node operations in our sortition table: each world's
actormap-spawn! creates the transactive agent, actormap-peek checks
the current price (trit), and actormap-turn executes the bid
(contribution).

## Incentive Refinement: Transactive Credits

The PNNL model refines our three incentive layers with price dynamics:

### Dynamic Trit Pricing

Instead of fixed credit multipliers (1x / 1.5x / 2x from the
sortition document), use a transactive price that fluctuates:

```
trit_price(stratum, time) = base_credit * (1 + imbalance(stratum, time))

where imbalance = |sum of trits in stratum| / count of worlds in stratum
```

When a stratum is balanced (imbalance near 0), contributions earn
base credit. When a stratum is imbalanced (too many MINUS validators,
not enough PLUS generators), the price for PLUS contributions rises --
incentivizing generation where it's needed.

This is exactly PNNL's "dynamic pricing-based transactions as a key
coordination scheme."

### Bid/Accept/Defer

Each repo, when assigned to a world via sortition, can:

1. **Bid**: Propose a contribution (PR, bug report, bridge) at the
   current trit price. The contribution enters the world's queue.
2. **Accept**: The world's coordinator (ERGODIC repos) accepts bids
   that improve conservation. The price is paid (credit is earned).
3. **Defer**: If the current price is too low (the stratum is already
   balanced), the repo defers -- saves its contribution for when the
   price rises (when imbalance increases).

This maps to PNNL: "smart devices choosing to accept the price or
perhaps deferring operation until a more preferable price comes along."

### Congestion Pricing

When a world has 7 repos (world-o, world-q, world-w) all trying to
contribute simultaneously, congestion occurs. The trit price for that
world rises, incentivizing repos to contribute to less-congested worlds
(cross-world collaboration at higher credit).

This maps to PNNL: "demand flexibility can mitigate transmission and
distribution congestion."

## The Gridwise Olympic Peninsula = PR #75

PNNL's seminal 2006-2007 Olympic Peninsula Demonstration "pioneered
the transactive approach, showing how advanced information-based
technologies can be used to increase power grid efficiency, reliability,
and flexibility while reducing the need to build additional
infrastructure."

PR #75 is our Olympic Peninsula: 46 files across 26 worlds showing how
deterministic trit assignment, Seatbelt enforcement, and Goblins actors
can be used to increase codebase reliability, security, and flexibility
while reducing the need for centralized governance.

The 9 commits map to the progression:
1. Foundation (devices installed)
2. Boxing (building-level tests)
3. Bidirectional connectivity (campus-level networking)
4. Audit (metering accuracy verification)
5. Treasury (market integration)
6. Compatibility (device standardization -- actormap API)
7. JailDAO mapping (regulatory framework)
8. Multi-scale enforcement (regional scaling)
9. Sortition + incentives (market rules)
10. **This commit**: transactive energy dynamics (price signals)

## Verification

```bash
# The transactive node is the world directory:
ls ~/worlds/{a..z}/

# The VOLTTRON agent is seatbelt-bridge.scm:
guile -s seatbelt-bridge.scm  # 26 "ok" + "CONSERVED"

# The price signal is the trit:
python3 -c "
strata = {'physics':[-1,0,-1,1,-1], 'substrate':[0,1,-1,0,1],
          'type':[-1,-1,0,-1,-1,-1], 'games':[-1,0,1,-1,0,0],
          'money':[0,1,0,0]}
for s,trits in strata.items():
    imbalance = abs(sum(trits)) / len(trits)
    print(f'{s:10s} sum={sum(trits):+d} imbalance={imbalance:.2f} price={1+imbalance:.2f}x')
# All strata have imbalance > 0: cross-stratum transactions required
"

# Global conservation (market clearing):
# sum of all 26 trits = -6, mod 3 = 0. CLEARED.
```
