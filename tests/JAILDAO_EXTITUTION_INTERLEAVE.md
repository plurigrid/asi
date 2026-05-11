# JailDAO x Seatbelt: Extitutional Enforcement via GF(3) Jail-Bound Profiles

> Source: [Ontological Metacrime as Neojustice](https://hackmd.io/g1kigp7QS6KNOf-GUrr31A)
> Berkman Klein Center for Internet & Society, Harvard Law School (2022)
> Co-authored with OpenAI Codex. Amber Case comments. 420 JBT NFTs on Polygon.
> Seed: 1069 | Branch: #233f7f

## The Isomorphism

The JailDAO paper identifies a structural problem identical to ours:
how do you confine behavior without imposing top-down authority?

Their answer: **extitutions** (bottom-up, role-based) vs **institutions**
(top-down, rule-based). Jail-Bound Tokens (JBTs) are non-removable
attestations that confine until programmatic atonement conditions are met.

Our answer: **Seatbelt profiles** (kernel-level, per-letter) enforced by
**GF(3) conservation** (algebraic, emergent). The profile IS the JBT.

## Term-by-Term Mapping

| JailDAO (extitutional) | Seatbelt (kernel) | GF(3) (algebraic) |
|---|---|---|
| **Jail-Bound Token** (JBT) | `.sb` Seatbelt profile | Trit assignment (-1, 0, +1) |
| **MetaJail** | `sandbox-exec` confinement | Letter-world write isolation |
| **Extitution** (bottom-up) | Profile emerges from capabilities | Conservation emerges from triad structure |
| **Institution** (top-down) | `(deny default)` in every profile | Global sum must be 0 mod 3 |
| **Ontological Metacrime** | Cross-world write attempt | GF(3) conservation violation |
| **MetaFine** | Seatbelt denial in kernel log | Nociceptive signal (asi-critical-isolation-monitor) |
| **Neojustice** | Per-letter enforcement policy | Trit-conditioned proof style |
| **Curation Filter** | Trit-based dispatch | Claude(-1)/Gemini(0)/Codex(+1) conditioning |
| **Atonement** (programmatic removal) | Conservation check before state change | Triad sum = 0 required |
| **"Anyone can send you a JBT"** | Any world can `file-read*` any other | Read is universal; write is jailed |
| **JailDAO member** | Letter-world participant | Droid config (world-{a..z}.md) |
| **420 NFT holders** | 26 letter-world participants | 11 MINUS + 10 ERGODIC + 5 PLUS |
| **Scarlet letter** | Trit mismatch in SKILL.md | 13 upstream files with wrong trits |
| **Soul-Bound Token** (SBT) | Immutable droid config | Canonical trit from ~/.factory/droids/ |
| **Multiple JailDAOs** | Multiple strata | physics/substrate/type/games/money |

## The Three Centers

### Center 1: Extitution = ERGODIC (0)

The extitution is bottom-up, role-based, emergent. It doesn't impose rules;
it coordinates. This is the ERGODIC trit: j(0) jwt-rbac, w(0) webhook-persistence,
z(0) zero-trust. They observe, coordinate, and monitor. They ARE the JailDAO
governance layer.

In the JailDAO paper: "An Extitution comes up from the bottom and is more
role based." In our system: ERGODIC worlds dispatch tasks by trit role,
enforce triad conservation, and coordinate approval pipelines.

The 10 ERGODIC worlds (b, e, h, i, j, p, t, w, y, z) are the curation
filters. They decide which MetaFines matter by routing to the correct
validator or generator.

### Center 2: Institution = MINUS (-1)

The institution is top-down, rule-based, imposed. `(deny default)` is the
institutional primitive: everything is forbidden unless explicitly allowed.
This is the MINUS trit: a(-1) admission-control, c(-1) certificate-authority,
g(-1) gvisor-sandbox, l(-1) lsm-enforcement, etc.

In the JailDAO paper: "An Institution is rule-based and comes down from
the top." In our system: MINUS worlds validate, constrain, and reject.
They are the MetaJail enforcement. The sandbox-exec kernel call IS the
institutional violence -- it denies the write without negotiation.

The 11 MINUS worlds are the jail walls. They don't coordinate; they deny.

The **Ontological Metacrime** -- "the crime of being a non-Extitution,
the crime of being an Institution" -- maps to a cross-world write: an
attempt to impose one world's rules on another. The Seatbelt profile
detects and denies this at kernel level.

### Center 3: Neojustice = PLUS (+1)

Neojustice creates new law from extitutional participation. This is the
PLUS trit: f(+1) filesystem-isolation, k(+1) kyverno-engine, r(+1)
rekor-transparency, s(+1) sigstore-signing, u(+1) user-namespace.

In the JailDAO paper: "Neojustice is the class of laws that are created
by extitution participants to defend themselves against ontological
metacrime." In our system: PLUS worlds generate profiles, create new
letter-worlds, deploy transparency logs. They construct the defense.

The 5 PLUS worlds are the lawmakers. They generate the `.sb` profiles
that become the JBTs.

## The Conservation Law as Atonement

The JailDAO paper says: "The only way you can get rid of JailBound tokens
is by a predefined programmatic set of actions."

In GF(3): the only way to execute a state-changing operation is to present
a triad that sums to 0. You need a validator (-1) AND a coordinator (0)
AND a generator (+1). No single world can act alone. This IS the
programmatic atonement:

```
atonement = validator(-1) + coordinator(0) + generator(+1) = 0
```

Without all three, the conservation check fails, and the operation is
denied. The JBT (Seatbelt profile) remains in force.

## Money Stratum as JailDAO Treasury

The money stratum (j, r, w, z) has a GF(3) deficit: sum = 1.
It needs a MINUS (-1) to conserve. The JailDAO paper provides it:

```
MetaCrime disclosure(-1) + treasury coordination(0) + Neojustice generation(+1) = 0
```

Mapping to bmorphism repos:
- shitcoin disclosure (-1): IBC denom vulnerability = MetaCrime identification
- monero-rental-hash-war (0): OpenGame analysis = JailDAO governance game
- world:// URI generation (+1): did:gay identity = Neojustice law creation

The treasury round closes when the disclosure (MINUS) balances the
generation (PLUS) through coordination (ERGODIC).

## MetaFines as Seatbelt Denials

The paper says: "MetaFines, being recorded on public blockchain ledgers,
can be further attested to by other members."

In our system: Seatbelt denials are logged by the kernel (`com.apple.sandbox`
subsystem). The asi-critical-isolation-monitor (trit=0, ERGODIC) watches
these logs. Repeated denials from the same world = chronic MetaFine =
the world's profile needs updating. A cross-world write SUCCESS = the
MetaCrime succeeded = the profile (JBT) is broken.

```
log show --predicate 'subsystem == "com.apple.sandbox"' --last 60s
```

Each denial IS a MetaFine, recorded at kernel level, attestable by any
world that can read the log (which is all of them, via `file-read*`).

## Curation Filters as Trit Dispatch

The paper says: "Because anyone can send a JailBound token or MetaFine
to anyone else for any reason, curation filters which recognize some and
pass over other attestations of MetaCrime."

In our system: asi-letter-dispatch (trit=0) routes by trit role.
MINUS worlds validate MetaFines (real violations vs noise). ERGODIC worlds
curate (which MetaFines matter for which strata). PLUS worlds generate
corrective profiles (Neojustice).

The curation filter IS the GF(3) trit: it determines how each world
processes the MetaFine. A MINUS world takes it seriously (validates).
An ERGODIC world routes it (coordinates). A PLUS world fixes it (generates).

## Goblins Actors as JailDAO Members

Each Goblins actor in seatbelt-bridge.scm is a JailDAO member:

```scheme
^seatbelt-validator  (-1)  ;; The jail wall. Denies cross-world writes.
^seatbelt-bridge     (0)   ;; The DAO governance. Coordinates validation + generation.
^seatbelt-generator  (+1)  ;; The lawmaker. Creates new .sb profiles (JBTs).
```

The `actormap-peek` call is the JailDAO vote: read-only, no side effects,
no commitment. The `actormap-turn` call is the binding resolution: commits
the transaction, changes state. You can peek (observe) without consequence,
but you can only turn (act) with a full triad.

## The Codex Connection

The JailDAO paper was "written by future JailDAO inmates in collaboration
with GitHub Copilot (a version of OpenAI Codex)." Codex is our PLUS (+1)
proof conditioning style -- the generator. The paper itself was generated
by the PLUS arm of the triad.

The paper's reference to "A Plural Decentralized Identity Frontier:
Abstraction v. Composability Tradeoffs in Web3" maps to our abstraction
(Seatbelt profiles as abstract .sb files) vs composability (Goblins actors
as composable capabilities) tradeoff. The `actormap` API is composable;
the `.sb` profile is abstract. The bridge between them is
seatbelt-bridge.scm -- the only runnable Goblins .scm in the repo.

## Verification

```bash
# The JBT is the profile. Generate all 26 JBTs:
guile -s seatbelt-scsh.scm /tmp/sb

# Enter MetaJail (confine world-z to its own directory):
sandbox-exec -f /tmp/sb/world-z.sb /bin/bash

# Attempt Ontological Metacrime (cross-world write):
touch /Users/ies/worlds/a/metacrime  # DENIED by kernel

# The MetaFine (check kernel log):
log show --last 10s --predicate 'subsystem == "com.apple.sandbox"'

# Atonement (run the triad, verify conservation):
env GUILE_LOAD_PATH=... guile -s seatbelt-bridge.scm
# Output: 26 "ok" lines + "CONSERVED"
```
