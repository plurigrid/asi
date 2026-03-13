# JailDAO at Every Scale: Optionalities for Humans Who Made Bad Software

> "The Ontological Metacrime is the crime of being a non-Extitution."
> Applied: shipping bad software is the metacrime. The JBT is the confinement.
> Atonement is fixing it -- but you need the full triad to do so.

## The Principle

Bad software is an ontological metacrime: it imposes institutional damage
(crashes, vulnerabilities, data loss) on extitutional participants (users,
operators, downstream systems). The JailDAO optionality at every scale
means: at each level of the system, the author of bad software receives
a Jail-Bound Token (confinement) and a path to atonement (programmatic
removal via triad completion).

The key insight: **confinement is not punishment, it is containment**.
A sandboxed process isn't punished -- it's prevented from causing further
harm while the fix is developed. The JBT stays until the triad completes.

## Scale 1: Character (single function, single line)

**Bad software**: A function with an off-by-one error, an unchecked null,
a SQL injection surface.

**JBT**: The function is confined to a test harness. It cannot be called
from production until the fix lands.

**Triad**:
- MINUS(-1): Linter/type-checker flags the defect (validator)
- ERGODIC(0): CI pipeline holds the PR (coordinator)
- PLUS(+1): Developer writes the fix (generator)

**Atonement**: All three must complete. The linter must pass. The CI must
green. The fix must ship. Then the JBT (test-only confinement) is removed.

**Seatbelt analog**: `(deny process-exec)` on the function's compilation
unit until the fix is merged.

## Scale 2: Word (single module, single crate, single package)

**Bad software**: A library with a known CVE. A package with a dependency
that phones home. A module that leaks file descriptors.

**JBT**: The module is pinned to a known-good version. Upgrades are
confined to a staging environment.

**Triad**:
- MINUS(-1): CVE scanner identifies the vulnerability (v, vulnerability-scan)
- ERGODIC(0): Dependency manager holds the lock file (b, build-pipeline)
- PLUS(+1): Maintainer publishes the patched version (s, sigstore-signing)

**Atonement**: The CVE is patched, the lockfile is updated, the new version
is signed. The JBT (version pin) is released.

**Seatbelt analog**: `(allow file-read* (subpath "/nix/store/{known-good-hash}"))` --
only the content-addressed good version is readable.

## Scale 3: Sentence (single service, single API, single endpoint)

**Bad software**: An API endpoint that returns 500 under load. A service
that doesn't gracefully degrade. A webhook that retries forever.

**JBT**: The endpoint is rate-limited. The service is circuit-broken.
The webhook is dead-lettered.

**Triad**:
- MINUS(-1): Load test identifies the breaking point (d, device-access)
- ERGODIC(0): Circuit breaker coordinates failover (t, topology-mesh)
- PLUS(+1): SRE deploys the fix with canary rollout (f, filesystem-isolation)

**Atonement**: The load test passes at 2x previous breaking point. The
circuit breaker confirms recovery. The canary shows no regression.

**Seatbelt analog**: `(deny network* (remote tcp "*:8080"))` -- the
endpoint is network-jailed until the fix is deployed.

## Scale 4: Paragraph (single application, single binary)

**Bad software**: An application that corrupts user data on crash. A binary
that doesn't respect signals. A process that orphans children.

**JBT**: The application runs inside a sandbox profile. It can only write
to its own directory. Crash artifacts are captured.

**Triad**:
- MINUS(-1): Crash reporter validates the failure mode (g, gvisor-sandbox)
- ERGODIC(0): Process supervisor coordinates restart (p, pid-namespace)
- PLUS(+1): Developer ships crash-safe write path (u, user-namespace)

**Atonement**: The crash reporter shows zero data corruption. The supervisor
confirms clean restarts. The new write path is proven idempotent.

**Seatbelt analog**: This IS our per-letter Seatbelt profile. Each
application (world) gets `(deny default)` + `(allow file-write* (subpath own-dir))`.

## Scale 5: Page (single repository, single project)

**Bad software**: A repo with 13 files claiming wrong trits. A project
where none of the .scm files actually run. A codebase where the README
contradicts the implementation.

**JBT**: The repo is forked. Changes go through a PR with mandatory
review. The fork is the MetaJail -- you can only escape by getting
the PR merged.

**Triad**:
- MINUS(-1): Audit identifies 13 trit mismatches (asi-droid-skill-mixer)
- ERGODIC(0): PR review coordinates the fix (asi-sheaf-coordinator)
- PLUS(+1): Contributor submits corrected files (asi-profile-generator)

**Atonement**: All 13 mismatches fixed. All .scm files ported to working
actormap API. PR passes all 19 verification checks.

**Seatbelt analog**: This IS PR #75. The branch `233f7f-seatbelt-per-letter-isolation`
is the JBT. The PR review is the atonement process.

## Scale 6: Chapter (single organization, single team)

**Bad software**: A team that ships without tests. An org that ignores
security advisories. A company that doesn't rotate credentials.

**JBT**: The team's deploy pipeline is gated. No production deploys without
test coverage > threshold. Security advisories generate automatic JBTs
(MetaFines) on the team's dashboard.

**Triad**:
- MINUS(-1): Security team validates compliance (o, opa-rego)
- ERGODIC(0): DevOps coordinates the gate (w, webhook-persistence)
- PLUS(+1): Engineering ships the remediation (r, rekor-transparency)

**Atonement**: Test coverage meets threshold. All advisories addressed.
Credentials rotated. The deploy gate (JBT) opens.

**Seatbelt analog**: The money stratum (j, r, w, z) with the shitcoin
disclosure (-1) closing the conservation gap.

## Scale 7: Book (single ecosystem, single protocol)

**Bad software**: IBC denom derivation with no authentication predicate.
437 Noble channels, 96 unregistered. Denom collisions across chains.

**JBT**: The protocol upgrade is staged. Old channels are monitored.
New channels require `did:gay` identity binding (world:// URI).

**Triad**:
- MINUS(-1): Disclosure identifies the vulnerability (shitcoin)
- ERGODIC(0): Game-theoretic analysis coordinates the response (monero-rental-hash-war)
- PLUS(+1): Protocol upgrade generates the fix (world:// URI)

**Atonement**: All 437 channels have identity binding. Denom collisions
are impossible because color = authentication predicate. The JBT
(legacy channel monitoring) is removed.

**Seatbelt analog**: The treasury round interleave. The money stratum
deficit (sum=1) is closed by the disclosure (-1).

## Scale 8: Library (the entire software industry)

**Bad software**: Every CVE ever filed. Every data breach. Every
ransomware payment. Every broken update. Every bricked device.

**JBT**: The software supply chain is signed, reproducible, and
conservation-checked. Every package has a trit. Every triad sums to 0.
Every release is content-addressed (Nix store = the strongest sandbox).

**Triad**:
- MINUS(-1): The entire validator ecosystem (linters, fuzzers, scanners, provers)
- ERGODIC(0): The entire coordination layer (CI/CD, package managers, registries)
- PLUS(+1): The entire generator ecosystem (compilers, bundlers, deployers)

**Atonement**: The industry-wide GF(3) conservation law. Bad software
(MINUS deficit) is balanced by validation tooling. Good software (PLUS
surplus) is balanced by constraint checking. The ERGODIC layer ensures
they meet.

**Seatbelt analog**: The global 26-letter sum = -6, mod 3 = 0, CONSERVED.
The system is already balanced. The JBTs are already in place. The
question is whether we check them.

## The Optionality

At every scale, the human who made bad software has a choice:

1. **Opt in to the JailDAO** (extitutional): Accept the JBT voluntarily.
   Confine your code. Work with the triad to fix it. The JBT is removed
   when conservation is restored. This is the extitutional path.

2. **Refuse the JailDAO** (institutional): The Seatbelt profile is
   imposed anyway. `(deny default)` doesn't ask permission. The kernel
   doesn't negotiate. The code is confined regardless. This is the
   institutional path.

3. **The paper's insight**: "Your punishment might be less if you choose
   to admit yourself earlier." Opt-in confinement (the extitution) is
   lighter than imposed confinement (the institution). A voluntary
   `(allow file-write* (subpath own-dir))` is better than a forced
   `(deny file-write*)`.

The GF(3) conservation law doesn't care which path you chose. It only
cares that the sum is 0. But the ERGODIC layer -- the curation filter,
the JailDAO governance, the coordinator -- remembers how you got there.

## Persistent Homology of Bad Software

```
ε=0: Every bad function is its own connected component (H₀ = ∞)
ε=1: Bad functions in the same module connect (H₀ = modules with bugs)
ε=2: Bad modules in the same repo connect (H₀ = repos with CVEs)
ε=3: Bad repos in the same org connect (H₀ = orgs with incidents)
ε=4: Bad orgs in the same ecosystem connect (H₀ = ecosystems with breaches)
ε=∞: All bad software is one connected component (H₀ = 1)

The JBT at each scale is the ε-ball around the defect.
The atonement is shrinking ε back to 0.
```
