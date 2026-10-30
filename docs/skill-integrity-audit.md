# Skill integrity audit and focused repair

Audit base: `293ce9f76e3abcd5ba18db284688bc0d9ac6691d` (main), inspected 2026-10-29.
Only three skill documents are repaired. Other findings are explicit debt, not
semantically accepted instructions. No cryptographic implementation is added.

## Scope and counts

Scan every file whose basename is exactly `SKILL.md`, recursively from the repo
root, including hidden agent directories and `plugins/asi`. This matches the
canonical filename used by the CLI and existing linter. It includes 3,172 tracked
files (discovery was checked against `git ls-files`); directories named SKILL.md
are not files. Lowercase `skill.md`, `skill.variant.md`, backup filenames, and
other historical/reference documents are not canonical entrypoints and are not
included. Fences are not exclusions: conflicted code is still live instruction.

| Finding | Original | Corrected |
|---------|---------:|----------:|
| Canonical skill files checked | 3,172 | 3,172 |
| Files with unresolved merge markers | 31 | 28 |
| Front matter syntax/delimiter/required-string failures | 66 | 66 |
| Distinct files with either failure | 92 | 89 |

The original marker files comprise 23 under `skills/`, one under
`plugins/asi/skills/`, and seven under `ies/music-topos` agent trees. All 31 are
actual competing instruction fragments; none of the observed matches is an
intentional teaching example or historical test fixture. Seven nested project
files are counted explicitly rather than silently excluded as archives. Five
marker files also have front matter failures, so the categories overlap.
Of the 66 front matter failures, 14 are in main/plugin/agent roots and 52 in ies.

Notably, the three repaired files' original front matter *parses as YAML*: earlier
normalization embedded markers in scalar strings. A parser alone cannot detect
this damage, and a body-only conflict never reaches a front matter parser.

## Reproduction and CI policy

Requires Python 3.11+ and one dependency (`PyYAML==6.0.3`); no project package,
cloud API, model, or Babashka install is required for the new command.

```bash
python3 -m pip install PyYAML==6.0.3
python3 scripts/check_skill_integrity.py
python3 scripts/check_skill_integrity.py --json
python3 scripts/check_skill_integrity.py --baseline scripts/skill_integrity_baseline.json
python3 -m unittest discover -s tests -p test_skill_integrity.py -v
```

Default is strict: any finding exits 1; malformed configuration/missing paths
exit 2. Explicit roots or SKILL.md paths restrict the scan. An empty scan fails.
The YAML parser uses safe loading, requires a mapping with nonempty string name
and description, and rejects duplicate keys. It does not attempt runtime-specific
schema parity or execute skill examples while scanning.

The new independent `skill-integrity` job in `.github/workflows/validate.yml`
runs the tests and checks all canonical files against the reviewed baseline.
The baseline contains the 89 **unchanged** remaining files, each with SHA-256 and
a reason. A new defective file, any edit to a deferred defective file, or a stale
entry after repair/deletion fails. Resolve a file and remove its baseline entry
in the same PR. Do not refresh hashes to approve unrelated edits to conflicted
instructions; deliberate exceptions need review. There is no auto-baseline or
auto-repair mode. This is a debt ratchet, not a claim of repository-wide health.

To reproduce the original scan using the new checker without altering the
current checkout (use a fresh destination):

```bash
git worktree add --detach /tmp/asi-integrity-original 293ce9f76e3abcd5ba18db284688bc0d9ac6691d
checker="$PWD/scripts/check_skill_integrity.py"
baseline="$PWD/scripts/skill_integrity_baseline.json"
(cd /tmp/asi-integrity-original && python3 "$checker" --json)
(cd /tmp/asi-integrity-original && python3 "$checker" --baseline "$baseline")
```

## Actual validation results

| Check | Result |
|-------|--------|
| New strict scan on original source | Exit 1; 31 marker files, 66 front matter failures, 92 distinct affected |
| New strict scan on corrected source | Exit 1; 28 marker files, 66 front matter failures, 89 distinct affected |
| New baseline CI check on original source | Exit 1; exactly the three repaired skills block, 89 unchanged deferred |
| New baseline CI check on corrected source | Exit 0; zero blocking, 89 unchanged deferred |
| New strict check on the three corrected skills | Exit 0; zero markers/front matter failures |
| New unit/regression tests | 15 tests pass |
| Existing `node test.js` | 16 tests pass |
| Existing `quick_validate.validate_skill` on the three original files | All return `(True, 'OK')` despite markers |
| Existing Babashka 1.12.208 linter on the three original files | Exit 0; 0 invalid, 3 name warnings |
| Existing Babashka linter on the three corrected files | Exit 0; 0 invalid, 0 warnings |
| Existing Babashka linter across original `skills/` | Exit 1; 1 invalid, 57 portability warnings |
| Existing Babashka linter across corrected `skills/` | Exit 1; 1 invalid, 54 portability warnings |

The new tests cover standard and diff3 markers, larger marker widths, body/fenced
conflicts, markers folded into YAML scalars, YAML syntax/types/duplicate keys,
unsafe tags, hidden/plugin discovery, empty/missing roots, invalid UTF-8, and
baseline changes/staleness. They also check all nine trit input pairs against
modular addition/multiplication and unique balancing, and parse the benchmark
shell examples with `bash -n`. Benchmark engines were not executed: their
external checkouts/binaries are not bundled. DID/QRTP cryptographic tests are
proof obligations in the repaired skill, not fabricated passing integration tests.

Existing CI at the pinned main commit already failed:
[Validate Skills run 29084229543](https://github.com/plurigrid/asi/actions/runs/29084229543)
has failures in `Enforce monotonic skill invariants` and
`Lint SKILL.md frontmatter (all skills, codex semantics)`; `juvix-typecheck` passed.
The manifest step masks lint exit status with `|| true`. The legacy JavaScript
check only looks for front matter delimiters and field substrings. The Babashka
linter only parses front matter and downgrades malformed names to warnings;
it has no whole-document conflict scan. The remaining portability failure is
`skills/rama-gay-zig/SKILL.md` (missing front matter). These existing gates were
not weakened or rewritten by this repair.

## Semantic resolution

- DID/passport: retain public trajectory metadata and QRTP transport, but remove
  the invented fingerprint verification key and forgeable hash challenge response.
  Require independent trusted key bindings, real signatures, issuer-specific trust,
  separate attenuated grants, replay protection, and bounded status freshness.
  Bisimulation is conditional and requires transition proof obligations; neither
  the shared interface nor trit equality proves it. Gap G-P2/G5 stay open.
- GF(3) oracle: the neighboring `skills/propagators/SKILL.md` specifies monotone
  partial knowledge. Keep the more detailed lattice/arithmetic/composition
  material, correct the return type/postconditions, treat model results as
  provisional evidence, and distinguish classification evidence from authority.
  The modular arithmetic is executable in the regression test; the rest remains
  illustrative integration pseudocode.
- Benchmark: competing blocks agree on workloads, flags, package target, and
  fairness requirements, but use different checkout names. Explicit checkout
  variables preserve both possibilities without asserting an unsupported rename.
  Retain historical numbers with a provenance/reproduction qualification.

## Marker inventory and deliberate follow-ups

Line numbers refer to the original commit. Deferred does not mean harmless or
intentional. Validate the indicated semantics against source/tests before merging
branches of the text; do not use a wholesale ours/theirs replacement.

| File | First marker line | Resolution / next evidence required |
|------|------------------:|-------------------------------------|
| `ies/music-topos/.agents/skills/influence-propagation/SKILL.md` | 182 | Deferred — Spectral-centrality extension versus relation list; nested/malformed merge. |
| `ies/music-topos/.codex/skills/borkdude/SKILL.md` | 3 | Deferred — Runtime scope and propagation provenance (codex versus amp) disagree. |
| `ies/music-topos/.codex/skills/gay-mcp/SKILL.md` | 3 | Deferred — Color/SPI claims, Specter caching extension, and propagation provenance differ. |
| `ies/music-topos/.codex/skills/localsend-mcp/SKILL.md` | 74 | Deferred — Transport/Specter extension contains unresolved nested merge fragments. |
| `ies/music-topos/.codex/skills/three-match/SKILL.md` | 3 | Deferred — 3-SAT gadget and caching extension plus propagation provenance need reconciliation. |
| `ies/music-topos/.codex/skills/unworld/SKILL.md` | 3 | Deferred — Derivational model and propagation provenance (codex versus amp) differ. |
| `ies/music-topos/.ruler/skills/acsets/SKILL.md` | 8 | Deferred — ACSet indexing, conservation, and category-of-elements extensions need Julia validation. |
| `plugins/asi/skills/yb-translator/SKILL.md` | 191 | Deferred — Related-skill trit assignments and expanded ontology workflow disagree. |
| `skills/aaif-governance-interleave/SKILL.md` | 2 | Deferred — Governance/compatibility scope and GF(3) proof claims need source verification. |
| `skills/belief-revision-log/SKILL.md` | 2 | Deferred — Persistent storage/schema and claimed gap closure need implementation evidence. |
| `skills/benchmark/SKILL.md` | 2 | Repaired — Reconciled external checkout names via explicit paths; retained fairness protocol. |
| `skills/bisimulation-oracle/SKILL.md` | 2 | Deferred — Finite/coinductive proof conditions and decision outcomes need formal review. |
| `skills/catlab-asi-interleave/SKILL.md` | 2 | Deferred — ACSet schema and integration/proof claims need Julia/API validation. |
| `skills/did-passport-interleave/SKILL.md` | 2 | Repaired — Separated structural metadata, authentication, issuer trust, and authority; replaced unproved security equivalence. |
| `skills/egpu/SKILL.md` | 2 | Deferred — Generic GPU paths versus Basin-specific runtime and hotplug policy. |
| `skills/emacspeak-binaural/SKILL.md` | 2 | Deferred — Sound-theme setup and auditory icon coverage differ. |
| `skills/geomstats-fisher-rao/SKILL.md` | 2 | Deferred — Information-geometry assumptions and integration claims need mathematical review. |
| `skills/gf3-conservation-oracle/SKILL.md` | 2 | Deferred — Graph/triad definitions and certificate requirements need reconciliation. |
| `skills/gf3-trit-oracle/SKILL.md` | 2 | Repaired — Reconciled total classification with partial-information lattice; retained documented arithmetic. |
| `skills/graft-prefer/SKILL.md` | 3 | Deferred — Generic versus Basin build scope, benchmark commands, and environment policy. |
| `skills/monad-bayes-asi-interleave/SKILL.md` | 2 | Deferred — Transformer-stack/integration claims need source and typechecking evidence. |
| `skills/mutual-information-oracle/SKILL.md` | 2 | Deferred — Estimator and coordination semantics require statistical review. |
| `skills/neurofeedback-oracle/SKILL.md` | 2 | Deferred — Signal thresholds and failure handling need implementation/data validation. |
| `skills/nonlinear-dynamics-observatory/SKILL.md` | 2 | Deferred — Model integrations and observatory scope differ. |
| `skills/norvidize/SKILL.md` | 8 | Deferred — Competing content and operating instructions need deliberate editorial resolution. |
| `skills/ontology-asi-interleave/SKILL.md` | 2 | Deferred — Ontology mapping and asserted bridge properties need source validation. |
| `skills/vertex-ai-protein-interleave/SKILL.md` | 2 | Deferred — Cloud/protein pipeline wiring and service assumptions need validation. |
| `skills/vertex-protein-bisimulation/SKILL.md` | 2 | Deferred — Protein-model equivalence and inference claims need formal/empirical evidence. |
| `skills/zig-syrup-propagator-interleave/SKILL.md` | 2 | Deferred — Module contracts, passport trust, and claimed gap closures need implementation audit. |
| `skills/zubyul-connectome/SKILL.md` | 2 | Deferred — Connectome modeling/integration scope and evidence need review. |
| `skills/zubyul-gene-networks/SKILL.md` | 2 | Deferred — Gene-network analysis and integration scope need review. |

The complete front matter debt inventory (including paths with no markers) and
exact unchanged-content hashes are in `scripts/skill_integrity_baseline.json`.
The JSON audit command prints per-line diagnostics for every finding.
