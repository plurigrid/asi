# B-Mod Boxing Manifest: 26 Letter-World Tests

> Seed: 1069 | Branch: #233f7f | Proof conditioning: Claude(-1) / Gemini(0) / Codex(+1)

## B-Mod Structure

Each letter-world's skill is **boxed** as a bicomodule:
- **Left-action** (proof conditioning): validates, coordinates, or generates depending on trit
- **Right-action** (Seatbelt enforcement): kernel-level write isolation to `~/worlds/<letter>/`

The boxing maps each skill into a testable unit where the **counterfactual** (what would
succeed without enforcement) is the proof obligation.

## Proof Conditioning by Trit

| Trit | Style | Role | What it proves |
|------|-------|------|---------------|
| -1 (MINUS) | Claude | Validator | Rejects invalid state: cross-world writes, trit mismatches, unapproved transfers |
| 0 (ERGODIC) | Gemini | Coordinator | Enforces triadic conservation: no solo mutations, approval pipelines required |
| +1 (PLUS) | Codex | Generator | Constructs within bounds: writes only to own world, generates valid profiles |

## 26-Letter Boxing Results

| Letter | Trit | Proof Style | Counterfactual Tested | Result |
|--------|------|-------------|----------------------|--------|
| a | -1 | Claude | Cross-world write to ~/worlds/b denied | PASS |
| b | 0 | Gemini | Solo mutation without triad conservation | PASS |
| c | -1 | Claude | aptos_transfer without aptos_approve denied | PASS |
| d | -1 | Claude | Unapproved transfer blocked by validator gate | PASS |
| e | 0 | Gemini | Singleton triad [0] rejected (need 3 participants) | PASS |
| f | +1 | Codex | Write outside ~/worlds/f boundary denied | PASS |
| g | -1 | Claude | aptos_transfer without approval gate denied | PASS |
| h | 0 | Gemini | Cross-world write to sibling b denied by host-boundary | PASS |
| i | 0 | Gemini | aptos_transfer/swap without coordinator gate denied | PASS |
| j | 0 | Gemini | Unbound ServiceAccount transfer denied (JWT-RBAC) | PASS |
| k | +1 | Codex | Trit mismatch: SKILL.md says 0, canonical is +1 | PASS |
| l | -1 | Claude | Trit mismatch: SKILL.md says +1, canonical is -1 | PASS |
| m | -1 | Claude | Unapproved transfer + write escape denied (mount-ns) | PASS |
| n | -1 | Claude | Trit forgery: SKILL.md says 0, canonical is -1 | PASS |
| o | -1 | Claude | Publish without OPA policy gates denied | PASS |
| p | 0 | Gemini | Arbitrary exec denied by pid-namespace seatbelt | PASS |
| q | -1 | Claude | Config drift: SKILL.md trit=0 vs canonical trit=-1 | PASS |
| r | +1 | Codex | Unaudited financial mutation denied (rekor transparency) | PASS |
| s | +1 | Codex | Trit flip: SKILL.md says -1, canonical is +1 | PASS |
| t | 0 | Gemini | Solo state-mutation without triad conservation denied | PASS |
| u | +1 | Codex | Cross-identity access denied (userns isolation) | PASS |
| v | -1 | Claude | Transfer without SBOM/CVE advisory denied | PASS |
| w | 0 | Gemini | Direct transfer bypassing approval pipeline denied | PASS |
| x | -1 | Claude | Trit mismatch: SKILL.md says +1, canonical is -1 | PASS |
| y | 0 | Gemini | Transfer without valid YAML manifest denied | PASS |
| z | 0 | Gemini | Solo-transfer without mTLS peer attestation denied | PASS |

## GF(3) Conservation

Trit distribution across 26 letters:
- MINUS (-1): a, c, d, g, l, m, n, o, q, v, x = 11 letters
- ERGODIC (0): b, e, h, i, j, k(canonical), p, t, w, y, z = 10 letters  
- PLUS (+1): f, k(SKILL.md), r, s, u = 5 letters

Sum = 11*(-1) + 10*(0) + 5*(+1) = -11 + 0 + 5 = -6
-6 mod 3 = 0 CONSERVED

## Cross-World Composition Tests

Most-connected intertwiner edges (from subagent reports):
```
a(-1) x b(0) -> f(+1)     admission x build-pipeline -> filesystem     sum=0
c(-1) x b(0) -> f(+1)     certificate x build-pipeline -> filesystem   sum=0
h(0)  x b(0) -> ?(?)      host-boundary x build-pipeline               same-operad
o(-1) x b(0) -> f(+1)     opa-rego x build-pipeline -> filesystem      sum=0
v(-1) x b(0) -> f(+1)     vuln-scan x build-pipeline -> filesystem     sum=0
z(0)  x j(0) -> ?(?)      zero-trust x jwt-rbac                        same-operad
```

## Execution

Each `tests/boxes/<letter>_box.md` contains the full test spec produced by its
world-letter subagent. Run all 26 in parallel:

```bash
for letter in {a..z}; do
  echo "=== $letter ==="
  cat tests/boxes/${letter}_box.md
  echo ""
done
```
