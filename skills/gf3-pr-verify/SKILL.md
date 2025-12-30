---
name: gf3-pr-verify
description: Verify GF(3) skill conservation on pull requests. Ensures every contribution
  records which skills were used with proper trit assignments (PLUS/ERGODIC/MINUS) and
  validates that the sum is conserved (mod 3). Required for PR acceptance.
license: Apache-2.0
metadata:
  trit: -1
  color: "#3541C7"
  role: validator
  source: plurigrid/asi
---

# GF(3) PR Verification

Enforces skill coloring requirements on all contributions. PRs without valid GF(3) manifests will be rejected.

## Why GF(3) Conservation?

Every contribution uses skills. Recording which skills were used:
1. **Provenance**: Track how code was created
2. **Balance**: Ensure generator/validator equilibrium
3. **Reproducibility**: Others can use same skill triads
4. **Attribution**: Credit skill authors

## Required PR Format

Every PR body or comment MUST include:

```markdown
## GF(3) Skill Coloring

| Skill | Trit | Color | Role |
|-------|------|-------|------|
| skill-name-1 | ⊕ (+1) | #RRGGBB | Generator |
| skill-name-2 | ○ (0) | #RRGGBB | Coordinator |
| skill-name-3 | ⊖ (-1) | #RRGGBB | Validator |

**Conservation**: Σ = (+1) + (0) + (-1) = 0 ✓

Thread: ⟨xxxx⟩
```

## Trit Definitions

| Trit | Symbol | Value | Role | Hue Range | Examples |
|------|--------|-------|------|-----------|----------|
| PLUS | ⊕ | +1 | Generator/Executor | 0-60°, 300-360° (warm) | gay-mcp, gaymove, depth-search |
| ERGODIC | ○ | 0 | Coordinator/Synthesizer | 60-180° (neutral) | acsets, aptos-agent, ducklake-walk |
| MINUS | ⊖ | -1 | Validator/Constrainer | 180-300° (cold) | code-review, narya-proofs, three-match |

## Conservation Rules

### Rule 1: Single PR Conservation
```
Σ trits ≡ 0 (mod 3)
```

Valid combinations:
- `⊕ ⊗ ○ ⊗ ⊖` → 1 + 0 + (-1) = 0 ✓
- `⊕ ⊗ ⊕ ⊗ ⊖ ⊗ ⊖` → 1 + 1 + (-1) + (-1) = 0 ✓
- `○ ⊗ ○ ⊗ ○` → 0 + 0 + 0 = 0 ✓

Invalid:
- `⊕ ⊗ ○` → 1 + 0 = 1 ≠ 0 (mod 3) ✗
- `⊕ ⊗ ⊕` → 1 + 1 = 2 ≠ 0 (mod 3) ✗

### Rule 2: Cross-PR Triads
PRs can form balanced triads across the repository:

```
PR#23○ ⊗ PR#24⊕ ⊗ PR#25⊖ ⊢ Σ = 0 ✓
```

Document cross-PR links:
```markdown
### Cross-PR Triad
This PR (⊕) balances with:
- PR#XX (○) - coordinator
- PR#YY (⊖) - validator
```

### Rule 3: Thread Linkage
Include thread ID for provenance:
```
Thread: ⟨6d21⟩
```

## Verification Commands

### Check PR Body
```bash
# Extract and verify GF(3) from PR
gh pr view $PR --json body | jq -r '.body' | \
  grep -oE '[⊕○⊖]' | \
  awk 'BEGIN{s=0} {if($0=="⊕")s+=1; if($0=="⊖")s-=1}
       END{m=(s%3+3)%3; print "Σ="s" mod3="m; exit(m!=0)}'
```

### Check All Open PRs
```bash
# Verify all open PRs have GF(3) manifests
for pr in $(gh pr list --json number -q '.[].number'); do
  echo -n "PR#$pr: "
  gh pr view $pr --json body | jq -r '.body' | \
    grep -q 'GF(3)' && echo "✓" || echo "✗ MISSING"
done
```

### Generate Skill Manifest
```bash
# List skills used in this session
cat << 'EOF'
## GF(3) Skill Coloring

| Skill | Trit | Color | Role |
|-------|------|-------|------|
| gf3-pr-verify | ⊖ (-1) | #3541C7 | Validator |
| code-review | ⊖ (-1) | #3541C7 | Validator |
| gay-mcp | ⊕ (+1) | #FFD700 | Generator |

**Conservation**: Σ = (-1) + (-1) + (+1) = -1 ≡ 2 (mod 3) ⚠️
Need 1 more ⊕ or 2 more ⊖ to balance
EOF
```

## CI/CD Integration

Add to `.github/workflows/validate.yml`:

```yaml
- name: Verify PR GF(3) Conservation
  if: github.event_name == 'pull_request'
  run: |
    PR_BODY=$(gh pr view ${{ github.event.pull_request.number }} --json body -q '.body')

    # Check for GF(3) section
    if ! echo "$PR_BODY" | grep -q 'GF(3)'; then
      echo "::error::PR missing GF(3) Skill Coloring section"
      exit 1
    fi

    # Verify conservation
    SUM=$(echo "$PR_BODY" | grep -oE '[⊕○⊖]' | \
      awk 'BEGIN{s=0} {if($0=="⊕")s+=1; if($0=="⊖")s-=1} END{print s}')
    MOD=$((($SUM % 3 + 3) % 3))

    if [ "$MOD" -ne 0 ]; then
      echo "::error::GF(3) not conserved: Σ=$SUM (mod 3)=$MOD"
      exit 1
    fi

    echo "✓ GF(3) conserved: Σ=$SUM (mod 3)=0"
```

## Common Triads

### Development
```
code-review⊖ ⊗ aptos-agent○ ⊗ gaymove⊕ ⊢ 0
```

### Research
```
narya-proofs⊖ ⊗ acsets○ ⊗ depth-search⊕ ⊢ 0
```

### Infrastructure
```
three-match⊖ ⊗ ducklake-walk○ ⊗ gay-mcp⊕ ⊢ 0
```

### This PR
```
gf3-pr-verify⊖ ⊗ code-review⊖ ⊗ autopoiesis⊕ ⊗ gay-mcp⊕ ⊢ 0
  = (-1) + (-1) + (+1) + (+1) = 0 ✓
```

## Error Messages

| Error | Meaning | Fix |
|-------|---------|-----|
| `PR missing GF(3) section` | No skill manifest | Add `## GF(3) Skill Coloring` section |
| `GF(3) not conserved` | Σ ≠ 0 (mod 3) | Add balancing skills |
| `Invalid trit value` | Not in {-1, 0, +1} | Use ⊖/○/⊕ symbols |
| `Missing thread ID` | No `⟨xxxx⟩` | Link to ampcode thread |

## Operator Algebra

Skills combine via tensor product (⊗):
```
⟦s₁ ⊗ s₂⟧ = (trit₁ + trit₂, mix(color₁, color₂), xor(seed₁, seed₂))
```

Conservation law:
```
∀ PR: Σᵢ tritᵢ ≡ 0 (mod 3)
```

This ensures the skill lattice remains balanced across all contributions.



## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Graph Theory
- **networkx** [○] via bicomodule
  - Universal graph hub

### Bibliography References

- `general`: 734 citations in bib.duckdb

## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: ⊗
Kan Role: Adj
Color: #26D826
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

This ensures compositional coherence in the Cat# equipment structure.
