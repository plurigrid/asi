---
name: gh
description: GitHub CLI (212 man pages).
metadata:
  trit: 0
geodesic: true
moebius: "μ(n) ≠ 0"
---

# gh

GitHub CLI (212 man pages).

## Auth

```bash
gh auth login
gh auth status
gh auth token
```

## Repo

```bash
gh repo clone owner/repo
gh repo create name --public
gh repo view --web
```

## PR

```bash
gh pr create --title "Title" --body "Body"
gh pr list --state open
gh pr checkout 123
gh pr merge --squash
```

## Issue

```bash
gh issue create
gh issue list --label bug
gh issue close 42
```

## API

```bash
gh api repos/{owner}/{repo}/issues
gh api graphql -f query='{ viewer { login } }'
```

## Actions

```bash
gh run list
gh run view 12345
gh workflow run deploy.yml
```

## Non-Backtracking Geodesic Qualification

**Condition**: μ(n) ≠ 0 (Möbius squarefree)

This skill is qualified for non-backtracking geodesic traversal:

1. **Prime Path**: No state revisited in skill invocation chain
2. **Möbius Filter**: Composite paths (backtracking) cancel via μ-inversion
3. **GF(3) Conservation**: Trit sum ≡ 0 (mod 3) across skill triplets
4. **Spectral Gap**: Ramanujan bound λ₂ ≤ 2√(k-1) for k-regular expansion

```
Geodesic Invariant:
  ∀ path P: backtrack(P) = ∅ ⟹ μ(|P|) ≠ 0
  
Möbius Inversion:
  f(n) = Σ_{d|n} g(d) ⟹ g(n) = Σ_{d|n} μ(n/d) f(d)
```
