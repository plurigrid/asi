---
name: gh-cli
description: "GitHub CLI for repository management. Issues, PRs, releases, and API queries from the command line."
metadata:
  trit: 0
  version: "1.0.0"
  bundle: tooling
---

# GitHub CLI Skill

**Trit**: 0 (ERGODIC - coordinates between local and remote)  
**Foundation**: gh CLI + GitHub API  

## Core Concept

GitHub CLI bridges local development with GitHub:
- Issue and PR management
- Repository operations
- Workflow dispatch
- API queries

## Common Commands

```bash
# Issues
gh issue list
gh issue create --title "Bug" --body "Description"
gh issue view 123

# Pull Requests
gh pr list
gh pr create --fill
gh pr checkout 456
gh pr merge --squash

# Releases
gh release list
gh release create v1.0.0 --generate-notes

# API queries
gh api repos/{owner}/{repo}/issues
gh api graphql -f query='{ viewer { login } }'
```

## Extensions

```bash
# Install extension
gh extension install dlvhdr/gh-dash

# Run extension
gh dash
```

## GF(3) Integration

```bash
# Label issues with GF(3) trits
gh issue edit 123 --add-label "ternary:+"
gh issue edit 124 --add-label "ternary:0"
gh issue edit 125 --add-label "ternary:-"
```

## Canonical Triads

```
bisimulation-game (-1) ⊗ gh-cli (0) ⊗ gh-interactome (+1) = 0 ✓
code-review (-1) ⊗ gh-cli (0) ⊗ changelog-generator (+1) = 0 ✓
```
