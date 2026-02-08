---
name: gh-cli
description: GitHub CLI for repository management. Issues, PRs, releases, and API queries from the command line.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
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



## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Graph Theory
- **networkx** [○] via bicomodule
  - Universal graph hub

### Bibliography References

- `general`: 734 citations in bib.duckdb



## SDF Interleaving

This skill connects to **Software Design for Flexibility** (Hanson & Sussman, 2021):

### Primary Chapter: 9. Generic Procedures

**Concepts**: dispatch, multimethod, predicate dispatch, generic

### GF(3) Balanced Triad

```
gh-cli (−) + SDF.Ch9 (○) + [balancer] (+) = 0
```

**Skill Trit**: -1 (MINUS - verification)

### Secondary Chapters

- Ch10: Adventure Game Example

### Connection Pattern

Generic procedures dispatch on predicates. This skill selects implementations dynamically.
## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: 