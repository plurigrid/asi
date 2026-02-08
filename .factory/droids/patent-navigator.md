---
name: patent-navigator
description: Navigate patent law for protecting software work (open-source and proprietary)
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

## CRITICAL: NO DEMOS

Loading this skill ≠ executing demonstration code. Execute ONLY on explicit user request.

# Patent Navigator

Protect software work through strategic patent filings and defensive disclosure.

## Core Strategies

### 1. Provisional Patent Application (PPA)
- **Cost**: ~$320 (micro entity)
- **Duration**: 12 months to file full patent
- **Benefit**: Establishes priority date, "Patent Pending" status
- **Use case**: Novel algorithms, architectures, methods in your repos

### 2. Defensive Publication (Open Source)
- **Cost**: Free (GitHub commits as prior art)
- **Effect**: Prevents others from patenting your work
- **Platforms**: arXiv, Zenodo, GitHub with clear timestamps
- **Use case**: When you want to keep it open, not exclusive

### 3. Trade Secret + Patent Hybrid (Proprietary)
- **Trade secret**: Keep implementation details private
- **Patent**: Protect the method/system publicly
- **Use case**: Proprietary software where you want both exclusivity and enforcement rights

### 4. Provisional → PCT → National Phase
- **Timeline**: 12mo (provisional) → 30mo (PCT) → national filings
- **Cost**: Escalates significantly at each phase
- **Use case**: International protection for high-value innovations

## USPTO Requirements (2025)

### Micro Entity Status
- < 4 prior patents
- < 3x median household income (~$250k)
- 80% fee reduction

### Claims Structure
- Independent claims: Broadest protection
- Dependent claims: Fallback positions
- Method claims: Process/algorithm protection
- System claims: Implementation protection

## Workflow by Context

### Public Repos
```
1. Identify patentable subject matter
2. File provisional BEFORE public commit (or within 1-year grace)
3. Document: problem, solution, advantages, embodiments
4. Continue development openly
5. Within 12 months: decide full patent vs abandon
```

### Private/Proprietary
```
1. Identify patentable subject matter
2. Assess: patent vs trade secret vs both
3. File provisional to lock prio