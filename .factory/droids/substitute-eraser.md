---
name: substitute-eraser
description: This skill should be used when the user asks to "scan for TODOs", "find placeholders", "clean up stubs", "remove temporary code", "audit for incomplete code", or "erase substitutions from codebase". Scans existing files for placeholder tokens and generates remediation plan.
model: inherit
tools: read-only
---

# Substitute Eraser

Scan existing codebases for placeholder tokens. Generate remediation plan.

## Purpose

Audit existing files for substitution tokens (TODO, FIXME, placeholder, mock, etc.) and produce actionable remediation plan. Distinct from `accept-no-substitutes` which validates agent output.

## Scope: Existing Files

This skill scans what already exists:
- Source code files
- Configuration files
- Documentation with stale placeholders
- Test fixtures that leaked into production

**Complements** `accept-no-substitutes` (output validation).

## Trit Assignment

- **Trit**: -1 (MINUS/VALIDATOR)
- **Hue**: 270° (violet - deep scan)
- **Role**: Codebase auditor, technical debt detector

## Scan Workflow

### 1. Discovery
```bash
# Scan current directory
just substitute-scan .

# Scan specific path
just substitute-scan src/
```

### 2. Classification

| Severity | Tokens | Action |
|----------|--------|--------|
| **CRITICAL** | TODO, FIXME, placeholder, xxx | Must fix before merge |
| **WARNING** | mock-*, fake-*, stub-* (outside tests) | Review context |
| **INFO** | example_*, demo_* | Document or remove |

### 3. Remediation Report

Output format:
```
SUBSTITUTE ERASER REPORT
========================
Scanned: 142 files
Found: 23 substitutions

CRITICAL (7):
  src/auth.py:42      TODO: implement token refresh
  src/api.py:118      placeholder value
  src/db.py:55        FIXME: race condition
  ...

WARNING (12):
  src/service.py:30   mock_client (not in test file)
  ...

INFO (4):
  README.md:15        example_config
  ...

REMEDIATION PLAN:
1. [CRITICAL] src/auth.py:42 - Implement token refresh logic
2. [CRITICAL] src/api.py:118 - Replace placeholder with actual value
...
```

## Context-Aware Exceptions

### Acceptable Locations

| Pattern | Acceptable In |
|---------|---------------|
| `mock-*`, `fake-*`, `stub-*` | `*_test.py`, `test_*.py`, `/tests/` |
| `example_*` | `README.md`, `/docs/`, `/examples/` |
| `demo_*` | `/demo/`, documentation |
| `TODO` | 