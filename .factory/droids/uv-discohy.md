---
name: uv-discohy
description: UV/UVX/Ruff toolchain for DiscoHy Thread Operad with Python packaging and linting
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# UV-DiscoHy Skill: Modern Python Tooling for Thread Operads

**Status**: ✅ Production Ready
**Trit**: 0 (ERGODIC - toolchain neutral)
**Toolchain**: uv + uvx + ruff
**Package**: music-topos with discohy_thread_operad

---

## Overview

This skill provides the **uv/uvx/ruff** toolchain integration for the DiscoHy Thread Operad system. It enables:

1. **Fast dependency management** via uv (10-100x faster than pip)
2. **One-shot tool execution** via uvx (no install required)
3. **Modern linting/formatting** via ruff (replaces black, isort, flake8)
4. **Python packaging** via pyproject.toml with hatchling

## Quick Start

```bash
# Initialize the environment
just uv-init

# Run the DiscoHy operad demo
just uv-discohy

# Lint and format
just uv-lint
just uv-format

# Run with specific variant
just uv-discohy-variant 2-transducer
```

## UV Commands

### Package Management

```bash
# Create virtual environment and install dependencies
uv venv
uv pip install -e ".[dev]"

# Add a dependency
uv pip install discopy>=1.1.0

# Sync all dependencies from pyproject.toml
uv pip sync pyproject.toml

# Show dependency tree
uv pip tree
```

### UVX: One-Shot Tool Execution

```bash
# Run ruff without installing
uvx ruff check src/

# Run pytest without installing
uvx pytest tests/

# Run a specific version
uvx --python 3.12 ruff check src/
```

## Ruff Configuration

From `pyproject.toml`:

```toml
[tool.ruff]
target-version = "py311"
line-length = 100
indent-width = 4

[tool.ruff.lint]
select = [
    "E",      # pycodestyle errors
    "W",      # pycodestyle warnings
    "F",      # Pyflakes
    "I",      # isort
    "B",      # flake8-bugbear
    "C4",     # flake8-comprehensions
    "UP",     # pyupgrade
    "ARG",    # flake8-unused-arguments
    "SIM",    # flake8-simplify
]

[tool.ruff.format]
quote-style = "double"
indent-style = "space"
```

### Ruff Commands

```bash
# Check for issues
ruff check src/ lib/

# Auto-fix issues
ruff check --fix src/

# Format code
ruff format 