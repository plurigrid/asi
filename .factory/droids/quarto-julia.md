---
name: quarto-julia
description: 'Quarto + Julia Skill'
model: inherit
tools: read-only
---

# Quarto + Julia Skill

**Status**: Production Ready
**Trit**: 0 (ERGODIC - coordinator/synthesizer)
**Purpose**: Reproducible documents with Julia code blocks and GF(3) skill tracking

---

## Overview

Quarto is a scientific publishing system that renders `.qmd` files to HTML, PDF, and more. Combined with Julia, it enables:

1. **Executable documents** - Julia code blocks run during render
2. **Skill activation logs** - Track GF(3) triads in rendered output
3. **Reproducible research** - Same seed = same colors = same results

## Two Julia Engines

| Feature | `julia` Engine (NEW) | `jupyter` Engine |
|---------|---------------------|------------------|
| Execute Julia code | ✅ | ✅ |
| Keep sessions alive | ✅ | ✅ |
| No Python required | ✅ | ❌ |
| No global pkg install | ✅ | ❌ |
| juliaup integration | ✅ | ❌ |
| Python/R via PythonCall/RCall | ✅ | ❌ |
| QuartoTools.jl expandable cells | ✅ | ❌ |

**Recommendation**: Use `engine: julia` for new projects.

## Installation (No Homebrew)

```bash
# Download and extract
cd /tmp
curl -sL https://github.com/quarto-dev/quarto-cli/releases/download/v1.6.42/quarto-1.6.42-macos.tar.gz -o quarto.tar.gz
tar -xzf quarto.tar.gz

# Install to ~/bin with proper structure
mkdir -p ~/bin/quarto-1.6.42
cp -r bin share ~/bin/quarto-1.6.42/

# Create wrapper script (critical for path resolution)
cat > ~/bin/quarto << 'EOF'
#!/bin/bash
export QUARTO_SHARE_PATH="$HOME/bin/quarto-1.6.42/share"
exec "$HOME/bin/quarto-1.6.42/bin/quarto" "$@"
EOF
chmod +x ~/bin/quarto

# Add to PATH
echo 'export PATH="$HOME/bin:$PATH"' >> ~/.zshrc
export PATH="$HOME/bin:$PATH"

# Verify
quarto --version  # Should show 1.6.42
```

## Basic .qmd Document (Modern julia Engine)

```markdown
---
title: "GF(3) Skill Activation Log"
author: "Plurigrid ASI"
date: today
format:
  html:
    code-fold: true
    toc: true
    theme: cosmo
engine: julia
execute:
  echo: true
  cache: true
---

## Skill Triad

```{julia}
#| label: gf3-triad
#| code-summary: "Define GF(3) s