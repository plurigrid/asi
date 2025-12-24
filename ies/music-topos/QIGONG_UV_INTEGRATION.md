# qigong: Modern Python Tooling with uv, ruff, and uvx

## Overview

**flox-qigong-uv.toml** integrates modern Python tooling for faster, more efficient development:

- **uv**: Ultra-fast Python package installer & environment manager (replaces pip/venv)
- **ruff**: Fast Python linter & formatter (replaces pylint/black)
- **uvx**: Run isolated Python CLI tools without installation

---

## Quick Start with uv

### 1. Activate qigong with uv support
```bash
cd /Users/bob/ies/music-topos
flox activate -d flox-qigong-uv.toml
```

### 2. Create virtual environment
```bash
flox scripts venv-create
# Or manually:
uv venv ~/.qigong/venv --python 3.12
```

### 3. Activate virtual environment
```bash
source ~/.qigong/venv/bin/activate
# Or:
flox scripts venv-activate
```

### 4. Install monitoring tools
```bash
uv pip install asitop psutil pandas numpy scipy matplotlib
# Or:
flox scripts install-monitoring
```

---

## uv: Ultra-Fast Package Management

### Why uv?

| Feature | pip | uv |
|---------|-----|----|
| Speed | ~10-30s | ~1-5s |
| Installation | Sequential | Parallel |
| Resolution | Simple | Advanced |
| Caching | Basic | Aggressive |
| Compilation | Python | Rust |

### Common uv Commands

```bash
# Create virtual environment (much faster than venv)
uv venv ~/.qigong/venv --python 3.12

# Install packages (parallel, cached)
uv pip install asitop psutil pandas

# Install from requirements.txt
uv pip install -r requirements.txt

# Compile requirements for reproducibility
uv pip compile requirements.in > requirements.txt

# Sync environment to exact state
uv pip sync requirements.txt
```

### uv in qigong Context

```bash
# Fast baseline monitoring setup
uv venv ~/.qigong/venv
source ~/.qigong/venv/bin/activate

# Install all monitoring tools at once
uv pip install asitop psutil pandas numpy scipy matplotlib seaborn

# Typical time: ~5 seconds (vs. 30s+ with pip)
```

---

## ruff: Ultra-Fast Python Linting

### Why ruff?

- 10-100x faster than pylint/flake8
- Written in Rust, single binary
- Drop-in replacement for multiple tools

### ruff Features

```bash
# Check code for style issues
ruff check qigong-control.sh

# Fix issues automatically
ruff check --fix ~/.qigong/data/power_model.py

# Format code (like black)
ruff format ~/.qigong/data/*.py

# Show specific violations
ruff check --select E,W,F  # Errors, Warnings, Flakes

# Ignore specific rules
ruff check --ignore E501  # Ignore line length
```

### Integration with qigong

```bash
# Lint all Python scripts
flox scripts lint-scripts

# Format all Python scripts
flox scripts format-scripts

# In development workflow
ruff check qigong-control.sh --fix
ruff format qigong-control.sh
```

---

## uvx: Run Isolated Python Tools

### Why uvx?

- No global installation needed
- Isolated environment per tool
- Perfect for one-off CLI tools

### uvx Examples

```bash
# Run asitop without installing
uvx asitop

# Run with specific version
uvx "asitop==1.0.0"

# Run custom script
uvx --python 3.12 my_script.py

# With dependencies
uvx --with requests --with pandas my_script.py
```

### uvx in qigong

```bash
# Monitor P/E cores without installation
uvx asitop

# One-off Python analysis
uvx --with pandas --with duckdb analysis.py

# Check Python version
uvx --version

# Interactive Python shell
uvx python3
```

---

## Workflow: Complete Monitoring Setup with uv

### Traditional Approach (pip)
```bash
# 1. Create venv
python3 -m venv ~/.qigong/venv          # ~5 seconds

# 2. Activate
source ~/.qigong/venv/bin/activate

# 3. Upgrade pip
pip install --upgrade pip               # ~10 seconds

# 4. Install tools
pip install asitop psutil pandas numpy scipy  # ~30 seconds

# Total: ~45 seconds
```

### Modern Approach (uv)
```bash
# 1. Create venv
uv venv ~/.qigong/venv --python 3.12   # ~1 second

# 2. Activate
source ~/.qigong/venv/bin/activate

# 3. Install tools
uv pip install asitop psutil pandas numpy scipy  # ~3 seconds

# Total: ~4 seconds (10x faster!)
```

---

## qigong Scripts with uv

### Create Virtual Environment
```bash
flox scripts venv-create
# Creates: ~/.qigong/venv
# Python: 3.12 (specified)
# Time: ~1 second
```

### Install Monitoring Tools
```bash
flox scripts install-monitoring
# Installs: asitop, psutil, pandas, numpy, scipy, matplotlib
# Into: ~/.qigong/venv
# Time: ~3 seconds
```

### Run Monitoring Dashboard
```bash
flox scripts run-monitoring
# Real-time: P/E core utilization, power consumption
# Updates: Every 2 seconds
# Stop: Ctrl+C
```

### Monitor P/E Cores
```bash
flox scripts monitor-cores
# Uses asitop via uvx if available
# Fallback: sysctl-based monitoring
```

### Python Interactive Shell
```bash
flox scripts python-shell
# Launches: Python 3.12 in qigong venv
# Available: asitop, psutil, pandas, numpy, etc.
```

---

## Advanced: Creating Custom Tools

### Create Python Tool for Thermal Analysis

```python
# ~/.qigong/thermal_analyzer.py
import subprocess
import json
import sys

def analyze_thermal():
    result = subprocess.run(
        ['powermetrics', '-n', '5', '-f', 'json', '-s', 'cpu_power,gpu_power,thermal_pressure'],
        capture_output=True,
        text=True
    )

    metrics = json.loads(result.stdout)

    print("=== Thermal Analysis ===")
    for m in metrics:
        print(f"CPU: {m['cpu_power']:.1f}W | GPU: {m['gpu_power']:.1f}W | Thermal: {m['thermal_pressure']}")

if __name__ == "__main__":
    analyze_thermal()
```

### Run with uvx (No Installation)
```bash
# First approach: use uvx directly
uvx --with psutil ./thermal_analyzer.py

# Or run in qigong venv
source ~/.qigong/venv/bin/activate
python ~/.qigong/thermal_analyzer.py
```

### Format with ruff
```bash
# Auto-format the file
ruff format ~/.qigong/thermal_analyzer.py

# Check for issues
ruff check ~/.qigong/thermal_analyzer.py --fix
```

---

## Configuration Files

### pyproject.toml for qigong Project

```toml
[project]
name = "qigong"
version = "3.0.0"
description = "Red Team / Blue Team Resource Management"
requires-python = ">=3.12"

[tool.uv]
python-version = "3.12"

[tool.ruff]
target-version = "py312"
line-length = 100

[tool.ruff.lint]
select = ["E", "F", "W", "I"]  # Errors, Flakes, Warnings, Imports
ignore = ["E501"]  # Line length handled separately

[tool.ruff.format]
quote-style = "double"
```

### requirements.txt Generated by uv

```bash
# Create
uv pip compile -o ~/.qigong/requirements.txt --python-version 3.12 << 'EOF'
asitop
psutil
pandas
numpy
scipy
matplotlib
EOF

# Use
uv pip sync ~/.qigong/requirements.txt
```

---

## Comparison: Brew vs. uv vs. Nix

| Aspect | Homebrew | uv | Nix |
|--------|----------|----|----|
| Speed | Slow | Fast | Slow (first run) |
| Isolation | None | Good | Excellent |
| Reproducibility | Poor | Good | Excellent |
| System Pollution | High (/opt/homebrew) | None | None |
| Python Version Control | Poor | Excellent | Excellent |
| Learning Curve | Easy | Easy | Steep |
| macOS Native | Yes | Yes | No (translation) |

### Recommendation for qigong
**uv + Nix via Flox**: Best of both worlds
- Flox provides system tools via Nix (reproducible, isolated)
- uv manages Python environment (fast, modern)
- ruff formats/lints Python code (fast, integrated)

---

## Troubleshooting

### Issue: "uv: command not found"
```bash
# Verify uv is in Flox
flox activate -d flox-qigong-uv.toml
which uv
# Should show path in ~/.flox/environments/...
```

### Issue: "uvx: installation from PyPI failed"
```bash
# Try with explicit version
uvx "asitop==1.0.0"

# Or use standard Python
source ~/.qigong/venv/bin/activate
python3 -m pip install asitop
```

### Issue: Python version mismatch
```bash
# Check Python version
python3 --version  # Should be 3.12

# Force specific version
uv venv ~/.qigong/venv --python 3.12.0

# Verify
~/.qigong/venv/bin/python --version
```

### Issue: ruff formatting conflicts with existing code
```bash
# Check what changes ruff wants
ruff check --fix --diff ~/.qigong/data/power_model.py

# Apply changes
ruff format ~/.qigong/data/power_model.py

# Verify changes
git diff ~/.qigong/data/power_model.py
```

---

## Integration with qigong Refinements

### Using uv for Monitoring Tool Development

```python
# ~/.qigong/refinement_monitor.py
import uv  # Not actually used, but shows intent
import subprocess
import json

class RefinementMonitor:
    def monitor_thermal(self):
        """Refinement 4 & 9: Thermal power modeling"""
        result = subprocess.run(['powermetrics', '-n', '1', '-f', 'json'],
                               capture_output=True, text=True)
        return json.loads(result.stdout)

    def monitor_cores(self):
        """Refinement 1: P/E cluster monitoring"""
        import psutil
        return {
            'p_cores': psutil.cpu_count(logical=False),
            'e_cores': psutil.cpu_count(logical=True) - psutil.cpu_count(logical=False)
        }
```

### Running Analysis with pandas
```python
# ~/.qigong/analyze_engagement.py
import pandas as pd
import duckdb

# Load thermal baseline
df = pd.read_json('~/.qigong/data/thermal_baseline_*.json')

# Query with DuckDB
result = duckdb.query("""
  SELECT
    timestamp,
    cpu_power,
    gpu_power,
    cpu_power + gpu_power as total_power
  FROM df
  WHERE total_power > 30
  ORDER BY timestamp
""").to_df()

print(result)
```

---

## Next Steps

1. **Activate**: `flox activate -d flox-qigong-uv.toml`
2. **Setup**: `flox scripts venv-create && flox scripts install-monitoring`
3. **Monitor**: `flox scripts run-monitoring`
4. **Develop**: Write Python tools, lint with `ruff`, install with `uv pip`
5. **Deploy**: Use `uvx` for one-off tools, `uv pip sync` for reproducible environments

---

## References

- [uv Documentation](https://docs.astral.sh/uv/)
- [ruff Documentation](https://docs.astral.sh/ruff/)
- [uvx for CLI Tools](https://docs.astral.sh/uv/guides/scripts/)
- [Python with uv in Flox](https://flox.dev/docs/languages/python/)

