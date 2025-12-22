# qigong: Complete File Index & Navigation Guide

## Overview

**qigong** is a comprehensive flox-based environment for red team / blue team exercises on macOS Sequoia with Apple Silicon. This file maps all qigong components.

---

## Core Environment Files

### Main Flox Configuration

| File | Purpose | When to Use |
|------|---------|------------|
| **flox-qigong-uv.toml** | **Primary environment (recommended)** | Start here - includes uv, ruff, uvx |
| flox-qigong-pure-nix.toml | Pure Nix without uv | Alternative if you prefer nixpkgs only |
| flox-qigong.toml | Original homebrew-based (deprecated) | Legacy, migration target |

**→ Use `flox-qigong-uv.toml` for new setups**

---

## Control & Orchestration

| File | Purpose |
|------|---------|
| **qigong-control.sh** | Master control script implementing all 11 refinements |
| QIGONG_SETUP.md | Quick start guide with example workflows |

**→ Run:** `chmod +x qigong-control.sh && ./qigong-control.sh setup`

---

## Documentation Files (In Order of Reading)

### 1. Start Here

| File | Length | Topics |
|------|--------|--------|
| **QIGONG_SUMMARY.md** | ~10 min | Overview of all 11 refinements, architecture, next steps |
| **QIGONG_SETUP.md** | ~15 min | Quick start, example workflows, troubleshooting |

### 2. Deep Dives

| File | Length | Topics |
|------|--------|--------|
| **QIGONG_REFINEMENTS.md** | ~45 min | Complete technical details for all 11 refinements |
| **REFINEMENTS_8_11_TECHNICAL.md** | ~30 min | Ultra-deep specs for refinements 8-11 (physics, code) |

### 3. Tools & Integration

| File | Length | Topics |
|------|--------|--------|
| **QIGONG_UV_INTEGRATION.md** | ~20 min | Modern Python tooling (uv, ruff, uvx) |
| **QIGONG_NIX_MIGRATION.md** | ~15 min | Homebrew → pure Nix migration guide |

### 4. Research & Strategy

| File | Length | Topics |
|------|--------|--------|
| **QIGONG_SUCCESSORS_RESEARCH.md** | ~40 min | 3 successors (DDCS, MCTH, OBAR) with research specs |
| **BEHAVIOR_SPACE_TACTICAL_MODEL.md** | ~35 min | 7 personalities, 5 groups, 5 approaches, 5 black swans |
| **TACTICAL_ADVANTAGE_MAP.md** | ~30 min | 5 advantage zones, competitive matrix, playbooks by player |
| **RAMANUJAN_SPECTRAL_FRAMEWORK.md** | ~40 min | Spectral gap theory, 3×3 mutually exclusive aspects, hyperbolic bulk |
| **COMPLETE_RESEARCH_SYNTHESIS.md** | ~15 min | Overview of all layers (qigong → successors → tactics → spectral) |

---

## Quick Navigation by Task

### "I want to understand qigong at a glance"
1. **QIGONG_SUMMARY.md** (5 min)
2. **QIGONG_SETUP.md** → "Quick Start" section (5 min)

### "I want to set up and run qigong"
1. **QIGONG_SETUP.md** → "Quick Start" (10 min)
2. Activate: `flox activate -d flox-qigong-uv.toml`
3. Run: `flox scripts setup`

### "I want to understand refinement X"
1. **QIGONG_REFINEMENTS.md** → "Refinement X" section
2. For refinements 8-11: **REFINEMENTS_8_11_TECHNICAL.md**

### "I want to use uv/ruff/uvx"
1. **QIGONG_UV_INTEGRATION.md**
2. Run: `flox scripts venv-create && flox scripts install-monitoring`

### "I want to migrate from homebrew"
1. **QIGONG_NIX_MIGRATION.md**
2. File layout: `flox-qigong-uv.toml` (recommended)

### "I want to run an engagement"
1. **QIGONG_SETUP.md** → "Example Workflows" section
2. Use: `./qigong-control.sh <command>`

---

## Refinement Quick Reference

### By Number (1-11)

| # | Name | File | Key Concepts |
|---|------|------|--------------|
| 1 | P/E-Cluster Optimization | QIGONG_REFINEMENTS.md | asitop, heterogeneous cores, polarity |
| 2 | setrlimit Quirks | QIGONG_REFINEMENTS.md | ARM64 limitations, RSS polling |
| 3 | Sandbox Entitlements | QIGONG_REFINEMENTS.md | codesign, privilege broker |
| 4 | Instruments + powermetrics | QIGONG_REFINEMENTS.md | Thermal budget, power monitoring |
| 5 | dyld Resource Accounting | QIGONG_REFINEMENTS.md | Library injection costs, kern.dyld_logging |
| 6 | Jetsam Pressure Relief | QIGONG_REFINEMENTS.md | Memory pressure, cooperative sharing |
| 7 | FSEvents Temporal Accounting | QIGONG_REFINEMENTS.md | Filesystem forensics, I/O costs |
| 8 | QoS Class Steering | REFINEMENTS_8_11_TECHNICAL.md | taskpolicy, Darwin scheduler, DispatchQueue |
| 9 | Thermal Power Modeling | REFINEMENTS_8_11_TECHNICAL.md | P = C×f×V², power budget prediction |
| 10 | Cache Contention | REFINEMENTS_8_11_TECHNICAL.md | 128-byte cache lines, false sharing, c2c |
| 11 | XNU Footprint | REFINEMENTS_8_11_TECHNICAL.md | kern_footprint, memory tracking, compression |

---

## Environment Variables

All defined in flox .toml files and documented in QIGONG_SETUP.md:

```
QIGONG_THERMAL_BUDGET_WATTS = "25"      # Pre-throttle margin
QIGONG_CACHE_LINE_BYTES = "128"         # M-series specific
QIGONG_QOS_BASELINE = "9"                # Background priority baseline
QIGONG_FOOTPRINT_WINDOW = "1000"        # Resource accounting interval (ms)
QIGONG_HOME = "~/.qigong"                # Data directory
UV_PYTHON = "3.12"                       # Python version for uv
UV_CACHE_DIR = "$HOME/.cache/uv"        # uv cache location
```

---

## Flox Scripts Available

### Via `flox scripts` or convenience commands:

```
setup                  Initialize qigong baselines
venv-create           Create uv virtual environment
venv-activate         Activate uv virtual environment
install-monitoring    Install monitoring tools via uv pip
status                Show environment status
lint-scripts          Lint Python scripts with ruff
format-scripts        Format Python scripts with ruff
run-asitop           Run asitop via uvx (isolated)
run-monitoring        Start complete monitoring dashboard
monitor-cores         Monitor P/E core utilization
monitor-power         Monitor power consumption (real-time)
analyze-resources     Analyze resource usage
python-shell         Python 3.12 interactive shell
```

### Run with:
```bash
flox scripts <script-name>
# Or directly via alias:
qigong-<command>     # (if aliases configured)
```

---

## File Organization

### In Repository
```
music-topos/

CORE ENVIRONMENT:
├── flox-qigong-uv.toml              (PRIMARY - use this)
├── flox-qigong-pure-nix.toml        (Alternative)
├── flox-qigong.toml                 (Legacy)
├── qigong-control.sh                (Master script)

DOCUMENTATION (Quick Start):
├── QIGONG_SUMMARY.md                (Overview)
├── QIGONG_SETUP.md                  (Quick start)
├── QIGONG_INDEX.md                  (This file)

DOCUMENTATION (Technical Deep Dives):
├── QIGONG_REFINEMENTS.md            (11 refinements)
├── REFINEMENTS_8_11_TECHNICAL.md   (Deep specs)
├── QIGONG_UV_INTEGRATION.md         (uv/ruff/uvx guide)
├── QIGONG_NIX_MIGRATION.md          (Homebrew migration)

RESEARCH & STRATEGY:
├── QIGONG_SUCCESSORS_RESEARCH.md    (3 successors: DDCS, MCTH, OBAR)
├── BEHAVIOR_SPACE_TACTICAL_MODEL.md (Personalities, groups, approaches, black swans)
├── TACTICAL_ADVANTAGE_MAP.md        (5 advantage zones, competitive playbooks)
├── RAMANUJAN_SPECTRAL_FRAMEWORK.md  (Spectral gap theory, 3×3 aspects, hyperbolic bulk)
└── COMPLETE_RESEARCH_SYNTHESIS.md   (All layers synthesis)

TOTAL: 21 files (5 config + 1 script + 6 core docs + 4 tech docs + 5 research docs)
```

### On User's Machine
```
~/.qigong/
├── logs/                            (Runtime logs)
├── data/                            (Baseline metrics)
├── venv/                            (Python virtual env)
└── reports/                         (Engagement reports)

~/.flox/environments/qigong/         (Cached nix packages)

~/.cache/uv/                         (uv package cache)
```

---

## System Tools (Pre-installed on macOS)

These don't need packages, just PATH configuration:

```
/usr/bin/powermetrics         (Energy monitoring)
/usr/sbin/taskpolicy          (QoS steering)
/usr/sbin/dtrace              (Dynamic tracing)
/Applications/.../Instruments (Xcode profiling)
/Applications/.../Activity Monitor
/Applications/.../Console
/Applications/.../Time Machine
```

---

## Integration Checklist

- [ ] **Understand**: Read QIGONG_SUMMARY.md
- [ ] **Setup**: Run `flox activate` + `flox scripts setup`
- [ ] **Test**: Run example from QIGONG_SETUP.md
- [ ] **Deploy**: Use in red team / blue team exercise
- [ ] **Analyze**: Run `./qigong-control.sh analyze`
- [ ] **Iterate**: Refine based on REFINEMENTS_8_11_TECHNICAL.md

---

## Cross-References

### By Topic

#### Thermal Management
- QIGONG_REFINEMENTS.md → Refinement 4
- REFINEMENTS_8_11_TECHNICAL.md → Refinement 9
- QIGONG_SETUP.md → "Thermal Budget Optimization" workflow

#### Python Development
- QIGONG_UV_INTEGRATION.md → All sections
- flox-qigong-uv.toml → Python package definitions

#### Red Team Evasion
- REFINEMENTS_8_11_TECHNICAL.md → Refinement 8 (QoS hijacking)
- REFINEMENTS_8_11_TECHNICAL.md → Refinement 9 (Power evasion)
- REFINEMENTS_8_11_TECHNICAL.md → Refinement 10 (Cache evasion)
- REFINEMENTS_8_11_TECHNICAL.md → Refinement 11 (Memory hiding)

#### Blue Team Detection
- QIGONG_REFINEMENTS.md → All refinements (detection strategies)
- QIGONG_SETUP.md → "Workflow 2: Cache-Aware Attack Detection"

#### System Architecture
- QIGONG_SUMMARY.md → "System Architecture" section
- REFINEMENTS_8_11_TECHNICAL.md → Refinement 10 (cache hierarchy)

---

## File Statistics

| Category | Files | Total Size | Est. Reading Time |
|----------|-------|-----------|-------------------|
| Core Environment | 4 | ~15 KB | - |
| Scripts | 1 | ~25 KB | - |
| Quick Start Docs | 3 | ~40 KB | ~30 min |
| Technical Deep Dives | 4 | ~110 KB | ~2 hours |
| Research & Strategy | 5 | ~200 KB | ~2.5 hours |
| **Total** | **21** | **~390 KB** | **~5-6 hours** |

---

## Recommended Reading Order

### For First-Time Users (1-2 hours)
1. **QIGONG_SUMMARY.md** (10 min) - Get oriented
2. **QIGONG_SETUP.md** → Quick Start (15 min) - Set up environment
3. **QIGONG_SETUP.md** → Example Workflows (30 min) - Run first test
4. **QIGONG_REFINEMENTS.md** (45 min) - Understand all refinements

### For Deep Understanding (3-4 hours)
1. Above (1-2 hours)
2. **REFINEMENTS_8_11_TECHNICAL.md** (30 min) - Physics & implementation
3. **QIGONG_UV_INTEGRATION.md** (20 min) - Modern tooling
4. **qigong-control.sh** (30 min) - Read source code

### For Operations (30 min)
1. **QIGONG_SETUP.md** → Quick Start (15 min)
2. **QIGONG_SETUP.md** → Example Workflows (15 min)
3. Run: `./qigong-control.sh engage-red 1234`

### For Strategic Understanding (2-3 hours)
1. **QIGONG_SUCCESSORS_RESEARCH.md** (40 min) - Understand 3 successors
2. **BEHAVIOR_SPACE_TACTICAL_MODEL.md** (35 min) - Personality archetypes, groups, approaches, black swans
3. **TACTICAL_ADVANTAGE_MAP.md** (30 min) - Competitive dynamics, who wins when
4. **COMPLETE_RESEARCH_SYNTHESIS.md** (15 min) - All layers overview

### For Mathematical Framework (1-2 hours)
1. **RAMANUJAN_SPECTRAL_FRAMEWORK.md** (40 min) - Spectral graph theory
2. **QIGONG_SUCCESSORS_RESEARCH.md** (40 min) - Technical implementation details
3. Read sources cited in both documents

---

## Getting Help

### Questions About...

**Setup & Installation:**
- → QIGONG_SETUP.md → "Troubleshooting"
- → QIGONG_UV_INTEGRATION.md → "Troubleshooting"

**Specific Refinement:**
- → QIGONG_REFINEMENTS.md → "[Refinement #] Name"
- → REFINEMENTS_8_11_TECHNICAL.md (for 8-11)

**uv/ruff/uvx Usage:**
- → QIGONG_UV_INTEGRATION.md → "[Section]"

**Red Team / Blue Team Workflows:**
- → QIGONG_SETUP.md → "Example Workflows"

**System Architecture:**
- → QIGONG_SUMMARY.md → "System Architecture"
- → REFINEMENTS_8_11_TECHNICAL.md → "Hardware Architecture"

**macOS Integration:**
- → QIGONG_REFINEMENTS.md → "Implementation" sections
- → REFINEMENTS_8_11_TECHNICAL.md → "Technical Implementation"

---

## Version History

| Version | Changes |
|---------|---------|
| 3.0.0 | Added uv, ruff, uvx integration |
| 2.0.0 | Pure Nix (removed homebrew) |
| 1.0.0 | Initial release with 11 refinements |

**Current:** 3.0.0 (uv-based, recommended)

---

## License

qigong is a research tool for authorized security testing only. See **QIGONG_SUMMARY.md** for legal notes.

---

## Next Steps

1. **Quick orientation**: Read QIGONG_SUMMARY.md (5 min)
2. **Hands-on**: Follow QIGONG_SETUP.md Quick Start (15 min)
3. **Deep dive**: Read relevant refinement sections (30 min+)
4. **Practice**: Run example workflows (30 min+)

**Or jump straight in:**
```bash
flox activate -d /Users/bob/ies/music-topos/flox-qigong-uv.toml
flox scripts setup
./qigong-control.sh refinement-1
```

