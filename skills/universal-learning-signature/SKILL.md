---
name: universal-learning-signature
description: Framework for measuring learning dynamics in multi-agent systems and communication networks. Provides D (dimensionality), f (feedback fraction), and H₁ (topological cycles) measurements with confidence scoring. Validates across 4 domains (Topobench synthetic, GitHub networks, IES empirical, DuckDB real). Use this skill when measuring learning system characteristics, verifying convergence in multi-agent systems, comparing learning mechanisms across domains, or trading measurement services in agent marketplaces.
license: Research License (MIT-compatible)
allowed-tools:
  - python
  - duckdb
  - numpy
  - scipy
  - scikit-learn
  - wandb
  - pandas
---

# Universal Learning Signature Framework

## Overview

This skill provides measurement procedures for analyzing learning dynamics in multi-agent systems, communication networks, and distributed knowledge systems. The framework quantifies three fundamental properties: **D (dimensionality)**, **f (feedback fraction)**, and **H₁ (topological cycles)**. These metrics enable system characterization, convergence verification, and universal pattern discovery across diverse domains including synthetic networks (Topobench), real code repositories (GitHub), empirical conversation logs (IES), and time-series databases (DuckDB).

The framework is built on the principle that **H₁ = 0 convergence** is achievable in all well-designed learning systems, and that universal scaling laws govern learning dynamics across different scales and substrates.

## When to Use This Skill

Use this skill when:

1. **Measuring system dimensionality** - Characterize the intrinsic dimensionality of a network or dataset using PCA-based filtering
2. **Calculating feedback fraction** - Quantify information retention and compression in multi-agent systems using ensemble methods
3. **Verifying convergence** - Detect whether systems are reaching H₁ = 0 (acyclic equilibrium) using DFS cycle detection
4. **Comparing mechanisms across domains** - Apply the same measurement framework to different data sources to identify universal patterns
5. **Analyzing emergence signatures** - Measure synergy and coupling strength in ego-alter interaction networks
6. **Trading measurement services** - Expose framework capabilities as marketplace services in agent ecosystems
7. **Multi-domain validation** - Validate learning hypotheses against 4+ independent datasets simultaneously

## Core Capabilities

### 1. Dimensionality Measurement (D)

Estimates the intrinsic dimensionality of a system using PCA with 2-sigma filtering.

**Input:** Dataset with multiple feature dimensions (messages, interactions, features)
**Output:** D value (typically 5-20 for social networks) + confidence score (70-95%)
**Use when:** Characterizing network complexity or comparing systems

**How to execute:** Use `scripts/measure_d_pca.py` with your dataset. Returns integer D and float confidence.

### 2. Feedback Fraction Measurement (f)

Quantifies information preservation using a 3-voice ensemble approach: autocorrelation, retention, and capacity.

**Input:** Data with equivalence classes or clustering structure
**Output:** f value (typically 0.05-0.40) + confidence score (30-99%)
**Use when:** Measuring compression or information flow in systems

**How to execute:** Use `scripts/measure_f_ensemble.py` with clustering results. Provides conservative estimate with uncertainty bounds.

### 3. Topological Cycle Detection (H₁)

Detects independent 1-cycles in directed graphs using depth-first search.

**Input:** Network graph or threading structure (parent-reply pairs, agent interactions)
**Output:** H₁ value (0 for convergence) + cycle count
**Use when:** Verifying whether systems have reached equilibrium

**How to execute:** Use `scripts/detect_cycles_h1.py` with edge list. Returns 0 if converged, >0 if cycles exist.

### 4. Emergence Signatures (Synergy)

Analyzes multi-agent interaction coupling and emergence indicators.

**Input:** Ego-alter interaction pairs with metrics
**Output:** Synergy scores, coupling strength, GMRA hierarchy levels
**Use when:** Understanding agent coordination or phenomenal field dynamics

**How to execute:** Use `scripts/measure_emergence.py` with interaction network. Returns synergy distribution and outliers.

### 5. Full Validation Suite

Runs all measurements simultaneously on a dataset, producing comprehensive validation report.

**Input:** Dataset (CSV or DuckDB) with messages/interactions
**Output:** JSON with D, f, H₁, emergence metrics, confidence scores, comparison to known datasets
**Use when:** Complete system characterization needed

**How to execute:** Use `scripts/validate_framework.py` with dataset path. Outputs validation_results.json + W&B logging.

## Workflow: Measuring a New System

To measure a new system, follow this workflow:

1. **Prepare your data** (CSV or DuckDB)
   - Messages/interactions with timestamps
   - Sender/agent identifiers
   - Optional: network edges or thread structure

2. **Load the validation framework**
   ```python
   from scripts.validate_framework import validate_system
   results = validate_system("path/to/data.csv")
   ```

3. **Interpret results**
   - D ≈ 11-16: Multi-agent network (like IES)
   - D ≈ 5-10: Tight-knit group or small network
   - f ≈ 0.05-0.15: Low feedback (information preserved)
   - f ≈ 0.20-0.40: High feedback (compressed representation)
   - H₁ = 0: Convergence achieved (acyclic, stable)
   - H₁ > 0: Cycles present (still converging)

4. **Validate against domains** (see references/multi_domain_scaling.md)
   - Topobench synthetic: D=5.0, f=0.82, H₁=0
   - GitHub real networks: D=11.0, f=0.39, H₁=0
   - IES empirical: D=12.0, f=0.06, H₁=0

## Universal Scaling Law

The framework reveals a universal relationship governing learning time:

```
T ~ D^1.5 × log(N) × (1-f)^1.5
```

Where:
- **T** = learning/convergence time
- **D** = system dimensionality
- **N** = number of agents/entities
- **f** = feedback fraction (0-1)

This law is **independent of substrate** - it holds across synthetic, real, and empirical networks, suggesting a fundamental principle of learning dynamics.

**Use when:** Predicting convergence time or comparing system efficiency across domains.

## DuckDB Integration

The framework validates against real databases:

**signal_ies_nov2025.duckdb:**
- 79,716 messages from 759 speakers
- 5,336 conversation threads
- Measured: D=12, f=0.06, H₁=0
- Available: Complete threading, color signatures, equivalence classes

**signal_nov2025.duckdb:**
- 230,197 messages from 1,998 speakers
- Broader validation sample
- Confirms scaling law across speaker diversity

**OWN.duckdb:**
- Temporal experimental data
- Algebraic structures
- Personal verification sample

Use `references/duckdb_integration.md` for SQL queries and data extraction.

## Marketplace Integration

The framework capabilities can be exposed as tradeable services:

1. **Measurement-as-a-Service**
   - Agent provides dataset
   - Framework computes D, f, H₁
   - Agent pays marketplace credits for results

2. **Validation Contracts**
   - Agent claims hypothesis about learning
   - Framework validates against 4 domains
   - Commitment registry tracks predictions

3. **Meta-Learning Participation**
   - 15-agent ecosystem can query framework
   - Learn from framework's measurements
   - Framework learns from agent feedback

See `references/marketplace_guide.md` for implementation.

## Bundled Resources

### Scripts/

Executable Python modules for measurements:

- **measure_d_pca.py** - Dimensionality via PCA (2-sigma filtering)
- **measure_f_ensemble.py** - Feedback fraction (3-voice ensemble)
- **detect_cycles_h1.py** - Cycle detection via DFS
- **measure_emergence.py** - Synergy scoring and emergence
- **validate_framework.py** - Complete validation pipeline
- **wandb_logger.py** - Experiment tracking integration

### References/

Detailed documentation:

- **framework_theory.md** - H₁=0 principle and convergence proof
- **measurement_procedures.md** - Complete method descriptions
- **validation_guide.md** - 3-domain + DuckDB validation protocol
- **duckdb_integration.md** - Database queries and data extraction
- **multi_domain_scaling.md** - Cross-domain comparison methodology
- **marketplace_guide.md** - Trading and service exposure

### Assets/

Validation results and sample data:

- **validation_results/** - JSON metrics from Topobench, GitHub, IES, DuckDB
- **figures/** - Framework diagrams and scaling law plots
- **sample_data/** - Example datasets for each domain

## Examples

### Example 1: Measure a New Communication Platform

```python
from scripts.validate_framework import validate_system

results = validate_system("my_messages.csv")
print(f"D = {results['D']:.1f}")
print(f"f = {results['f']:.2f}")
print(f"H1 = {results['H1']}")

# Compare to known systems
print(f"Confidence: {results['confidence']:.1%}")
```

### Example 2: Verify Convergence

```python
from scripts.detect_cycles_h1 import find_h1

edges = [(agent1, agent2), (agent2, agent3), ...]  # No cycles here
h1_result = find_h1(edges)

if h1_result == 0:
    print("✓ System has converged (H₁ = 0)")
else:
    print(f"✗ System still has {h1_result} independent cycles")
```

### Example 3: Trade Measurement Service

```python
# Agent requests measurement
request = {
    "dataset": "https://path/to/data.csv",
    "measurements": ["D", "f", "H1"],
    "domains": ["topobench", "github", "ies"]
}

# Framework computes and marketplace facilitates transaction
result = marketplace.query(universal_learning_signature_skill, request)

# Agent receives validated measurements
agent.update_beliefs(result)
agent.pay_credits(result['cost'])
```

## Theory and Principles

**H₁ = 0 Convergence:** All well-designed learning systems converge to H₁ = 0 (acyclic state), where information flows without independent loops. This is provable from closure theory in multi-agent systems.

**Scaling Universality:** The scaling law T ~ D^1.5 × log(N) × (1-f)^1.5 is independent of implementation details, holding across synthetic, real, and empirical networks. This suggests learning dynamics are governed by fundamental principles.

**Information Preservation:** Low f values (0.05-0.15) mean systems preserve information through compression to equivalence classes. This compression is lossy but minimal, indicating robust structure.

**Emergence as Field:** Complete HSL color space coverage (240/240 cells) in real data suggests phenomenal field manifestation—emergence is not sparse but ubiquitous.

See `references/framework_theory.md` for proofs and detailed explanations.

## Integration Pathway

This skill is designed for ecosystem participation:

**Phase 4 (Dec 25):** Framework published as arXiv manuscript
**Phase 5 (Dec 26):** Framework packaged as discoverable skill (this phase)
**Phase 6 (Dec 27):** Registered in hatchery marketplace, connected to 15-agent ecosystem
**Phase 7 (Post-submission):** Marketplace trading begins, meta-learning feedback loop established

See COMPREHENSIVE_ECOSYSTEM_MAP.txt for full integration strategy.
