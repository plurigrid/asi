---
name: reafference-corollary-discharge
description: Von Holst reafference and corollary discharge for behavioral verification and signal processing
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Skill: Reafference & Corollary Discharge (von Holst Neuroscience)

**Category**: Behavioral Verification | Neural Mechanism Implementation
**Level**: Advanced (Requires understanding of: reafference theory, signal processing, corollary discharge)
**Status**: ✓ COMPLETE & OPERATIONAL
**Trit Assignment**: +1 (PLUS) - Active threat detection & signal amplification
**Propagates To**: codex, claude, amp, cursor, copilot

---

## Overview

Implements **von Holst's reafference theory** (1950) - a breakthrough neuroscience principle describing how organisms distinguish self-generated signals from external threats.

**Core Principle**:
> "The brain doesn't passively receive sensory feedback. It actively PREDICTS what feedback should occur and CANCELS it out. Only MISMATCHES between prediction and sensation reach conscious attention."

This skill applies this mechanism to interaction analysis, creating a complete:
1. **Efference Copy** (prediction) generation system
2. **Sensory Reafference** (observation) matching
3. **Comparator** (error signal) computation
4. **Corollary Discharge** (suppression/amplification) mechanism

---

## Key Features

### 1. Efference Copy Generation
- **Input**: Interaction content (file paths, descriptions)
- **Method**: SHA-256 hash → color index mapping (1-5)
- **Output**: Deterministic predicted color for each interaction
- **Property**: Identical predictions for identical inputs

### 2. Sensory Reafference Matching
- **Input**: Observed interaction history from ~/.claude/history.jsonl
- **Method**: Compare predicted vs observed colors
- **Output**: Match score (0.0 = mismatch, 1.0 = perfect match)
- **Property**: TAP state classification (LIVE/VERIFY/BACKFILL)

### 3. Comparator: Error Signal Computation
- **Formula**: `error = expected - actual`
- **Method**: Color distance in 5-color space
- **Output**: Error magnitude (0.0-1.0) and threat level
- **Threat Levels**:
  - **SAFE**: error < 0.01 (99% confidence in prediction)
  - **WARNING**