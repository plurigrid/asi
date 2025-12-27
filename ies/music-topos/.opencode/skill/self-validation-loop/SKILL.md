---
name: self-validation-loop
description: Run self-validation loops for triadic color systems using prediction vs observation and error minimization.
---

# Self-Validation Loop

Use when training or evaluating self-validation for 3-stream color systems.

## Inputs
- seed, indices
- sources: splitmix_ternary, xoroshiro_3color, gay_mcp
- comparator: reafference or comparator

## Workflow
1. Predict expected colors (efference copy).
2. Observe actual colors (color_at or stream generation).
3. Compare predictions with observations.
4. Aggregate accuracy and surprise.

## Gay MCP tools
- gay_seed, efference_copy, color_at, reafference, comparator, active_inference, self_model

## Metrics
- accuracy = matches / total
- surprise = mismatch count or summed error
- pass threshold: accuracy >= 0.99 or surprise == 0

## Output
- JSON log with seed, indices, predicted, observed, errors, accuracy, surprise

## Example prompt
"Run a self-validation loop over indices 1..20 and report accuracy and surprise."
