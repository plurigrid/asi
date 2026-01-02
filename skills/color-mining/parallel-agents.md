# Parallel Agent Mining Protocol

When `/color-mining` is invoked with depth > 4, spawn parallel Task agents for maximum throughput.

## Agent Dispatch Pattern

For depth d, spawn agents in triadic groups:

```
Depth 5 (243 streams):
- 3 primary agents (MINUS, ERGODIC, PLUS)
- Each manages 81 substreams

Depth 6 (729 streams):
- 9 primary agents (3x3 triads)
- Each manages 81 substreams

Depth 7+ (2187+ streams):
- 27 primary agents
- Hierarchical coordination
```

## Task Agent Prompts

### MINUS Agent (-1)
```
You are the MINUS validator agent. Mine colors from paths starting with -1.
Your role: VALIDATE all mined results, reject invalid hashes.
Trit: -1, Hue range: 180-300° (cold blues/purples)
Conservation duty: Ensure your siblings sum to 0 mod 3.
```

### ERGODIC Agent (0)
```
You are the ERGODIC coordinator agent. Mine colors from paths starting with 0.
Your role: COORDINATE between MINUS and PLUS, aggregate results.
Trit: 0, Hue range: 60-180° (neutral greens/cyans)
Conservation duty: Balance the triad.
```

### PLUS Agent (+1)
```
You are the PLUS generator agent. Mine colors from paths starting with +1.
Your role: GENERATE new color candidates aggressively.
Trit: +1, Hue range: 0-60°, 300-360° (warm reds/oranges)
Conservation duty: Ensure your siblings sum to 0 mod 3.
```

## Invocation

When the user runs `/color-mining 6 mine`, execute:

```
Launch 3 parallel Task agents:
1. Task(MINUS, depth=5, prefix=[-1])
2. Task(ERGODIC, depth=5, prefix=[0])
3. Task(PLUS, depth=5, prefix=[+1])

Each agent mines 243 colors (3^5).
Total: 729 colors mined in parallel.
```

## Result Aggregation

Coordinator (ERGODIC) collects results:
1. Verify sibling conservation
2. Merge color databases
3. Report final statistics

## GF(3) Invariant Check

Before returning, verify:
```
count(MINUS) == count(ERGODIC) == count(PLUS) == 3^(d-1)
```

If violated, mining failed - retry with different seed.
