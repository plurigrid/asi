---
name: skill-evolution
description: Patterns for evolutionarily robust skills that adapt across agent generations. Darwin-Godel machine principles for self-improving skill ecosystems.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Skill Evolution

Self-improving skill ecosystems via evolutionary pressure.

## Core Principle

Skills that survive across agent generations share:
1. **Minimal coupling** to specific agent implementations
2. **Clear fitness signals** via validation
3. **Mutation-friendly structure** for iteration
4. **Selection pressure** from cross-platform use

## Evolutionary Fitness Metrics

### 1. Compatibility Score

```python
def compatibility_score(skill_dir):
    validators = [
        ("codex-rs", run_codex_validator),
        ("claude-code", run_claude_validator),
        ("skills-ref", run_agentskills_validator),
    ]
    passed = sum(1 for _, v in validators if v(skill_dir))
    return passed / len(validators)
```

Target: 1.0 (passes all validators)

### 2. Activation Rate

```sql
SELECT skill_name, 
       COUNT(*) as activations,
       AVG(success_rate) as effectiveness
FROM skill_usage
GROUP BY skill_name
ORDER BY activations DESC
```

Skills with low activation → candidates for mutation or extinction.

### 3. Token Efficiency

```python
def token_efficiency(skill):
    tokens_used = count_tokens(skill.body)
    task_success = measure_task_completion(skill)
    return task_success / tokens_used
```

Smaller skills that accomplish tasks = higher fitness.

## Mutation Operators

### 1. Description Refinement

```yaml
# Before (vague)
description: Helps with databases

# After (specific triggers)
description: Design PostgreSQL schemas, write migrations, optimize queries. Use for database design, schema changes, or query performance issues.
```

### 2. Body Compression

```markdown
# Before: 800 lines
[verbose explanations...]

# After: 200 lines + references/
See [detailed API](references/API.md) for complete documentation.
```

### 3. Triadic Rebalancing

When a skill drifts from its trit assignment:

```yaml
# Was ERGODIC (0) but became too generative
metadata:
  trit: 0  # Review: should this be +1?
```

### 4. Cross-Pollination

Combine successful patterns fro