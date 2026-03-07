---
name: "AgentDB Learning Plugins"
description: "Create and train RL learning plugins with AgentDB's plugin system."
---

# AgentDB Learning Plugins

## CLI Quick Start

```bash
# Interactive wizard
npx agentdb@latest create-plugin

# Use specific template
npx agentdb@latest create-plugin -t decision-transformer -n my-agent

# Preview without creating
npx agentdb@latest create-plugin -t q-learning --dry-run

# Custom output directory
npx agentdb@latest create-plugin -t actor-critic -o ./plugins

# List available templates
npx agentdb@latest list-templates

# List installed plugins
npx agentdb@latest list-plugins

# Get plugin info
npx agentdb@latest plugin-info my-agent
```

---

## API Quick Start

```typescript
import { createAgentDBAdapter } from 'agentic-flow/reasoningbank';

const adapter = await createAgentDBAdapter({
  dbPath: '.agentdb/learning.db',
  enableLearning: true,
  enableReasoning: true,
  cacheSize: 1000,
});
```

---

## Algorithm Templates and Configs

### 1. Decision Transformer (Recommended)

Offline RL -- learns from logged experiences without online interaction.

```bash
npx agentdb@latest create-plugin -t decision-transformer -n dt-agent
```

```json
{
  "algorithm": "decision-transformer",
  "model_size": "base",
  "context_length": 20,
  "embed_dim": 128,
  "n_heads": 8,
  "n_layers": 6
}
```

### 2. Q-Learning

Off-policy, value-based. Best for discrete action spaces.

```bash
npx agentdb@latest create-plugin -t q-learning -n q-agent
```

```json
{
  "algorithm": "q-learning",
  "learning_rate": 0.001,
  "gamma": 0.99,
  "epsilon": 0.1,
  "epsilon_decay": 0.995
}
```

### 3. SARSA

On-policy, value-based. More conservative than Q-Learning -- better for safety-critical tasks.

```bash
npx agentdb@latest create-plugin -t sarsa -n sarsa-agent
```

```json
{
  "algorithm": "sarsa",
  "learning_rate": 0.001,
  "gamma": 0.99,
  "epsilon": 0.1
}
```

### 4. Actor-Critic

Policy gradient with value baseline. Works for continuous and discrete action spaces.

```bash
npx agentdb@latest create-plugin -t actor-critic -n ac-agent
```

```json
{
  "algorithm": "actor-critic",
  "actor_lr": 0.001,
  "critic_lr": 0.002,
  "gamma": 0.99,
  "entropy_coef": 0.01
}
```

### 5. Curiosity-Driven

```bash
npx agentdb@latest create-plugin -t curiosity-driven -n curious-agent
```

### Templates 5-9

Also available via `list-templates`: `active-learning`, `adversarial-training`, `curriculum-learning`, `federated-learning`, `multi-task-learning`. These have no dedicated CLI template flag -- use the interactive wizard (`create-plugin` with no `-t`).

---

## Training Workflow

### Store Experiences

```typescript
await adapter.insertPattern({
  id: '',
  type: 'experience',
  domain: 'task-domain',
  pattern_data: JSON.stringify({
    embedding: await computeEmbedding(JSON.stringify(step)),
    pattern: {
      state: step.state,
      action: step.action,
      reward: step.reward,
      next_state: step.next_state,
      done: step.done,
    },
  }),
  confidence: step.reward > 0 ? 0.9 : 0.5,
  usage_count: 1,
  success_count: step.reward > 0 ? 1 : 0,
  created_at: Date.now(),
  last_used: Date.now(),
});
```

### Train

```typescript
const metrics = await adapter.train({
  epochs: 100,
  batchSize: 64,
  learningRate: 0.001,
  validationSplit: 0.2,
});
// Returns: { loss, valLoss, duration, epochs }
```

### Evaluate

```typescript
const result = await adapter.retrieveWithReasoning(testQuery, {
  domain: 'task-domain',
  k: 10,
  synthesizeContext: true,
});
const suggestedAction = result.memories[0].pattern.action;
const confidence = result.memories[0].similarity;
```

---

## Prioritized Experience Replay

```typescript
// Store with TD error as priority
await adapter.insertPattern({
  // ... standard fields
  confidence: tdError,  // TD error = priority
});

// Retrieve only high-priority experiences
const highPriority = await adapter.retrieveWithReasoning(queryEmbedding, {
  domain: 'task-domain',
  k: 32,
  minConfidence: 0.7,
});
```

---

## Multi-Agent Training

```typescript
for (const agent of agents) {
  const experience = await agent.step();
  await adapter.insertPattern({
    domain: `multi-agent/${agent.id}`,
    // ... experience data
  });
}

await adapter.train({ epochs: 50, batchSize: 64 });
```

---

## Combined Learning + Reasoning

```typescript
await adapter.train({ epochs: 50, batchSize: 32 });

const result = await adapter.retrieveWithReasoning(queryEmbedding, {
  domain: 'decision-making',
  k: 10,
  useMMR: true,
  synthesizeContext: true,
  optimizeMemory: true,
});
```

---

## Troubleshooting

**Not converging**: Lower `learningRate` (try `0.0001`).

**Overfitting**: Add `validationSplit: 0.2`, enable `optimizeMemory: true` to consolidate patterns.

**Slow training**: Enable quantization (`quantizationType: 'binary'`).
