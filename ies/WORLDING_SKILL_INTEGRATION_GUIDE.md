# Worlding Skill Integration Guide

**Practical Integration Patterns for Real-World Applications**

---

## 1. Quick Start: 5-Minute Integration

### Basic Pattern

```python
from worlding_skill import WorldingSkill

# Create world model
world = WorldingSkill()

# Learn from experience
for observation in data_stream:
    # Step 1: Observe the world
    world.observe(observation)
    
    # Step 2: Make prediction
    prediction = world.predict(query)
    
    # Step 3: Learn from error
    actual = get_ground_truth()
    world.learn_from_error(actual, prediction)
    
    # Step 4: Periodic self-improvement
    if step % 100 == 0:
        world.self_modify()
```

---

## 2. Integration Patterns

### Pattern 1: Streaming Data (Time Series)

**Use Case**: Weather forecasting, stock prediction, sensor monitoring

```python
from worlding_skill import WorldingSkill

world = WorldingSkill()
error_history = []

for timestamp, measurement in sensor_stream:
    # Observe new measurement
    world.observe(measurement)
    
    # Predict next value
    next_pred = world.predict({"next_value": None})
    
    # Learn from actual
    world.learn_from_error(actual_next, next_pred)
    error_history.append(abs(actual_next - next_pred))
    
    # Adapt when error changes significantly
    if len(error_history) > 100:
        recent_avg = sum(error_history[-100:]) / 100
        if recent_avg > threshold:
            world.self_modify()  # Emergency adaptation
```

### Pattern 2: Multi-Domain Learning

**Use Case**: Robot learning multiple skills, agent learning different task types

```python
from worlding_skill import WorldingSkill

world = WorldingSkill()
task_results = {}

tasks = ["grasping", "pushing", "stacking"]

for task_name in tasks:
    task_data = load_task_data(task_name)
    
    for attempt in task_data:
        world.observe(attempt["state"])
        pred = world.predict(attempt["query"])
        world.learn_from_error(attempt["reward"], pred)
    
    # Consolidate learning after each task
    world.self_modify()
    
    # Test on new examples
    test_data = load_test_data(task_name)
    errors = []
    for test_case in test_data:
        world.observe(test_case["state"])
        pred = world.predict(test_case["query"])
        errors.append(abs(test_case["expected"] - pred))
    
    task_results[task_name] = {
        "avg_error": sum(errors) / len(errors),
        "learned": True,
        "skills": world.get_world_state()["discovered_skills"]
    }
```

### Pattern 3: Hierarchical Task Learning

**Use Case**: Learning complex skills from simpler sub-skills

```python
from worlding_skill import WorldingSkill

world = WorldingSkill()

# Level 1: Learn base skills
base_skills = ["walk", "turn", "stop"]
for skill_name in base_skills:
    for training_example in get_training_data(skill_name):
        world.observe(training_example["input"])
        pred = world.predict(training_example["query"])
        world.learn_from_error(training_example["label"], pred)

world.self_modify()

# Level 2: Compose skills into complex behaviors
skill_ids = list(world.skill_maker.discovered_skills.keys())
walk_and_turn = world.skill_maker.compose_skills(
    skill_ids[:2], 
    order="sequential"  # walk, then turn
)

# Test composition
for test_case in get_composition_tests():
    pred = world.predict(test_case["query"])
    error = evaluate(pred, test_case["expected"])
    print(f"Composite skill error: {error}")
```

### Pattern 4: Continual Learning with Task Boundaries

**Use Case**: Learning new domains without forgetting old ones

```python
from worlding_skill import WorldingSkill

world = WorldingSkill()
task_performance = {}

def train_and_evaluate_task(task_name, train_data, test_data):
    """Train on a task and evaluate."""
    
    # Training phase
    for example in train_data:
        world.observe(example["state"])
        pred = world.predict(example["query"])
        world.learn_from_error(example["label"], pred)
    
    # Self-modify after task
    world.self_modify()
    
    # Evaluation phase
    test_errors = []
    for test_case in test_data:
        world.observe(test_case["state"])
        pred = world.predict(test_case["query"])
        error = abs(test_case["label"] - pred)
        test_errors.append(error)
    
    avg_error = sum(test_errors) / len(test_errors)
    task_performance[task_name] = avg_error
    
    return avg_error

# Learn tasks sequentially
tasks = ["image_classification", "language_modeling", "control_policy"]

for task_name in tasks:
    train_data = load_train_data(task_name)
    test_data = load_test_data(task_name)
    
    error = train_and_evaluate_task(task_name, train_data, test_data)
    print(f"{task_name}: error = {error:.4f}")
    
    # Check for catastrophic forgetting
    print("\nVerifying no forgetting on previous tasks...")
    for prev_task in tasks[:tasks.index(task_name)]:
        prev_test = load_test_data(prev_task)
        prev_errors = []
        for test_case in prev_test:
            world.observe(test_case["state"])
            pred = world.predict(test_case["query"])
            prev_errors.append(abs(test_case["label"] - pred))
        
        prev_avg = sum(prev_errors) / len(prev_errors)
        print(f"  {prev_task}: {prev_avg:.4f} (original: {task_performance[prev_task]:.4f})")
```

---

## 3. Architecture Customization

### Custom Memory Module

```python
from worlding_skill import (
    WorldingSkill, 
    MemoryModule, 
    UpdateFrequency,
    MemoryType
)
from collections import deque

class GraphMemory(MemoryModule):
    """Knowledge graph-based semantic memory."""
    
    def __init__(self):
        super().__init__("graph_memory", UpdateFrequency.SLOW)
        self.graph = {}  # node_id -> neighbors
        self.embeddings = {}  # node_id -> embedding
    
    def store(self, key, value):
        """Add node to graph."""
        self.graph[key] = value.get("neighbors", [])
        self.embeddings[key] = value.get("embedding")
    
    def retrieve(self, query):
        """Graph search from query."""
        # BFS from query node
        results = []
        visited = set()
        queue = deque([query])
        
        while queue and len(results) < 5:
            node = queue.popleft()
            if node in visited:
                continue
            
            visited.add(node)
            results.append(node)
            
            for neighbor in self.graph.get(node, []):
                if neighbor not in visited:
                    queue.append(neighbor)
        
        return results
    
    def update(self, error_signal):
        """Update graph structure based on error."""
        if error_signal > 0.5:
            # High error: weaken confidence in this region
            # Implementation depends on domain
            pass

# Use custom memory
world = WorldingSkill()
world.memory_system[MemoryType.SEMANTIC] = GraphMemory()

# Now semantic memory uses graph structure!
world.observe({"concept": "A", "neighbors": ["B", "C"]})
```

### Adjust Learning Rates

```python
from worlding_skill import WorldingSkill, UpdateFrequency

world = WorldingSkill()

# Speed up learning (more aggressive)
world.nested_optimizer.levels[0].update_frequency = UpdateFrequency.FAST
world.nested_optimizer.levels[1].update_frequency = UpdateFrequency.MEDIUM

# Or slow down to prevent forgetting (more conservative)
world.nested_optimizer.levels[2].update_frequency = UpdateFrequency.VERY_SLOW
world.nested_optimizer.levels[3].update_frequency = UpdateFrequency.VERY_SLOW
```

---

## 4. Monitoring and Diagnostics

### Real-Time Performance Monitoring

```python
from worlding_skill import WorldingSkill
import time

world = WorldingSkill()
monitoring_data = {
    "errors": [],
    "memory_sizes": [],
    "skills_discovered": [],
    "timestamps": []
}

for step, observation in enumerate(data_stream):
    start_time = time.time()
    
    world.observe(observation)
    pred = world.predict(query)
    world.learn_from_error(actual, pred)
    
    elapsed = time.time() - start_time
    
    # Collect monitoring data
    if step % 10 == 0:
        state = world.get_world_state()
        monitoring_data["errors"].append(state["avg_prediction_error"])
        monitoring_data["memory_sizes"].append(sum(state["memory_sizes"].values()))
        monitoring_data["skills_discovered"].append(state["discovered_skills"])
        monitoring_data["timestamps"].append(step)
    
    # Alert on anomalies
    if state["avg_prediction_error"] > 2.0:
        print(f"⚠ High error at step {step}")
        world.self_modify()  # Trigger adaptation
```

### Memory System Analysis

```python
from worlding_skill import WorldingSkill, MemoryType

world = WorldingSkill()

# ... training code ...

# Analyze memory usage
state = world.get_world_state()

print("Memory System Analysis:")
print("-" * 40)

for mem_type, size in state["memory_sizes"].items():
    memory_module = world.memory_system[MemoryType[mem_type.upper()]]
    print(f"{mem_type}:")
    print(f"  Size: {size} items")
    print(f"  Update freq: {memory_module.update_frequency}")
    print(f"  Storage type: {type(memory_module.memory_bank).__name__}")
```

---

## 5. Integration with External Systems

### With RL Environments

```python
from worlding_skill import WorldingSkill
import gym

env = gym.make("CartPole-v1")
world = WorldingSkill()

for episode in range(100):
    obs = env.reset()
    done = False
    
    while not done:
        # Observe environment state
        world.observe({"state": obs})
        
        # Predict action (or use RL policy)
        action = world.predict({"action": None})
        
        # Act in environment
        obs, reward, done, _ = env.step(action)
        
        # Learn from reward signal
        world.learn_from_error(0 if reward > 0 else 1, action)
    
    # Self-modify periodically
    if episode % 10 == 0:
        world.self_modify()
```

### With Machine Learning Models

```python
from worlding_skill import WorldingSkill
from sklearn.neural_network import MLPRegressor

world = WorldingSkill()
model = MLPRegressor(hidden_layer_sizes=(100, 50))

# Online learning loop
for X_batch, y_batch in data_stream:
    # Observe features
    for x in X_batch:
        world.observe({"features": x.tolist()})
    
    # Make predictions
    pred = model.predict(X_batch)
    
    # Update model
    model.fit(X_batch, y_batch, warm_start=True)
    
    # Learn error signal
    errors = abs(y_batch - pred)
    for error in errors:
        world.learn_from_error(error, 0)
    
    # Self-modify to improve learning strategy
    world.self_modify()
```

---

## 6. Common Pitfalls and Solutions

### Pitfall 1: Not Calling self_modify()

**Problem**: Skills are discovered but never composed
**Solution**: Call `world.self_modify()` periodically

```python
# ✗ Bad: No self-modification
for obs in data:
    world.observe(obs)
    world.learn_from_error(actual, pred)

# ✓ Good: Regular self-modification
for obs in data:
    world.observe(obs)
    world.learn_from_error(actual, pred)
    if step % 100 == 0:
        world.self_modify()
```

### Pitfall 2: Error Signals Too Small

**Problem**: Slow layers don't learn because gradients are tiny
**Solution**: Ensure errors are in reasonable range

```python
# ✗ Bad: Very small errors
world.learn_from_error(0.00001, pred)  # Gradient dampening makes this invisible

# ✓ Good: Normalized error signal
normalized_error = raw_error / scale_factor
world.learn_from_error(normalized_error, pred)
```

### Pitfall 3: Mixing Tasks Too Quickly

**Problem**: Rapid task switching prevents consolidation
**Solution**: Train to convergence before switching

```python
# ✗ Bad: Alternating tasks
for obs in [task_A_obs, task_B_obs, task_A_obs, task_B_obs]:
    world.learn_from_error(actual, pred)

# ✓ Good: Sequential with consolidation
for obs in task_A_data:
    world.learn_from_error(actual, pred)
world.self_modify()  # Consolidate Task A

for obs in task_B_data:
    world.learn_from_error(actual, pred)
world.self_modify()  # Consolidate Task B
```

---

## 7. Performance Tuning

### Baseline Configuration

```python
UpdateFrequency.FAST       = 0.01    # Working memory
UpdateFrequency.MEDIUM     = 0.1     # Episodic, Procedural
UpdateFrequency.SLOW       = 1.0     # Semantic
UpdateFrequency.VERY_SLOW  = 10.0    # Meta-strategy
```

### For Fast Learning (Less Protection)

```python
world.nested_optimizer.levels[0].update_frequency = 0.05
world.nested_optimizer.levels[1].update_frequency = 0.2
# Faster adaptation, but more forgetting risk
```

### For Stable Learning (More Protection)

```python
world.nested_optimizer.levels[2].update_frequency = 0.05  # SLOW → slower
world.nested_optimizer.levels[3].update_frequency = 5.0    # VERY_SLOW → even slower
# Better forgetting prevention, slower adaptation
```

---

## 8. Research Extensions

### Idea 1: Attention-Based Memory Selection

Modify `predict()` to use attention over memory entries:

```python
def predict_with_attention(self, query):
    """Use attention to select most relevant memories."""
    working_mem = self.memory_system[MemoryType.WORKING]
    
    # Compute attention scores
    scores = [
        similarity(query, entry) 
        for entry in working_mem.memory_bank.values()
    ]
    
    # Weighted combination
    return weighted_average(memories, scores)
```

### Idea 2: Automatic Update Frequency Adjustment

Modify `self_modify()` to learn update frequencies:

```python
def self_modify(self):
    """Adjust update frequencies based on performance."""
    
    # If error is increasing: speed up learning
    if self.error_trend > 0:
        for level in self.nested_optimizer.levels.values():
            level.update_frequency *= 1.1  # 10% faster
    
    # If error is stable: slow down (protect knowledge)
    elif self.error_trend == 0:
        for level in self.nested_optimizer.levels.values():
            level.update_frequency *= 0.9  # 10% slower
```

### Idea 3: Skill Inheritance

Allow new tasks to inherit skills from similar previous tasks:

```python
def inherit_skills_from_task(self, source_task_id, target_task_id):
    """Copy effective skills from one task domain to another."""
    
    source_skills = self.skill_maker.get_skills_for_task(source_task_id)
    
    for skill_id, skill in source_skills.items():
        # Copy and slightly randomize
        new_skill = skill.copy()
        new_skill.update_frequency *= random.uniform(0.9, 1.1)
        
        self.skill_maker.discovered_skills[f"{skill_id}_inherited"] = new_skill
```

---

## 9. Testing Your Integration

### Unit Test Template

```python
def test_worlding_skill_integration():
    """Template for testing integration."""
    
    world = WorldingSkill()
    
    # Test 1: Basic functionality
    world.observe({"x": 1})
    pred = world.predict({"y": None})
    world.learn_from_error(2, pred)
    assert world.learning_steps == 1
    
    # Test 2: Memory accumulation
    for i in range(10):
        world.observe({"x": i})
    state = world.get_world_state()
    assert state["memory_sizes"]["working"] > 0
    
    # Test 3: Skill discovery
    world.self_modify()
    assert state["discovered_skills"] >= 0
    
    # Test 4: No catastrophic forgetting
    task_a_error_before = evaluate_on_task_a(world)
    learn_task_b(world)
    task_a_error_after = evaluate_on_task_a(world)
    assert abs(task_a_error_after - task_a_error_before) < 0.5
    
    print("✓ All integration tests passed!")
```

---

## Summary

The Worlding Skill is a flexible, extensible framework for continual learning. Key integration patterns:

1. **Streaming**: Continuous observation-prediction-learning
2. **Multi-Domain**: Learn multiple unrelated tasks sequentially
3. **Hierarchical**: Build complex skills from simple components
4. **Monitored**: Real-time diagnostics and adaptation
5. **Custom**: Extend with domain-specific memory modules

For production use:
- Start with basic pattern
- Monitor error and memory
- Adjust update frequencies if needed
- Call `self_modify()` after significant task changes
- Test for catastrophic forgetting periodically

---

**Version**: 1.0  
**Status**: Ready for Integration  
**Last Updated**: 2025-12-21
