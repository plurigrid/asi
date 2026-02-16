# momentum-field Skill

**Trit**: 0 (ERGODIC - transports excellence between validator and generator)
**Color**: Yellow (#F5A623)
**Role**: COORDINATOR in the excellence triad

## Canonical Triad

```
excellence-gradient (-1) ⊗ momentum-field (0) ⊗ refuse-mediocrity (+1) = 0 ✓
     VALIDATOR              COORDINATOR              GENERATOR
   (measures delta)      (transports flow)        (raises floor)
```

## Core Definition

**Momentum** = derivative of progress with respect to time

```
p = progress (shipped value)
v = dp/dt    (velocity - shipping rate)
a = dv/dt    (acceleration - velocity change)
j = da/dt    (jerk - smoothness of acceleration)
```

## Flow State Detection

Based on Csikszentmihalyi's flow theory, detect via interaction patterns:

```python
@dataclass
class FlowState:
    challenge_skill_ratio: float  # Optimal: 0.9-1.1
    clear_goals: bool             # Unambiguous next action
    immediate_feedback: bool      # Know if progressing
    deep_concentration: float     # Interruption-free time (hours)
    sense_of_control: bool        # Agency over outcome
    time_distortion: bool         # Hours feel like minutes
    
def detect_flow(interactions: List[Interaction]) -> FlowState:
    """Flow = high challenge + high skill + low friction."""
    burst_lengths = [len(burst) for burst in segment_bursts(interactions)]
    avg_burst = mean(burst_lengths)
    
    return FlowState(
        challenge_skill_ratio=estimate_challenge_skill(interactions),
        clear_goals=has_explicit_objective(interactions[-1]),
        immediate_feedback=feedback_latency_ms(interactions) < 100,
        deep_concentration=max_uninterrupted_hours(interactions),
        sense_of_control=error_recovery_rate(interactions) > 0.9,
        time_distortion=avg_burst > 10  # Long coherent bursts
    )
```

## Momentum Metrics (Kanban-Derived)

### Primary Metrics

| Metric | Formula | Target |
|--------|---------|--------|
| **Cycle Time** | `finish_time - start_time` | Minimize |
| **Lead Time** | `finish_time - request_time` | Minimize |
| **Throughput** | `items_done / time_period` | Maximize |
| **WIP** | `started - finished` | Limit |
| **Flow Efficiency** | `value_add_time / lead_time` | >25% |

### WIP Limits (Little's Law)

```
Lead Time = WIP / Throughput

Therefore: WIP_limit = Target_Lead_Time × Current_Throughput
```

Recommended WIP limits per focus area:
- **Individual**: 1-2 items
- **Pair**: 2-3 items  
- **Team**: N+1 where N = team size

## Momentum Killers

### The Deadly Seven

| Killer | Momentum Cost | Recovery Time |
|--------|---------------|---------------|
| **Context Switch** | -30% velocity per switch | 23 min |
| **Unclear Goals** | -50% (thrashing) | Until clarified |
| **Meetings** | -15 min/meeting overhead | Immediate |
| **Waiting (blocked)** | -100% (full stop) | Until unblocked |
| **Perfectionism** | -40% (diminishing returns) | Decision to ship |
| **Scope Creep** | -25% per added requirement | Scope reset |
| **Technical Debt** | -5% compounding daily | Refactor sprint |

### Detection Patterns

```python
def detect_momentum_killers(interactions: List[Interaction]) -> List[Killer]:
    killers = []
    
    # Context switching: topic changes per hour
    topic_changes = count_topic_changes(interactions, window="1h")
    if topic_changes > 3:
        killers.append(Killer.CONTEXT_SWITCH)
    
    # Unclear goals: high question/action ratio
    q_a_ratio = questions(interactions) / actions(interactions)
    if q_a_ratio > 0.5:
        killers.append(Killer.UNCLEAR_GOALS)
    
    # Blocked: long gaps with no progress
    gaps = find_gaps(interactions, threshold="30m")
    if any(g.reason == "waiting" for g in gaps):
        killers.append(Killer.BLOCKED)
    
    return killers
```

## Momentum Recovery Protocols

### Protocol 1: Restart Ritual (Cold Start)

```markdown
1. State ONE clear objective (15 words max)
2. List 3 concrete next actions
3. Set timer for 25 minutes (Pomodoro)
4. Disable all notifications
5. Start with smallest action
```

### Protocol 2: Unblock Sprint (Blocked State)

```markdown
1. Identify the blocker explicitly
2. Timebound: "If not unblocked in 30 min, escalate"
3. Parallel path: Work on something else OR
4. Reduce scope: Ship smaller version without blocked dependency
5. Document: Why blocked, when unblocked, lesson learned
```

### Protocol 3: Velocity Injection (Stale State)

```markdown
1. Ship something tiny (README fix, comment, config)
2. Commit immediately (momentum from motion)
3. Review recent wins (3 things shipped this week)
4. Pair with high-momentum collaborator
5. Change environment (different location/music/time)
```

### Protocol 4: Flow State Entry

```markdown
Prerequisites:
- [ ] Clear single objective
- [ ] All resources available (no waiting)
- [ ] Notifications disabled
- [ ] 90+ minute block scheduled
- [ ] Challenge matches skill level

Entry Sequence:
1. Read objective aloud
2. First action already known
3. Begin immediately (no planning in the moment)
```

## Integration with Triad

### With excellence-gradient (-1)

```python
def gradient_to_momentum(gradient: ExcellenceGradient) -> MomentumVector:
    """Gradient provides direction, momentum provides magnitude."""
    return MomentumVector(
        direction=gradient.steepest_ascent(),
        magnitude=current_velocity(),
        acceleration=gradient.curvature()  # How fast can we turn
    )
```

### With refuse-mediocrity (+1)

```python
def momentum_floor(current: Momentum, floor: QualityFloor) -> Momentum:
    """Refuse mediocrity sets minimum acceptable velocity."""
    if current.velocity < floor.minimum_shipping_rate:
        trigger_recovery_protocol()
    
    return current.with_constraint(min_velocity=floor.minimum_shipping_rate)
```

## DuckDB Tracking

```sql
CREATE TABLE momentum_samples (
    timestamp TIMESTAMPTZ,
    session_id UUID,
    velocity DOUBLE,        -- items/hour
    acceleration DOUBLE,    -- velocity change/hour
    jerk DOUBLE,           -- acceleration smoothness
    wip_count INT,
    flow_state BOOLEAN,
    active_killers TEXT[]  -- array of killer names
);

-- Compute rolling momentum
SELECT 
    session_id,
    AVG(velocity) OVER (ORDER BY timestamp ROWS 10 PRECEDING) as avg_velocity,
    STDDEV(velocity) OVER (ORDER BY timestamp ROWS 10 PRECEDING) as velocity_stability,
    COUNT(*) FILTER (WHERE flow_state) as flow_minutes
FROM momentum_samples
GROUP BY session_id;
```

## Commands

```bash
# Track momentum
just momentum-sample          # Record current state
just momentum-status          # Show velocity/acceleration
just momentum-killers         # Detect active killers

# Recovery
just momentum-restart         # Cold start protocol
just momentum-unblock ISSUE   # Unblock sprint
just momentum-inject          # Ship something tiny

# Analysis  
just momentum-report PERIOD   # Weekly/daily report
just momentum-flow-ratio      # Flow time percentage
```

## Csikszentmihalyi Flow Conditions

| Condition | Operational Check |
|-----------|-------------------|
| Clear goals | Objective stated in <15 words |
| Immediate feedback | <100ms response, test passes visible |
| Challenge-skill balance | Not bored, not anxious |
| Deep concentration | 90+ min uninterrupted blocks |
| Sense of control | Can make decisions without approval |
| Loss of self-consciousness | Not worried about judgment |
| Time distortion | Session felt shorter than clock time |
| Autotelic experience | Would do it for its own sake |

## GF(3) Triads

```
excellence-gradient (-1) ⊗ momentum-field (0) ⊗ refuse-mediocrity (+1) = 0 ✓
cognitive-surrogate (-1) ⊗ momentum-field (0) ⊗ entropy-sequencer (+1) = 0 ✓
topos-catcolab (-1) ⊗ momentum-field (0) ⊗ open-games (+1) = 0 ✓
```

## References

- Csikszentmihalyi, M. "Flow: The Psychology of Optimal Experience" (1990)
- Anderson, D. "Kanban: Successful Evolutionary Change" (2010)
- Newport, C. "Deep Work" (2016)
- Mark, G. et al. "The Cost of Interrupted Work" (2008) - 23 min recovery

---

**Skill Name**: momentum-field
**Type**: Shipping Velocity & Flow Optimization
**Trit**: 0 (ERGODIC - transports between validator and generator)
**GF(3)**: Conserved via triadic composition with excellence-gradient and refuse-mediocrity
