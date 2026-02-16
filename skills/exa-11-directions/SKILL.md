# exa-11-directions Skill

**Status**: ✅ Production Ready
**Trit**: 0 (ERGODIC - coordinates research across domains)
**Type**: Distributed Research Orchestrator
**Execution Model**: core.async.flow + agent-o-rama compatible

---

## Overview

**exa-11-directions** is a distributed research orchestrator that spawns 11 parallel deep research agents across different domains, each exploring unusual software packages and skills that enhance the 200-skill music-topos ecosystem.

### The 11 Research Directions

1. **Category Theory & ACSet Implementations** - Categorical data structures, functorial programming
2. **Distributed Systems & CRDT Frameworks** - Conflict-free replication, consensus algorithms
3. **Music, Sound Synthesis & Audio DSP** - Synthesis, microtonal systems, generative music
4. **Advanced Data Structures & Lenses** - Persistent data, bidirectional navigation, optics
5. **Proof Assistants & Formal Verification** - Theorem provers, type theory, verification systems
6. **Visualization, UI & Interaction** - Graph visualization, 3D rendering, sonification
7. **Machine Learning & Adaptive Learning** - Reinforcement learning, meta-learning, novelty search
8. **Game Theory & Economic Systems** - Open games, market mechanisms, agent-based modeling
9. **Information Theory & Entropy** - Entropy decomposition, synergy measurement, information flow
10. **Biology, Neuroscience & Consciousness** - Connectome analysis, integrated information theory
11. **Physics, Chemistry & Topological Systems** - Dynamical systems, topological data analysis

---

## Architecture

### Three-Layer Execution

```
┌─────────────────────────────────────────────────────────┐
│ Layer 1: LAUNCH (Parallel Agent Spawning)              │
│ - 11 Exa research tasks launched simultaneously        │
│ - Each gets unique task ID for tracking                │
└─────────────────────────────────────────────────────────┘
                        ↓
┌─────────────────────────────────────────────────────────┐
│ Layer 2: MONITOR (Polling & Progress Tracking)         │
│ - Exponential backoff polling: 30s → 60s → 90s...     │
│ - Max 20 polls (up to 30 minutes per direction)       │
│ - Real-time progress reporting                         │
└─────────────────────────────────────────────────────────┘
                        ↓
┌─────────────────────────────────────────────────────────┐
│ Layer 3: AGGREGATE (Result Synthesis & Export)         │
│ - JSON, Markdown, DuckDB exports                       │
│ - Package statistics and categorization                │
│ - Integration with skill ecosystem                     │
└─────────────────────────────────────────────────────────┘
```

### core.async Flow

```clojure
;; Channel-based async pipeline
(launch-all-directions)
  → output-ch (11 task descriptors)
  → (monitor-all-tasks task-descriptors poll-interval-ms)
  → output-ch (progress updates)
  → (aggregate-11-direction-results)
  → {:summary {...} :directions {...} :statistics {...}}
```

---

## Usage

### 1. Direct Babashka Execution

```bash
# Set API key
export EXA_API_KEY="your-exa-api-key"

# Launch all 11 directions (default: 30s polls, max 20 polls)
bb lib/exa_11_directions.bb execute

# Custom polling parameters
POLL_INTERVAL=60000 MAX_POLLS=10 bb lib/exa_11_directions.bb execute
```

### 2. Via Justfile

```bash
# Launch with defaults (30s polling, 20 max polls)
just exa-11-research

# Custom parameters
just exa-11-research 60000 10

# Check status
just exa-status

# Export results
just exa-export all      # JSON + Markdown + DuckDB
just exa-export json     # JSON only
just exa-export markdown # Markdown only
```

### 3. Agent-O-Rama Integration

```bash
# Spawn as agent-o-rama skill
just exa-agent-spawn

# With callback function
(skill :exa-11-directions :action :spawn-research-agents!)
```

### 4. Clojure REPL (nbb-compatible)

```clojure
(require '[exa-11-directions :as exa])

;; Launch all directions
(exa/launch-all-directions)

;; Monitor tasks
(exa/monitor-all-tasks task-descriptors 30000)

;; Aggregate results
(exa/aggregate-11-direction-results results-vec)
```

---

## Output Formats

### JSON Results

```json
{
  "summary": {
    "total-directions": 11,
    "completed": 11,
    "failed": 0,
    "timestamp": "2025-12-24T15:30:45Z"
  },
  "directions": {
    "Category Theory & ACSet Implementations": {
      "direction-id": 1,
      "status": "completed",
      "package-count": 47,
      "sample-packages": [
        "github.com/algebraicjulia/Catlab.jl",
        "github.com/algebraicjulia/ACSets.jl"
      ]
    },
    ...
  },
  "statistics": {
    "total-packages-found": 512,
    "avg-packages-per-direction": 46.5
  }
}
```

### Markdown Report

```markdown
# Exa 11-Direction Research Results

**Completed**: 11 / 11
**Timestamp**: 2025-12-24T15:30:45Z
**Total Packages Found**: 512

## Results by Direction

### Category Theory & ACSet Implementations
- **Status**: completed
- **Packages Found**: 47
- **Report Lines**: 2341

...
```

### DuckDB Table

```sql
SELECT direction, package_count, status, sample_packages
FROM research_results
ORDER BY package_count DESC;
```

---

## GF(3) Integration

**Trit**: 0 (ERGODIC)
**Role**: Coordinates multi-directional research

### Triadic Compositions with exa-11-directions

```
curiosity-driven (+1) ⊗ exa-11-directions (0) ⊗ code-review (-1) = 0 ✓
- Generation: Curiosity drives exploration
- Coordination: Research orchestrates findings
- Validation: Review filters results
```

```
rama-gay-clojure (+1) ⊗ exa-11-directions (0) ⊗ sheaf-cohomology (-1) = 0 ✓
- Generation: Rama generates data pipelines
- Coordination: Research orders package discovery
- Validation: Sheaf ensures coherence
```

---

## Implementation Details

### core.async Channels

| Channel | Purpose | Buffer |
|---------|---------|--------|
| `tasks-ch` | Task launch outputs | 11 (11 directions) |
| `monitor-ch` | Progress updates | Unbuffered |
| `results-ch` | Final aggregated results | 1 |

### Polling Strategy

- **Exponential Backoff**: Start at 30s, increase by 30s each poll
- **Max Polls**: 20 (up to 630 seconds = ~10.5 minutes per direction)
- **Completion Check**: All tasks must reach "completed" status
- **Early Exit**: Stops polling if all tasks complete early

### Package Detection

Packages identified via regex patterns in research reports:
- GitHub: `github.com/`, `github:`
- NPM: `npm:`, npm package names
- PyPI: `PyPI`, package names

---

## File Structure

```
.claude/skills/exa-11-directions/
├── SKILL.md (this file)
└── lib/exa_11_directions.bb (executable)
└── lib/exa_11_directions.clj (Clojure version)
```

---

## Dependencies

- **Babashka** (for `.bb` execution)
- **Cheshire** (JSON library)
- **http-kit** (HTTP client via babashka)
- **EXA_API_KEY** (environment variable)

---

## Configuration

Via environment variables:

```bash
# API Key (required)
export EXA_API_KEY="sk-..."

# Polling interval in milliseconds (default: 30000)
export POLL_INTERVAL=60000

# Maximum number of polls (default: 20)
export MAX_POLLS=10
```

---

## Metrics & Statistics

After execution, review:

```bash
# Total packages found across all directions
jq '.statistics.total-packages-found' /tmp/exa-11-directions*.json

# Packages per direction (avg)
jq '.statistics.avg-packages-per-direction' /tmp/exa-11-directions*.json

# Completed vs failed
jq '.summary | {completed, failed}' /tmp/exa-11-directions*.json
```

---

## Future Extensions

1. **Package Integration**: Automatically add discovered packages to skill manifests
2. **Ranking System**: Score packages by GitHub stars, documentation, community
3. **Skill Bridging**: Match discovered packages to existing 200 skills
4. **Automated Triads**: Suggest GF(3)=0 compositions using discovered packages
5. **Continuous Monitoring**: Periodic re-runs to track ecosystem evolution

---

## Troubleshooting

### EXA_API_KEY not set
```bash
export EXA_API_KEY="your-key-from-https://dashboard.exa.ai"
```

### Tasks timing out
Increase `POLL_INTERVAL` or `MAX_POLLS`:
```bash
POLL_INTERVAL=90000 MAX_POLLS=30 just exa-11-research
```

### No results generated
Ensure task IDs were received:
```bash
grep "taskId" /tmp/exa-11-directions*.json
```

---

## References

- **Exa Docs**: https://docs.exa.ai
- **Babashka Docs**: https://github.com/babashka/babashka
- **core.async Patterns**: https://clojure.org/about/async
- **Music-Topos 200-Skill Ecosystem**: See ECOSYSTEM_ANALYSIS_SESSION_REPORT.md

---

**Created**: 2025-12-24
**Framework**: Exa API + core.async.flow + agent-o-rama
**Status**: Ready for production use
