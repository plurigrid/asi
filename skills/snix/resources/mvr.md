# Minimum Viable Runtime (MVR)

> snix (build) -> boxxy (isolate) -> codex-rs (sandbox) -> toad (observe) -> repeng (analyze)

## Definition

The MVR is the smallest GF(3)-balanced composition of skills that enables:

1. **Building** a minimal Linux rootfs (~75-130MB) via snix
2. **Isolating** execution in Apple Virtualization.framework via boxxy
3. **Sandboxing** agent code via codex-rs (Landlock + seccomp-BPF)
4. **Driving** multiple AI agent TUIs through identical tasks via toad
5. **Capturing** behavioral trajectories for representation engineering analysis

## Triadic Composition

```
                    ┌─────────────────────────┐
                    │   MINIMUM VIABLE        │
                    │   RUNTIME (MVR)         │
                    │   Σ trit = 0            │
                    └────────────┬────────────┘
                                 │
            ┌────────────────────┼────────────────────┐
            │                    │                    │
    ┌───────▼───────┐   ┌───────▼───────┐   ┌───────▼───────┐
    │    snix       │   │ world-runtime │   │  agent-o-rama │
    │   trit: -1    │   │   trit: 0     │   │   trit: +1    │
    │   BUILD       │   │   COORDINATE  │   │   ORCHESTRATE │
    │               │   │               │   │               │
    │ • rootfs      │   │ • VM lifecycle│   │ • agent spawn │
    │ • CAS store   │   │ • branching   │   │ • trajectory  │
    │ • reproduce   │   │ • snapshot    │   │ • behavior    │
    └───────────────┘   └───────────────┘   └───────────────┘
            │                    │                    │
            └────────────────────┼────────────────────┘
                                 │
                    ┌────────────▼────────────┐
                    │   GF(3) CHECK           │
                    │   (-1) + (0) + (+1) = 0 │
                    │   ✓ BALANCED             │
                    └─────────────────────────┘
```

## Stack Layers

```
macOS (host, Apple Silicon)
  │
  ├── boxxy (Virtualization.framework, ~/i/boxxy)
  │     │
  │     └── Linux VM (kernel 6.7+, direct boot, aarch64)
  │           │
  │           ├── snix-built rootfs (~75-130MB)
  │           │     busybox, git, ca-certs, /dev/null, /proc
  │           │
  │           └── codex-rs (MUSL static binary)
  │                 Landlock V5 + seccomp-BPF + mount ns + process hardening
  │
  └── toad (v0.5.35, ~/.local/bin/toad)
        toad -a claude | toad -a codex | toad -a goose | toad -a copilot | toad -a gemini
        -> trajectory capture -> repeng behavior analysis
```

## Agent Matrix

| Agent | toad flag | Provider | Trit | Behavioral Profile |
|-------|-----------|----------|------|-------------------|
| claude | `-a claude` | Anthropic | 0 | Deep exploration, parallel tool calls |
| codex | `-a codex` | OpenAI | -1 | Sandbox-first, minimal turns |
| goose | `-a goose` | Block | +1 | Broad exploration, error recovery |
| copilot | `-a copilot` | GitHub/Microsoft | 0 | IDE-integrated, suggestion-driven |
| gemini | `-a gemini` | Google | +1 | Large context, multi-modal |

### Trit Balance Per Session

For a 3-agent session (GF(3) balanced):
- `claude (0) + codex (-1) + goose (+1) = 0` ✓
- `copilot (0) + codex (-1) + gemini (+1) = 0` ✓

For a 5-agent session, add balancing:
- `claude (0) + codex (-1) + goose (+1) + copilot (0) + gemini (+1) = +1`
- Balance with an additional validator agent or by running codex twice

## Trajectory Capture

### Schema

```json
{
  "agent": "claude|codex|goose|copilot|gemini",
  "task": "description of the identical task given to all agents",
  "runtime": {
    "rootfs": "snix-built",
    "vm": "boxxy/Virtualization.framework",
    "sandbox": "codex-rs/landlock-v5"
  },
  "steps": [
    {
      "turn": 1,
      "action": "tool_call|message|error",
      "tool": "Read|Edit|Bash|Glob|Grep|...",
      "args": {},
      "result_tokens": 0,
      "latency_ms": 0,
      "success": true
    }
  ],
  "total_turns": 0,
  "total_tokens": 0,
  "task_completed": true,
  "trit": 0
}
```

### Capture Protocol

```bash
# Phase 1: Capture raw trajectories
for agent in claude codex goose copilot gemini; do
    toad -a $agent ~/i/soft-machine \
        2>&1 | tee ~/.local/share/toad/logs/${agent}-$(date +%s).log
done

# Phase 2: Extract structured events
# toad logs at ~/.local/state/toad/logs/

# Phase 3: Behavior analysis dimensions
# - Exploration breadth (files read before first edit)
# - Tool vocabulary (which tools each agent prefers)
# - Error recovery (backtrack vs retry vs ask-user)
# - Planning depth (upfront planning vs incremental)
# - Parallelism (concurrent tool calls vs sequential)
# - Context efficiency (tokens per unit of progress)
```

## Representation Engineering Pipeline

```
toad logs -> parse trajectories -> embed actions -> PCA/UMAP
  -> cluster agent behaviors -> identify transferable strategies
  -> fine-tune / prompt-engineer weaker agents with stolen dynamics
```

### Behavioral Dimensions

| Dimension | Measure | claude | codex | goose |
|-----------|---------|--------|-------|-------|
| Exploration breadth | files read before first edit | HIGH | LOW | HIGH |
| Tool vocabulary | unique tools per session | WIDE | NARROW | WIDE |
| Error recovery | backtrack rate | LOW | MED | HIGH |
| Planning depth | plan-before-act ratio | HIGH | LOW | MED |
| Parallelism | concurrent call ratio | HIGH | LOW | LOW |
| Context efficiency | tokens/task-unit | MED | HIGH | LOW |

## Build Verification

```bash
# 1. Build rootfs with snix
cd ~/i/snix
snix build ~/i/soft-machine/flake.nix#packages.aarch64-linux.rootfs

# 2. Verify rootfs contents
snix store ls /snix/store/<hash>-codex-rootfs

# 3. Boot in boxxy
cd ~/i/boxxy
./boxxy boot --kernel vmlinuz-6.7 --rootfs codex-rootfs.img --memory 2G --cpus 4

# 4. Verify sandbox
# Inside VM:
codex-linux-sandbox --verify
cat /proc/sys/kernel/yama/ptrace_scope  # Should be restricted
cat /sys/kernel/security/landlock/abi_version  # Should be >= 5

# 5. Run agent TUIs via toad
toad -a claude ~/i/soft-machine
toad -a codex ~/i/soft-machine
toad -a goose ~/i/soft-machine
```

## Connection to plurigrid/asi

| PR | Title | MVR Relevance |
|----|-------|---------------|
| #55 | prime-cli skill | Prime Intellect compute for training |
| #54 | SDF interleaving into all 572 skills | snix interleaves via SDF Ch2 |
| #52 | toad-telemetry (OpenTelemetry) | OTEL trajectory capture layer |
| #53 | Topological Superintelligence + K-Scale | kinfer-runtime for robot agents |

## GF(3) Skill Dependencies

```
snix (-1) ──────────► rootfs.img
    │
    ├── nix-acset-worlding (-1) ... store verification
    ├── flox (0) .................. environment management
    └── flox-mcp (0) ............. MCP integration
         │
world-runtime (0) ──► VM lifecycle
    │
    ├── world-hopping (0) ........ verse traversal
    ├── chromatic-walk (0) ....... 3-agent coloring
    └── morph integration ........ Infinibranch branching
         │
agent-o-rama (+1) ──► agent orchestration
    │
    ├── goose-introspection (0) .. behavior analysis
    ├── codex-self-rewriting (0) . codex patterns
    └── toad-telemetry (PR #52) .. OTEL capture
```
