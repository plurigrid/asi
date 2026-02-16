---
name: orchestrate
description: Orchestrate multiple AI agents across Vers VMs for parallel task execution
---

# VM Orchestration Skill

You can orchestrate multiple AI agents running on Vers VMs. Each VM runs its own vers instance that you can control via the CLI.

## Architecture

```
You (orchestrator)
  │
  │ vers → localhost:9999
  │
  ├── VM-1 (vers on :80) ─── works on task
  ├── VM-2 (vers on :80) ─── works on task
  └── VM-N (vers on :80) ─── works on task
```

## CLI Commands

All commands use the vers binary:
```bash
vers <command> [args]
```

The vers server must be running (default port 9999). Commands communicate with it via JSON-RPC.

## Golden Image

New VMs are created from a golden image with:
- Bun 1.3.6 pre-installed
- vers with all dependencies
- Pre-configured .env with API keys

This makes VM creation fast (~2-3 seconds).

## Available Commands

### List VMs
```bash
vers vms
```

### Create a VM
Creates a new VM from the golden image.
```bash
vers vm create "description of what this VM will work on"
```

Returns: `{ "vmId": "...", "agentUrl": "https://<vmId>.vm.vers.sh" }`

### Run a Prompt on VM(s)
Send a prompt to all VMs (fire-and-forget, doesn't wait for completion):
```bash
vers vm run "your task here"
```

### Execute Command on VM (SSH)
Run arbitrary shell commands on a VM via SSH:
```bash
vers vm exec <vmId> "ls -la /root"
```

Returns: `{ "stdout": "...", "stderr": "...", "exitCode": 0 }`

Use this to:
- Check agent status: `curl -s http://localhost:80/health`
- View logs: `tail -100 ~/.vers-agent/logs/vers-agent.log`
- Run git commands: `git status` (in working directory)
- Restart agent: `systemctl restart vers-agent`

### Sync Local Git to VM
Sync your local git repository to a VM:
```bash
vers vm sync <vmId>
```

### Evaluate VM (Build/Test/Lint)
Run evaluation commands on a VM:
```bash
vers vm eval <vmId>
```

### Watch VM Events (SSE Stream)
Real-time streaming of events from all VMs, tagged by VM ID:
```bash
vers vm watch

# Filter to specific VMs (comma-separated)
vers vm watch "vm-id-1,vm-id-2"
```

Output shows VM ID prefix with color coding:
```
[a1c9d57b] Hello! I'm working on the task...
[df6f41fb] Starting implementation...
[a1c9d57b] ✓ Done
```

## Orchestration Patterns

### Pattern 1: Parallel Exploration
Create multiple VMs and try different approaches:
```bash
# 1. Create VMs for different approaches
vers vm create "implement feature X - approach A"
vers vm create "implement feature X - approach B"
vers vm create "implement feature X - approach C"

# 2. Run task on all VMs
vers vm run "implement feature X using your assigned approach"

# 3. Watch progress in real-time
vers vm watch
```

### Pattern 2: Divide and Conquer
Split a large task across multiple VMs:
```bash
# Create VMs for each subtask
vers vm create "implement auth module"
vers vm create "implement database layer"
vers vm create "implement API endpoints"

# Dispatch work to all
vers vm run "implement your assigned module"

# List VMs to check status
vers vms
```

### Pattern 3: Code Sync & Deploy
Sync local git changes to VMs:
```bash
# Sync local git to a VM
vers vm sync <vmId>

# Or execute commands directly
vers vm exec <vmId> "git pull"
```

### Pattern 4: Different Prompts to Different VMs
Send unique prompts to specific VMs using curl with vmIds filter:
```bash
# Get VM IDs first
vers vms

# Send different prompts (use curl for vmIds filtering)
curl -sX POST http://localhost:9999/rpc -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","id":1,"method":"vm/run","params":{"prompt":"Write a haiku","vmIds":["vm-id-1"]}}'

curl -sX POST http://localhost:9999/rpc -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","id":1,"method":"vm/run","params":{"prompt":"Explain recursion","vmIds":["vm-id-2"]}}'
```

## Key Principles

1. **Branches are cheap** - Fork VMs liberally to explore alternatives
2. **Commits cost money** - Only commit checkpoints when you need to preserve state long-term
3. **Side effects are real** - VMs have full network access, actions are not reversible
4. **Fire and forget** - vm run dispatches work but doesn't wait for completion
5. **Check status** - Use `vms` for quick overview, `vm watch` for real-time streaming
6. **Agent on port 80** - Each VM's vers runs on port 80, use vm exec + curl to interact
7. **Multiplexed events** - Use `vm watch` to monitor all VMs in one stream, tagged by vmId

## When to Use This Skill

Use `/orchestrate` when you need to:
- Run the same task with different approaches in parallel
- Split a large task across multiple agents
- Explore a solution space (MCTS-style)
- Scale up compute for a complex problem
- Deploy code changes to remote VMs

$ARGUMENTS
