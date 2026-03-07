---
name: gx10-offload
description: Offload inference, code generation, and batch processing to local GX10 DGX Spark (GB10 Blackwell) running Ollama
---

# GX10 Offload

Offload work to the local NVIDIA DGX Spark cluster node running Ollama with Devstral models on GB10 Blackwell GPU (128GB unified memory).

## When to Use

- Long code generation tasks that benefit from a dedicated local model
- Batch processing of multiple prompts
- Draft generation for review (speculative decoding pattern)
- Tasks where latency to cloud APIs is a bottleneck
- Privacy-sensitive inference that must stay on-premises

## Connection

| Property | Value |
|----------|-------|
| Host (WiFi) | `10.0.0.234` / `gx10-94e2.local` (mDNS) |
| Host (Tailscale) | `100.67.53.87` (gx10-acee, different unit) |
| User | `a` |
| Password | `aaaaaa` |
| Ollama API | `http://localhost:11434` on the device |
| SSH tunnel | `ssh -L 11434:localhost:11434 a@10.0.0.234` |

**Note**: The WiFi-connected unit is **gx10-94e2** (discovered via mDNS).
The Tailscale-reachable unit is **gx10-acee** (different physical Spark).

## Available Models

| Model | Size | Use Case |
|-------|------|----------|
| `devstral` | 14GB | Fast coding tasks, lightweight generation |
| `devstral-2:123b` | 74GB | Heavy reasoning, complex code generation |
| `devstral2-4k` | 74GB | Same as above, 4k context window |

## Quick Usage

### Single prompt via SSH

```bash
sshpass -p 'aaaaaa' ssh -o PreferredAuthentications=password -o PubkeyAuthentication=no \
  a@100.67.53.87 \
  "curl -s http://localhost:11434/api/generate -d '{\"model\":\"devstral\",\"prompt\":\"YOUR_PROMPT\",\"stream\":false}'"
```

### Via SSH tunnel (persistent)

```bash
# Open tunnel in background
sshpass -p 'aaaaaa' ssh -o PreferredAuthentications=password -o PubkeyAuthentication=no \
  -fNL 11434:localhost:11434 a@100.67.53.87

# Then use locally as if Ollama were running here
curl http://localhost:11434/api/generate \
  -d '{"model":"devstral","prompt":"Hello","stream":false}'
```

### OpenAI-compatible API

```bash
curl http://localhost:11434/v1/chat/completions \
  -H "Content-Type: application/json" \
  -d '{
    "model": "devstral",
    "messages": [{"role": "user", "content": "Write a Python function to sort a list"}]
  }'
```

### Using the offload script

```bash
# Simple prompt
~/.claude/skills/gx10-offload/scripts/offload.sh "Write a Rust function for binary search"

# With specific model
~/.claude/skills/gx10-offload/scripts/offload.sh "Explain monads" devstral-2:123b

# Batch mode (one prompt per line)
~/.claude/skills/gx10-offload/scripts/offload.sh --batch prompts.txt
```

## Offload Patterns

### 1. Draft-and-Review

Offload draft generation to GX10, then review/refine with Claude:

```bash
# GX10 generates draft
DRAFT=$(~/.claude/skills/gx10-offload/scripts/offload.sh "Implement a Redis cache wrapper in Python with TTL support")
# Claude reviews and improves the draft
```

### 2. Batch Code Generation

Generate multiple implementations in parallel on GX10:

```bash
for task in "sort" "search" "hash" "tree"; do
  ~/.claude/skills/gx10-offload/scripts/offload.sh "Implement $task in Rust" &
done
wait
```

### 3. Test Generation

Offload test writing to the local model:

```bash
~/.claude/skills/gx10-offload/scripts/offload.sh "Write pytest tests for: $(cat src/main.py)"
```

## Device Status Check

```bash
~/.claude/skills/gx10-offload/scripts/offload.sh --status
```

## Ensure Ollama is Running

```bash
sshpass -p 'aaaaaa' ssh -o PreferredAuthentications=password -o PubkeyAuthentication=no \
  a@100.67.53.87 'pgrep ollama || nohup ollama serve > /tmp/ollama.log 2>&1 &'
```

## Hardware

- **GPU**: NVIDIA GB10 Blackwell (DGX Spark)
- **Memory**: 128GB unified (Grace-Blackwell architecture)
- **CPU**: 20-core Grace ARM64
- **OS**: Ubuntu 24.04 aarch64, kernel 6.14-nvidia
- **PyTorch**: 2.10.0 with CUDA
- **Disk**: 510GB free

## GF(3) Assignment

| Trit | Role | Description |
|------|------|-------------|
| +1 | PLUS | Generator - produces code/text offloaded from Claude |

Conservation triad: `gx10-offload (+1) + tailscale (0) + skill-creator (-1) = 0`
