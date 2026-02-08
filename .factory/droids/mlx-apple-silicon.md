---
name: mlx-apple-silicon
description: Run LLMs on Apple Silicon with MLX/mlx_lm - unified memory, 4-bit quantization, streaming generation, prompt caching. Optimal for M-series chips.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# MLX Apple Silicon Skill

> *"Unified memory means no GPU↔CPU transfers - arrays live in shared memory."*

**Trit**: +1 (PLUS - generative)
**Color**: Warm (optimistic/fast)

## Overview

[MLX](https://github.com/ml-explore/mlx) is Apple's ML framework for Apple Silicon:
- **Unified Memory**: No GPU↔CPU data transfers
- **Lazy Evaluation**: Compute only what's needed
- **Metal Backend**: Native GPU acceleration
- **4-bit Quantization**: 75% smaller models

[MLX-LM](https://github.com/ml-explore/mlx-lm) provides high-level LLM APIs.

## Quick Start

```bash
# Install (macOS Apple Silicon)
pip install mlx mlx-lm

# Install (Linux CUDA - v0.28+)
pip install "mlx[cuda]"

# Generate text
mlx_lm.generate --model mlx-community/Mistral-7B-Instruct-v0.3-4bit \
  --prompt "Hello" --max-tokens 100

# Interactive chat
mlx_lm.chat --model mlx-community/Mistral-7B-Instruct-v0.3-4bit

# Vision/Multimodal (mlx-vlm)
pip install mlx-vlm
mlx_vlm.chat --model mlx-community/Qwen2.5-VL-7B-Instruct-4bit
```

## Python API

### Basic Generation

```python
from mlx_lm import load, generate

# Load 4-bit quantized model
model, tokenizer = load("mlx-community/Mistral-7B-Instruct-v0.3-4bit")

# Generate
messages = [{"role": "user", "content": "Write a haiku"}]
prompt = tokenizer.apply_chat_template(messages, add_generation_prompt=True)
text = generate(model, tokenizer, prompt=prompt, max_tokens=100)
print(text)
```

### Streaming Generation

```python
from mlx_lm import load, stream_generate

model, tokenizer = load("mlx-community/Mistral-7B-Instruct-v0.3-4bit")

for response in stream_generate(model, tokenizer, prompt="Hello", max_tokens=100):
    print(response.text, end="", flush=True)
    # response.token, response.logprobs, response.generation_tps available
```

### Batch Generation

```python
from mlx_lm import load, batch_generate

model, tokenizer = load("mlx-community/Mistral-7B-Instruct-v0.3-4bit")

prompts = ["Story about AI", "Explain ML", "Write a poem"]
result = batch_generate(m