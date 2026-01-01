# EleutherAI MLX Skill

Convert and run EleutherAI models (Pythia, GPT-NeoX) on Apple Silicon using MLX.

## Environment Setup

```bash
# Create flox environment
cd ~/Projects/eleuther-mlx
flox init
flox install python312Packages.mlx python312Packages.pip python312Packages.huggingface-hub

# Create venv and install mlx-lm
flox activate -- bash -c "python3 -m venv .venv && source .venv/bin/activate && pip install mlx-lm transformers"
```

## Model Conversion

### Convert EleutherAI Pythia (various sizes)

```bash
# Pythia 410M (4-bit quantized, ~228MB)
flox activate -- bash -c "source .venv/bin/activate && mlx_lm.convert --hf-path EleutherAI/pythia-410m -q --q-bits 4"

# Pythia 1B
mlx_lm.convert --hf-path EleutherAI/pythia-1b -q --q-bits 4

# Pythia 1.4B
mlx_lm.convert --hf-path EleutherAI/pythia-1.4b -q --q-bits 4

# Pythia 2.8B
mlx_lm.convert --hf-path EleutherAI/pythia-2.8b -q --q-bits 4

# GPT-NeoX 20B (requires significant memory)
mlx_lm.convert --hf-path EleutherAI/gpt-neox-20b -q --q-bits 4
```

### Quantization Options

```bash
# 8-bit (higher quality, larger size)
mlx_lm.convert --hf-path EleutherAI/pythia-410m -q --q-bits 8

# 4-bit grouped (balance of quality/size)
mlx_lm.convert --hf-path EleutherAI/pythia-410m -q --q-bits 4 --q-group-size 64

# No quantization (full precision, FP16)
mlx_lm.convert --hf-path EleutherAI/pythia-410m
```

## Generation

```bash
# Basic generation
mlx_lm.generate --model ./mlx_model --prompt "The future of AI is" --max-tokens 100

# With temperature and sampling
mlx_lm.generate --model ./mlx_model --prompt "Once upon a time" \
  --max-tokens 200 --temp 0.7 --top-p 0.95

# Chat mode (if model supports it)
mlx_lm.chat --model ./mlx_model
```

## Python API

```python
from mlx_lm import load, generate

model, tokenizer = load("./mlx_model")

response = generate(
    model,
    tokenizer,
    prompt="Explain quantum computing:",
    max_tokens=200,
    temp=0.7
)
print(response)
```

## Fine-tuning with LoRA

```bash
# Prepare training data (JSONL format)
# {"text": "Training example 1"}
# {"text": "Training example 2"}

mlx_lm.lora --model ./mlx_model \
  --train \
  --data ./train.jsonl \
  --batch-size 4 \
  --lora-layers 8 \
  --iters 1000
```

## Available EleutherAI Models

| Model | Params | HF Path |
|-------|--------|---------|
| Pythia-70M | 70M | EleutherAI/pythia-70m |
| Pythia-160M | 160M | EleutherAI/pythia-160m |
| Pythia-410M | 410M | EleutherAI/pythia-410m |
| Pythia-1B | 1B | EleutherAI/pythia-1b |
| Pythia-1.4B | 1.4B | EleutherAI/pythia-1.4b |
| Pythia-2.8B | 2.8B | EleutherAI/pythia-2.8b |
| Pythia-6.9B | 6.9B | EleutherAI/pythia-6.9b |
| Pythia-12B | 12B | EleutherAI/pythia-12b |
| GPT-NeoX-20B | 20B | EleutherAI/gpt-neox-20b |

## GF(3) Integration

```
Trit: +1 (PLUS) - Generator/executor role
Hue: 30° (warm orange)
```

This skill pairs with:
- **huggingface-hub** (ERGODIC, 0): Model discovery and caching
- **transformers** (MINUS, -1): Tokenizer and config validation

Conservation: (-1) + (0) + (+1) = 0 (mod 3)

## Notes

- Requires Apple Silicon (M1/M2/M3/M4/M5)
- MLX uses unified memory - larger models benefit from high-memory Macs
- 4-bit quantization reduces memory ~4x with minimal quality loss
- Model outputs saved to `./mlx_model/` by default
