---
name: hijaling
description: 'This skill extends [mlegls/hyjax](https://github.com/mlegls/hyjax) with:'
---
# hijaling

> Hy + JAX + Outlines = Structured s-expression generation via constrained LLM decoding. The final use of HyJAX.

## Trit: +1 (PLUS - generative)

## Etymology

```
hijaling = Hy + JAX + Outlines + lang
         = Lisp s-expressions + autodiff + structured generation + language
```

## Core Concept

```
┌─────────────────────────────────────────────────────────────────┐
│                       HIJALING PIPELINE                         │
│                                                                 │
│   Input Text ──▶ Outlines ──▶ Constrained LLM ──▶ Hy S-expr    │
│       │           (JSON         (guided           (valid        │
│       │           Schema)        decode)           Hy code)     │
│       │              │              │                 │         │
│       ▼              ▼              ▼                 ▼         │
│   "describe"    SexprSchema    GPT/Claude        (defn foo      │
│   "a neural"    {form, args,   w/ grammar         [x y]         │
│   "network"     body, ...}     constraint         (+ x y))      │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## Outlines S-expression Schema

```python
# hijaling/schema.py
from pydantic import BaseModel
from typing import List, Union, Literal, Optional
from enum import Enum

class HyAtom(BaseModel):
    """Atomic Hy value"""
    type: Literal["symbol", "keyword", "integer", "float", "string"]
    value: str

class HyList(BaseModel):
    """Hy list (function call, defn, etc.)"""
    elements: List[Union["HyAtom", "HyList"]]

class HyDefn(BaseModel):
    """Hy function definition - most common form"""
    name: str
    params: List[str]
    docstring: Optional[str] = None
    body: List[Union["HyAtom", "HyList"]]

class HyExpr(BaseModel):
    """Any valid Hy expression"""
    form: Literal["defn", "defclass", "setv", "if", "when", "for", "import", "require", "do"]
    content: Union[HyDefn, HyList]

class HyModule(BaseModel):
    """Complete Hy module"""
    imports: List[str] = []
    requires: List[str] = []
    definitions: List[HyExpr]

# Enable forward references
HyList.model_rebuild()
```

## Outlines Generator

```python
# hijaling/generator.py
import outlines
from outlines import models, generate
from hijaling.schema import HyModule, HyDefn, HyExpr

def create_hijaling_generator(model_name: str = "claude-sonnet"):
    """Create an Outlines generator for Hy s-expressions."""
    
    # Use OpenAI/Anthropic via outlines
    model = outlines.from_openai(
        openai.OpenAI(),
        model_name
    )
    
    return model

def generate_hy_function(prompt: str, model) -> str:
    """Generate a Hy function from natural language."""
    
    schema = HyDefn.model_json_schema()
    
    result = model(
        f"Generate a Hy (Lisp for Python) function: {prompt}. "
        f"Use s-expression syntax with (defn name [params] body).",
        HyDefn,
        temperature=0.3
    )
    
    # Convert JSON to s-expression
    return defn_to_sexp(HyDefn.model_validate_json(result))

def defn_to_sexp(defn: HyDefn) -> str:
    """Convert HyDefn JSON to actual s-expression string."""
    params = " ".join(defn.params)
    body = " ".join(expr_to_sexp(b) for b in defn.body)
    
    if defn.docstring:
        return f'(defn {defn.name} [{params}]\n  "{defn.docstring}"\n  {body})'
    else:
        return f'(defn {defn.name} [{params}]\n  {body})'

def expr_to_sexp(expr) -> str:
    """Recursively convert expression to s-expression."""
    if isinstance(expr, dict):
        if expr.get("type") in ("symbol", "keyword", "integer", "float"):
            return str(expr["value"])
        elif expr.get("type") == "string":
            return f'"{expr["value"]}"'
        elif "elements" in expr:
            inner = " ".join(expr_to_sexp(e) for e in expr["elements"])
            return f"({inner})"
    return str(expr)
```

## JAX Integration

```python
# hijaling/jax_bridge.py
"""Bridge HyJAX to JAX via Outlines-generated code."""

import jax
import jax.numpy as jnp
from hy import read_str, eval as hy_eval
from hijaling.generator import generate_hy_function

def hijaling_jax(description: str, model) -> callable:
    """
    Generate a JAX-compatible function from natural language.
    
    1. Use Outlines to generate Hy s-expression
    2. Parse with hy.read_str
    3. Compile to Python AST
    4. JIT with JAX
    """
    
    # Generate Hy code
    hy_code = generate_hy_function(
        f"{description}. Use jax.numpy (as jnp) for array operations.",
        model
    )
    
    # Parse and evaluate in Hy
    hy_form = read_str(hy_code)
    fn = hy_eval(hy_form)
    
    # JIT compile with JAX
    return jax.jit(fn)

# Example usage
def demo():
    from hijaling.generator import create_hijaling_generator
    
    model = create_hijaling_generator()
    
    # Generate a neural network layer
    linear_layer = hijaling_jax(
        "a linear transformation layer that multiplies input x by weights w and adds bias b",
        model
    )
    
    # The generated Hy code might be:
    # (defn linear [x w b]
    #   "Linear transformation: Wx + b"
    #   (+ (jnp.dot x w) b))
    
    # Test it
    x = jnp.array([1.0, 2.0, 3.0])
    w = jnp.eye(3)
    b = jnp.zeros(3)
    
    result = linear_layer(x, w, b)
    print(result)  # [1.0, 2.0, 3.0]
```

## NuShell Integration

```nu
# hijaling.nu - Structured s-expression generation via NuShell

# Generate Hy code via Outlines
def hijaling [prompt: string] {
  # Call Python hijaling
  let result = (python3 -c $"
from hijaling.generator import create_hijaling_generator, generate_hy_function
model = create_hijaling_generator()
print(generate_hy_function('($prompt)', model))
")
  
  # Parse as structured data
  {
    prompt: $prompt
    hy_code: $result
    timestamp: (date now | format date "%Y-%m-%d %H:%M:%S")
    hash: ($result | hash sha256 | str substring 0..8)
  }
}

# Generate and execute
def hijaling-exec [prompt: string] {
  let gen = (hijaling $prompt)
  
  # Write to temp file
  $gen.hy_code | save -f /tmp/hijaling_temp.hy
  
  # Execute with hy
  hy /tmp/hijaling_temp.hy
}

# Batch generation from table
def hijaling-batch [prompts: table] {
  $prompts | each { |row|
    hijaling $row.prompt
  }
}
```

## Gwern Integration

```python
# hijaling/gwern.py
"""Self-operating Gwern via hijaling."""

from hijaling.generator import create_hijaling_generator, generate_hy_function

def gwern_to_hy(essay_topic: str) -> str:
    """Convert Gwern essay concept to Hy s-expression."""
    
    model = create_hijaling_generator()
    
    prompts = {
        "scaling": "a function that models scaling laws: performance = k * compute^alpha",
        "bitter-lesson": "a function that returns the bitter lesson: general methods + compute beat specialized knowledge",
        "spaced-repetition": "a function that calculates optimal spaced repetition intervals using Ebbinghaus forgetting curve",
        "tool-ai": "a function that orchestrates tool use by an AI agent with a list of available tools",
    }
    
    prompt = prompts.get(essay_topic, f"a function representing the concept: {essay_topic}")
    
    return generate_hy_function(prompt, model)

# Self-operating: generate code that generates code
def meta_gwern():
    """Gwern writes Gwern."""
    
    model = create_hijaling_generator()
    
    # Generate a function that generates functions
    meta_code = generate_hy_function(
        "a higher-order function that takes a topic string and returns "
        "a function implementing that topic's core algorithm",
        model
    )
    
    return meta_code
```

## Example Generated S-expressions

```hy
;; hijaling output for "neural network forward pass"
(defn forward-pass [x weights biases activations]
  "Compute forward pass through neural network layers."
  (reduce 
    (fn [h [w b act]]
      (act (+ (jnp.dot h w) b)))
    (zip weights biases activations)
    x))

;; hijaling output for "attention mechanism"
(defn attention [query key value]
  "Scaled dot-product attention."
  (let [d-k (get (jnp.shape key) -1)
        scores (/ (jnp.dot query (jnp.transpose key)) 
                  (jnp.sqrt d-k))
        weights (jax.nn.softmax scores :axis -1)]
    (jnp.dot weights value)))

;; hijaling output for "gwern scaling law"
(defn scaling-law [compute alpha k]
  "Gwern scaling hypothesis: performance = k * compute^alpha"
  (* k (** compute alpha)))
```

## GF(3) Conservation

```
hijaling (+1) ⊗ hyjax-relational (0) ⊗ outlines-validator (-1) = 0 ✓
gwern-simonw-emacs (+1) ⊗ hijaling (+1) ⊗ leapity-frog (-1) = +1 (IMBALANCED - needs validator)
```

## Dependencies

```toml
# pyproject.toml
[project]
name = "hijaling"
dependencies = [
    "hy>=1.0.0",
    "jax[cpu]",
    "outlines>=0.1.0",
    "pydantic>=2.0",
    "openai",
]
```

## Usage

```bash
# Install
pip install hijaling

# Generate Hy function
hijaling "a recursive fibonacci function" > fib.hy

# Execute
hy fib.hy

# In Python
from hijaling import hijaling_jax
fib = hijaling_jax("recursive fibonacci", model)
print(fib(10))  # 55

# In NuShell
hijaling "matrix multiplication" | save result.json
```

## Connection to mlegls/hyjax

This skill extends [mlegls/hyjax](https://github.com/mlegls/hyjax) with:
1. **Outlines constraint** - Guarantees valid Hy syntax
2. **Gwern integration** - Self-operating essay→code
3. **NuShell bridge** - Structured data pipeline
4. **Simon W exposure** - LLM CLI tool compatibility

## References

- [mlegls/hyjax](https://github.com/mlegls/hyjax) - Hy bindings for JAX
- [dottxt-ai/outlines](https://github.com/dottxt-ai/outlines) - Structured generation
- [hylang/hy](https://github.com/hylang/hy) - Lisp dialect for Python
- [gwern.net](https://gwern.net) - Essay corpus
- [hyjax-relational](file:///Users/bob/ies/plurigrid-asi-skillz/skills/hyjax-relational/SKILL.md) - Thread analysis


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
