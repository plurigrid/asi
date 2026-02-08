---
name: system2-attention
description: System 2 attention mechanisms for deliberate, slow reasoning in transformer
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# System 2 Attention Skill: Deliberate Reasoning Validation

**Status**: ✅ Production Ready
**Trit**: -1 (MINUS - validator/constraint)
**Color**: #2626D8 (Blue)
**Principle**: Filter noise via deliberate re-attention
**Frame**: Two-stage attention with explicit reasoning

---

## Overview

**System 2 Attention** (S2A) validates and filters transformer attention by regenerating context deliberately. Standard attention (System 1) is fast but susceptible to sycophancy and irrelevant context. S2A re-attends after explicit reasoning.

1. **Context regeneration**: LLM rewrites context removing irrelevant info
2. **Two-pass attention**: Fast then deliberate
3. **Sycophancy reduction**: Filter opinion-seeking noise
4. **Factual grounding**: Anchor to verified facts

## Core Pattern

```
S2A(x, context):
  # System 1: fast pattern matching
  context_filtered = LLM("Extract only relevant facts from: {context}")
  
  # System 2: deliberate reasoning on clean context
  return LLM(x, context=context_filtered)
```

```python
def system2_attention(query: str, context: str, model) -> str:
    # Stage 1: Regenerate context (remove sycophantic/irrelevant)
    filter_prompt = f"""Given the context below, extract only the 
    objective facts relevant to answering questions. Remove opinions,
    leading questions, and irrelevant details.
    
    Context: {context}
    
    Relevant facts only:"""
    
    clean_context = model.generate(filter_prompt)
    
    # Stage 2: Answer with filtered context
    return model.generate(query, context=clean_context)
```

## Key Concepts

### 1. Context Filtering

```python
class S2AFilter:
    def __init__(self, model):
        self.model = model
    
    def filter_sycophancy(self, context: str) -> str:
        """Remove opinion-seeking and leading content."""
        return self.model.generate(
            f"Rewrite removing any opinions or leading questions:\n{context}"
        )
    
    def filter_irrelevant(self, context: str, query: str) -