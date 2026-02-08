---
name: kolmogorov-compression
description: Kolmogorov complexity as the ultimate intelligence measure. Shortest
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Kolmogorov Compression Skill

> *"The Kolmogorov complexity of x is the length of the shortest program that outputs x."*
> — Andrey Kolmogorov

## Overview

**Kolmogorov complexity** K(x) = length of shortest program P where P() = x.

**Intelligence = Compression**: Finding short descriptions of data.

## Core Concept

```latex
K(x) = min { |P| : U(P) = x }

Where:
  U = Universal Turing Machine
  P = program (binary string)
  |P| = length of P

Properties:
  - K(x) ≤ |x| + O(1)  (trivial: print x)
  - K(x) is uncomputable (halting problem)
  - K(x|y) = conditional complexity given y
```

## The KoLMogorov-Test (2025)

Use LLMs to approximate Kolmogorov complexity:

```python
class KolmogorovCompressor:
    """
    Approximate K(x) via code generation.
    """
    
    def __init__(self, llm):
        self.llm = llm
    
    def compress(self, data: str) -> str:
        """Generate shortest program that outputs data."""
        prompt = f"""
        Generate the shortest Python program that prints exactly:
        {data[:100]}...
        
        The program must output EXACTLY this string.
        Make it as SHORT as possible.
        """
        
        program = self.llm.generate(prompt)
        return self.extract_code(program)
    
    def complexity(self, data: str) -> int:
        """Estimate K(data)."""
        program = self.compress(data)
        return len(program.encode())
    
    def intelligence_score(self, model, data: str) -> float:
        """
        KoLMogorov-Test score.
        
        Higher = better compression = more intelligent.
        """
        program = model.compress(data)
        ratio = len(program) / len(data)
        return 1 - ratio  # Higher = better
```

## Connection to Theorem Proving

```
For proof P of theorem T:
  K(T) ≈ min |P| over all proofs P

Short proofs = Simple theorems
Long proofs = Complex theorems (but still provable)

Gödel: Some true statements have K(T) = ∞ (unprovable)
```

---

## End-of-Skill Interface