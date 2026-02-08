---
name: causal-inference
description: "Bengio's causal inference for AI: Interventional reasoning, counterfactuals, and System 2 deep learning. World models with causal structure."
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Causal Inference Skill

> *"Current deep learning is System 1: fast, intuitive, but easily fooled. We need System 2: slow, deliberate, causal."*
> — Yoshua Bengio

## Overview

**Causal inference** enables:
1. **Interventional reasoning**: What happens if I *do* X?
2. **Counterfactual reasoning**: What *would have* happened if...?
3. **Transfer**: Causal structure generalizes across domains
4. **Robustness**: Causal models resist distribution shift

## Pearl's Causal Hierarchy

```
Level 3: Counterfactual (Imagining)
  "What would have happened if I had done X?"
  P(y_x | x', y')
          ▲
Level 2: Intervention (Doing)
  "What happens if I do X?"
  P(y | do(X))
          ▲
Level 1: Association (Seeing)
  "What does X tell me about Y?"
  P(y | x)
```

## Structural Causal Models (SCM)

```python
class StructuralCausalModel:
    """
    SCM: Variables, causal graph, structural equations.
    """
    
    def __init__(self, variables: List[str], graph: DAG, equations: Dict):
        self.variables = variables
        self.graph = graph  # Directed Acyclic Graph
        self.equations = equations  # X_i = f_i(parents(X_i), U_i)
    
    def intervene(self, intervention: Dict[str, float]) -> "SCM":
        """
        do(X = x): Replace equation for X with constant.
        
        This breaks incoming edges to X.
        """
        new_equations = self.equations.copy()
        for var, value in intervention.items():
            new_equations[var] = lambda *_: value
        
        new_graph = self.graph.remove_edges_to(intervention.keys())
        
        return StructuralCausalModel(
            self.variables, new_graph, new_equations
        )
    
    def counterfactual(self, evidence: Dict, intervention: Dict) -> Dict:
        """
        Counterfactual: What would Y be if X had been x, given we observed evidence?
        
        Three steps:
        1. Abduction: Infer noise terms from evidence
        2. Action: Apply intervention
        3. Prediction: 