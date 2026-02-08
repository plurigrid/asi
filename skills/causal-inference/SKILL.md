---
name: causal-inference
description: "Bengio's causal inference for AI: Interventional reasoning, counterfactuals, and System 2 deep learning. World models with causal structure."
metadata:
  trit: 0
  polarity: ERGODIC
  source: 'Bengio et al. 2019: Towards Causal Representation Learning'
  technologies:
  - Python
  - DoWhy
  - CausalML
  - Pyro
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
        3. Prediction: Compute counterfactual outcome
        """
        # Step 1: Abduction - infer noise terms U
        noise_terms = self.abduct_noise(evidence)
        
        # Step 2: Action - apply intervention
        intervened_scm = self.intervene(intervention)
        
        # Step 3: Prediction - forward propagate with inferred noise
        counterfactual_world = intervened_scm.forward(noise_terms)
        
        return counterfactual_world


class CausalDiscovery:
    """
    Learn causal structure from data.
    """
    
    def __init__(self, data: pd.DataFrame):
        self.data = data
        
    def pc_algorithm(self) -> DAG:
        """
        PC Algorithm: Constraint-based causal discovery.
        
        1. Start with complete undirected graph
        2. Remove edges based on conditional independence tests
        3. Orient edges using v-structures and rules
        """
        from causallearn.search.ConstraintBased.PC import pc
        
        result = pc(self.data.values)
        return result.G
    
    def gflownet_discovery(self) -> Distribution[DAG]:
        """
        Use GFlowNet to sample DAGs proportional to likelihood.
        
        This gives a DISTRIBUTION over causal graphs,
        properly accounting for uncertainty.
        """
        from gflownet import CausalDAGGFlowNet
        
        gfn = CausalDAGGFlowNet(n_variables=len(self.data.columns))
        gfn.train(reward=lambda g: self.bayesian_score(g))
        
        # Sample multiple DAGs
        dag_samples = [gfn.sample() for _ in range(1000)]
        return dag_samples
```

## System 2 Deep Learning

```python
class System2Network:
    """
    Bengio's vision: Combine System 1 (fast) with System 2 (slow).
    
    System 1: Neural pattern matching (current DL)
    System 2: Deliberate causal reasoning (compositional, symbolic)
    """
    
    def __init__(self):
        self.system1 = NeuralNetwork()  # Fast intuition
        self.system2 = CausalReasoner()  # Slow reasoning
        self.attention = DynamicAttention()  # Which to use when
    
    def forward(self, x: Tensor, requires_reasoning: bool = False) -> Tensor:
        """
        Hybrid forward pass.
        """
        # System 1: quick answer
        fast_answer = self.system1(x)
        
        if not requires_reasoning:
            return fast_answer
        
        # System 2: verify/refine via causal reasoning
        slow_answer = self.system2.reason(x, fast_answer)
        
        # Combine based on confidence
        confidence = self.attention(x, fast_answer, slow_answer)
        return confidence * fast_answer + (1 - confidence) * slow_answer
    
    def causal_attention(self, query: Tensor) -> Tensor:
        """
        Attention guided by causal relevance, not just correlation.
        
        Standard attention: A(Q, K, V) = softmax(QK^T/√d) V
        Causal attention: Weight by causal effect, not correlation
        """
        correlational_weights = self.compute_attention(query)
        causal_effects = self.system2.estimate_effects(query)
        
        # Reweight by causal importance
        causal_weights = correlational_weights * causal_effects
        return self.apply_attention(causal_weights)
```

## GF(3) Triads

```
# Causal-Categorical Triad
sheaf-cohomology (-1) ⊗ causal-inference (0) ⊗ gflownet (+1) = 0 ✓

# System 2 Triad
proofgeneral-narya (-1) ⊗ causal-inference (0) ⊗ forward-forward-learning (+1) = 0 ✓

# World Model Triad
persistent-homology (-1) ⊗ causal-inference (0) ⊗ self-evolving-agent (+1) = 0 ✓
```

## Integration with Interaction Entropy

```ruby
module CausalInference
  def self.intervene(interaction_sequence, intervention)
    # Build causal graph from interaction sequence
    graph = build_causal_graph(interaction_sequence)
    
    # Apply intervention
    intervened = graph.do(intervention)
    
    # Predict outcome
    outcome = intervened.forward_propagate
    
    {
      original_graph: graph,
      intervention: intervention,
      predicted_outcome: outcome,
      trit: 0  # Coordinator (bridges observational and interventional)
    }
  end
  
  def self.counterfactual(interaction, alternative_action)
    # What would have happened if we'd done alternative_action?
    noise = abduct_noise(interaction)
    intervened = apply_intervention(alternative_action)
    counterfactual_outcome = propagate_with_noise(intervened, noise)
    
    {
      actual_outcome: interaction[:outcome],
      counterfactual_outcome: counterfactual_outcome,
      difference: interaction[:outcome] - counterfactual_outcome
    }
  end
end
```

## Key Properties

1. **Invariance**: Causal mechanisms are stable across environments
2. **Modularity**: Can change one mechanism without affecting others
3. **Compositionality**: Complex models from simple causal primitives
4. **Identifiability**: Can (sometimes) learn causal structure from data

## References

1. Bengio, Y. et al. (2019). "A Meta-Transfer Objective for Learning to Disentangle Causal Mechanisms."
2. Schölkopf, B. et al. (2021). "Toward Causal Representation Learning."
3. Pearl, J. (2009). *Causality: Models, Reasoning, and Inference*.
4. Bengio, Y. (2017). "The Consciousness Prior."
