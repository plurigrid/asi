# ADHD-Endocannabinoid Olog: A Categorical Ontology for Precision Dysregulation Theory

## Meta-Information
- **Created**: 2026-01-27
- **Framework**: Applied Category Theory (Olog formalism)
- **Integration Target**: CatColab / Topos Institute
- **Julia Packages**: Catlab.jl, ACSets.jl, StructuredDecompositions.jl, AlgebraicDynamics.jl

---

## 1. OLOG TYPES (Objects in the Category)

### 1.1 Core Entity Types

```
Type: Patient
  - Description: "An individual with measurable neurobiological parameters"
  - Properties: age, biological_sex, ADHD_subtype, comorbidities

Type: EndocannabinoidMeasure  
  - Description: "A quantified ECS parameter from a specific tissue/measurement"
  - Properties: parameter_name, value, unit, method, tissue_source

Type: CognitiveFunction
  - Description: "A measurable cognitive domain affected by ECS"
  - Properties: domain, score, z_score, test_used

Type: MechanisticHypothesis
  - Description: "A proposed causal pathway from ECS to phenotype"
  - Properties: name, mechanism, prior_probability, posterior_probability

Type: NeuralCircuit
  - Description: "An anatomical circuit modulated by endocannabinoids"
  - Properties: nodes, connections, dominant_neurotransmitter

Type: PrecisionParameter
  - Description: "A parameter controlling prediction confidence in active inference"
  - Properties: β_value, modulator, brain_region

Type: GenderModulator
  - Description: "A sex-specific factor affecting ECS function"
  - Properties: hormone, receptor_affinity, expression_pattern
```

### 1.2 Hierarchical Types (2-3-5-7 Decomposition)

```
Level 2 (Binary):
  Type: ADHDPresence ∈ {Present, Absent}
  Type: ECSBalance ∈ {Balanced, Imbalanced}

Level 3 (Ternary/GF(3)):
  Type: ECSTone ∈ {Hypoactive(-1), Balanced(0), Hyperactive(+1)}
  Type: PrecisionState ∈ {Underweighted(-1), Calibrated(0), Overweighted(+1)}
  Type: RewardSensitivity ∈ {Blunted(-1), Normal(0), Hypersensitive(+1)}

Level 5 (Quinary):
  Type: CognitiveDomain ∈ {
    Attention,
    ImpulseControl,
    WorkingMemory,
    EmotionalRegulation,
    RewardProcessing
  }

Level 7 (Septenary):
  Type: ECSNode ∈ {
    CB1_prefrontal,
    CB1_striatal,
    CB2_immune,
    AEA_tone,
    2AG_tone,
    FAAH_activity,
    MAGL_activity
  }
```

---

## 2. OLOG MORPHISMS (Arrows/Aspects)

### 2.1 Structural Morphisms

```
Aspect: hasMeasurement : Patient → EndocannabinoidMeasure
  - Description: "Each patient has associated ECS measurements"
  - Cardinality: 1-to-many

Aspect: affectsCognition : EndocannabinoidMeasure → CognitiveFunction
  - Description: "ECS parameters influence cognitive outcomes"
  - Polarity: Signed (+/-)

Aspect: modulatedBy : PrecisionParameter → EndocannabinoidMeasure
  - Description: "Precision weighting is controlled by ECS tone"

Aspect: explains : MechanisticHypothesis → CognitiveFunction
  - Description: "A hypothesis predicts cognitive phenotype"

Aspect: testedBy : MechanisticHypothesis → EndocannabinoidMeasure
  - Description: "A hypothesis is validated by specific measurements"

Aspect: dimorphicIn : EndocannabinoidMeasure → GenderModulator
  - Description: "ECS parameters vary by sex-specific factors"
```

### 2.2 Causal Morphisms (Interventional)

```
Intervention: do(FAAH_activity = low) → AEA_tone
  - Effect: Increases anandamide bioavailability
  - Polarity: +

Intervention: do(AEA_tone = high) → CB1_activation
  - Effect: Enhanced CB1 receptor signaling
  - Polarity: +

Intervention: do(CB1_prefrontal = activated) → ImpulseControl
  - Effect: Improved response inhibition
  - Polarity: +

Intervention: do(Estrogen = high) → CB1_expression
  - Effect: Upregulates CB1 in reward circuits
  - Polarity: +
```

### 2.3 Counterfactual Morphisms

```
Counterfactual: CF(FAAH_normal | FAAH_overexpressed) → ΔADHD_severity
  - Query: "What would ADHD severity be if FAAH were normalized?"
  - Computation: E[Y | do(X=x)] - E[Y | X=x_observed]

Counterfactual: CF(CB1_male | CB1_female) → ΔRewardSensitivity
  - Query: "What is the sex-specific effect of CB1 expression on reward?"
  - Controls for: Estrogen, Testosterone, FAAH polymorphism
```

---

## 3. COMMUTATIVE DIAGRAMS (Olog Axioms)

### 3.1 The ECS-Precision Triangle

```
                    ECSMeasure
                    /         \
           affects /           \ modulatedBy
                  ↓             ↓
        CognitiveFunction ←── PrecisionParameter
                      calibrates

Axiom: For all cognitive functions f:
  affects(ecs, f) = calibrates(modulatedBy(ecs), f)
  
Interpretation: ECS affects cognition THROUGH precision modulation
```

### 3.2 The Gender Dimorphism Square

```
        Patient ────hasSex────→ BiologicalSex
           |                         |
    hasMeasure                   modulates
           ↓                         ↓
    ECSMeasure ←───dimorphicIn─── GenderModulator

Axiom: hasMeasure ∘ dimorphicIn = modulates ∘ hasSex
  
Interpretation: Sex affects ECS measures through hormonal modulation
```

### 3.3 The Causal Intervention Cube

```
                 FAAH_activity
                     |
              (intervention)
                     ↓
     AEA_tone ────────→ CB1_activation
         |                    |
    (mediation)          (mediation)
         ↓                    ↓
  PrecisionWeight ───→ ImpulseControl
                    
Path Independence Axiom:
  do(FAAH=x) → AEA → CB1 → Impulse  ≡  do(FAAH=x) → AEA → Precision → Impulse
```

---

## 4. GF(3) CONSERVATION STRUCTURE

### 4.1 Trit Assignments for ECS Nodes

```julia
# GF(3) = {-1, 0, +1} with modular arithmetic

const ECS_TRITS = Dict(
    :CB1_prefrontal  => +1,  # Source (synthesis)
    :CB1_striatal    => +1,  # Source
    :CB2_immune      => -1,  # Sink (degradation)
    :AEA_tone        =>  0,  # Ergodic (balance)
    :2AG_tone        =>  0,  # Ergodic
    :FAAH_activity   => -1,  # Sink (catabolism)
    :MAGL_activity   => -1   # Sink (catabolism)
)

# Verification: sum(trits) = (+1) + (+1) + (-1) + 0 + 0 + (-1) + (-1) = -1
# Not balanced! Need to add one +1 node for conservation

# Additional node for balance:
const ECS_TRITS_BALANCED = merge(ECS_TRITS, Dict(
    :CB1_hippocampal => +1  # Add source node
))
# Now: (+1)*3 + (-1)*3 + 0*2 = 0 ≡ 0 (mod 3) ✓
```

### 4.2 Tripartite Decomposition

```
MINUS Partition (Analysis/Degradation):
  - FAAH_activity: Hydrolyzes anandamide
  - MAGL_activity: Hydrolyzes 2-AG  
  - CB2_immune: Neuroinflammatory modulation

ERGODIC Partition (Balance/Homeostasis):
  - AEA_tone: Tonic anandamide signaling
  - 2AG_tone: Tonic 2-AG signaling

PLUS Partition (Synthesis/Production):
  - CB1_prefrontal: Executive function receptor
  - CB1_striatal: Reward/motor receptor
  - CB1_hippocampal: Memory receptor
```

---

## 5. CATCOLAB INSTANTIATION SCHEMA

### 5.1 Signed Category (Causal Loop) Representation

```typescript
// CatColab causal-loop theory instantiation

const ADHD_ECS_CausalLoop = {
  theory: "causal-loop",
  name: "ADHD_ECS_Feedback_Network",
  
  variables: [
    { id: "FAAH", name: "FAAH Expression", domain: "continuous" },
    { id: "AEA", name: "Anandamide Tone", domain: "continuous" },
    { id: "CB1_pfc", name: "CB1 Prefrontal", domain: "continuous" },
    { id: "precision", name: "Precision Weight", domain: "continuous" },
    { id: "impulse", name: "Impulse Control", domain: "continuous" },
    { id: "adhd", name: "ADHD Severity", domain: "continuous" },
    { id: "estrogen", name: "Estrogen Level", domain: "continuous" }
  ],
  
  links: [
    { from: "FAAH", to: "AEA", polarity: "-", delay: 0 },
    { from: "AEA", to: "CB1_pfc", polarity: "+", delay: 0 },
    { from: "CB1_pfc", to: "precision", polarity: "+", delay: 0 },
    { from: "precision", to: "impulse", polarity: "+", delay: 0 },
    { from: "impulse", to: "adhd", polarity: "-", delay: 0 },
    { from: "estrogen", to: "CB1_pfc", polarity: "+", delay: 0 },
    { from: "adhd", to: "estrogen", polarity: "-", delay: 1 }  // Feedback
  ],
  
  loops: [
    {
      name: "R1_FAAH_ADHD",
      type: "reinforcing",
      path: ["FAAH", "AEA", "CB1_pfc", "precision", "impulse", "adhd"],
      interpretation: "FAAH overexpression reinforces ADHD severity"
    },
    {
      name: "B1_Estrogen_Buffering",
      type: "balancing", 
      path: ["adhd", "estrogen", "CB1_pfc", "precision", "impulse", "adhd"],
      interpretation: "Estrogen partially buffers ADHD through CB1 upregulation"
    }
  ]
};
```

### 5.2 Olog Representation

```typescript
// CatColab simple-olog theory instantiation

const ADHD_ECS_Olog = {
  theory: "simple-olog",
  name: "ADHD_ECS_Ontology",
  
  types: [
    { id: "Patient", description: "Individual with ADHD phenotype" },
    { id: "ECSMeasure", description: "Endocannabinoid measurement" },
    { id: "CogFunc", description: "Cognitive function score" },
    { id: "Hypothesis", description: "Mechanistic hypothesis" },
    { id: "Sex", description: "Biological sex category" }
  ],
  
  aspects: [
    { 
      from: "Patient", to: "ECSMeasure", 
      name: "has_measurement",
      description: "Patient has ECS parameter measured"
    },
    {
      from: "ECSMeasure", to: "CogFunc",
      name: "affects",
      description: "ECS parameter affects cognitive outcome"
    },
    {
      from: "Hypothesis", to: "CogFunc",
      name: "explains",
      description: "Hypothesis predicts cognitive phenotype"
    },
    {
      from: "Patient", to: "Sex",
      name: "has_sex",
      description: "Patient has biological sex"
    },
    {
      from: "Sex", to: "ECSMeasure",
      name: "modulates",
      description: "Sex modulates ECS expression"
    }
  ],
  
  facts: [
    "Every Patient has_measurement some ECSMeasure",
    "Every ECSMeasure affects some CogFunc",
    "has_measurement . affects = has_sex . modulates . affects"
  ]
};
```

---

## 6. STRUCTURAL CAUSAL MODEL (Pearl SCM)

### 6.1 Formal SCM Definition

```
ADHD-ECS Structural Causal Model M = (U, V, F, P(U))

Exogenous Variables U:
  - U_genetic: Genetic background (FAAH polymorphisms, CNR1 variants)
  - U_inflammatory: Neuroinflammatory factors
  - U_hormonal: Baseline hormone levels (pre-puberty)
  - U_env: Environmental factors (stress, nutrition)

Endogenous Variables V:
  - FAAH_expr: FAAH enzyme expression
  - AEA_tone: Anandamide concentration
  - CB1_pfc: CB1 receptor availability (prefrontal)
  - CB1_str: CB1 receptor availability (striatum)
  - precision_β: Precision weighting parameter
  - impulse: Impulse control score
  - attention: Attention score
  - ADHD_severity: Combined ADHD severity
  - estrogen: Circulating estrogen
  - testosterone: Circulating testosterone

Structural Equations F:
  FAAH_expr     = 1.0 + 0.3*U_genetic + 0.1*testosterone + ε₁
  AEA_tone      = 10.0 - 1.5*FAAH_expr + 0.2*estrogen + ε₂
  CB1_pfc       = 2.0 + 0.5*AEA_tone + 0.3*estrogen - 0.2*U_inflammatory + ε₃
  CB1_str       = 2.5 + 0.6*AEA_tone + 0.1*testosterone + ε₄
  precision_β   = 1.0 + 0.4*CB1_pfc + 0.2*CB1_str + ε₅
  impulse       = 50 + 8*precision_β - 3*U_inflammatory + ε₆
  attention     = 50 + 6*precision_β + 2*CB1_pfc + ε₇
  ADHD_severity = 100 - 0.4*impulse - 0.4*attention - 0.2*precision_β + ε₈

Prior P(U):
  U_genetic ~ N(0, 1)
  U_inflammatory ~ Exp(1)
  U_hormonal ~ N(0, 0.5)
  U_env ~ N(0, 1)
```

### 6.2 Counterfactual Queries

```
Q1: Average Treatment Effect of FAAH Inhibition
    ATE = E[ADHD | do(FAAH = 0.5)] - E[ADHD | do(FAAH = 2.0)]
    
Q2: Sex-Specific Effect of CB1 Modulation
    E[ADHD | do(CB1_pfc = 3), Sex=Female] - E[ADHD | do(CB1_pfc = 3), Sex=Male]

Q3: Mediation Analysis
    Direct effect of AEA on ADHD (not through precision):
    NDE = E[ADHD | do(AEA=high), do(precision=baseline)]
    
    Indirect effect through precision:
    NIE = E[ADHD | do(AEA=high)] - NDE

Q4: Transportability Query
    Given findings in rodent models, what is expected effect in humans?
    Uses do-calculus rule 3 with selection bias adjustment
```

---

## 7. JULIA IMPLEMENTATION SCHEMA

### 7.1 ACSet Schema Definition

```julia
using Catlab
using Catlab.CategoricalAlgebra

@present ADHDECSSchema(FreeSchema) begin
    # Objects (Types)
    Patient::Ob
    ECSMeasure::Ob
    CognitiveFunction::Ob
    MechanisticHypothesis::Ob
    NeuralCircuit::Ob
    BiologicalSex::Ob
    
    # Morphisms (Aspects)
    has_measure::Hom(Patient, ECSMeasure)
    affects::Hom(ECSMeasure, CognitiveFunction)
    explains::Hom(MechanisticHypothesis, CognitiveFunction)
    tested_by::Hom(MechanisticHypothesis, ECSMeasure)
    has_sex::Hom(Patient, BiologicalSex)
    modulates::Hom(BiologicalSex, ECSMeasure)
    in_circuit::Hom(ECSMeasure, NeuralCircuit)
    
    # Attributes
    Value::AttrType
    Score::AttrType
    Probability::AttrType
    Name::AttrType
    
    # Attribute assignments
    ecs_value::Attr(ECSMeasure, Value)
    ecs_name::Attr(ECSMeasure, Name)
    cog_score::Attr(CognitiveFunction, Score)
    cog_domain::Attr(CognitiveFunction, Name)
    hyp_name::Attr(MechanisticHypothesis, Name)
    hyp_prior::Attr(MechanisticHypothesis, Probability)
    hyp_posterior::Attr(MechanisticHypothesis, Probability)
    patient_id::Attr(Patient, Name)
    sex_name::Attr(BiologicalSex, Name)
end

@acset_type ADHDECSData(ADHDECSSchema, index=[:has_measure, :affects, :has_sex])
```

### 7.2 Sample Instantiation

```julia
adhd_data = @acset ADHDECSData begin
    # Patients
    Patient = 3
    patient_id = ["P001", "P002", "P003"]
    
    # Biological Sex
    BiologicalSex = 2
    sex_name = ["Male", "Female"]
    has_sex = [1, 2, 1]  # P001→Male, P002→Female, P003→Male
    
    # ECS Measurements (7 per patient = 21 total)
    ECSMeasure = 21
    ecs_name = repeat(["CB1_pfc", "CB1_str", "CB2_immune", 
                       "AEA", "2AG", "FAAH", "MAGL"], 3)
    ecs_value = [
        # Patient 1 (Male, ADHD)
        0.8, 0.7, 1.2, 0.5, 0.6, 1.8, 1.5,
        # Patient 2 (Female, Control)
        1.2, 1.1, 0.8, 1.0, 0.9, 1.0, 1.0,
        # Patient 3 (Male, Control)
        1.1, 1.0, 0.9, 0.9, 1.0, 1.1, 0.9
    ]
    has_measure = vcat(fill(1, 7), fill(2, 7), fill(3, 7))
    
    # Sex modulation (simplified)
    modulates = [1, 1, 1, 1, 1, 1, 1,  # Male affects first 7
                 8, 9, 10, 11, 12, 13, 14]  # Female affects next 7
    
    # Cognitive Functions
    CognitiveFunction = 5
    cog_domain = ["Attention", "ImpulseControl", "WorkingMemory", 
                  "EmotionalReg", "RewardProcessing"]
    cog_score = [35.0, 40.0, 45.0, 50.0, 38.0]  # Population means
    
    # ECS → Cognitive mappings
    affects = [1, 1, 2, 2, 3, 4, 5]  # Simplified
    
    # Mechanistic Hypotheses
    MechanisticHypothesis = 4
    hyp_name = [
        "FAAH_Overexpression",
        "CB1_Deficiency_PFC",
        "Precision_Dysregulation",
        "Reward_Calibration_Deficit"
    ]
    hyp_prior = [0.25, 0.25, 0.25, 0.25]
    hyp_posterior = [0.0, 0.0, 0.0, 0.0]  # To be updated
    
    explains = [2, 1, 1, 5]  # Each hypothesis explains a cognitive domain
    tested_by = [6, 1, 1, 4]  # Each hypothesis tested by an ECS measure
    
    # Neural Circuits
    NeuralCircuit = 3
    in_circuit = repeat([1, 1, 2, 3, 3, 3, 3], 3)
end
```

---

## 8. STRUCTURED DECOMPOSITION APPLICATION

### 8.1 Tree Decomposition for ADHD-ECS

```julia
using StructuredDecompositions

# Define the decomposition graph (skeleton)
decomp_graph = @acset Graph begin
    V = 4  # Four bags
    E = 3  # Three edges (tree structure)
    src = [1, 2, 3]
    tgt = [2, 3, 4]
end

# Bag contents (following 2-3-5-7 hierarchy)
bags = [
    # Bag 1: Level 2 (Binary phenotype)
    Set([:ADHD_present, :ADHD_absent]),
    
    # Bag 2: Level 3 (Ternary ECS state)
    Set([:ECS_hypoactive, :ECS_balanced, :ECS_hyperactive]),
    
    # Bag 3: Level 5 (Quinary cognitive domains)
    Set([:Attention, :Impulse, :WM, :EmotReg, :Reward]),
    
    # Bag 4: Level 7 (Septenary ECS nodes)
    Set([:CB1_pfc, :CB1_str, :CB2_imm, :AEA, :2AG, :FAAH, :MAGL])
]

# Adhesion (overlap between adjacent bags)
adhesions = [
    Set([:ECS_state_binary]),    # Bag 1-2 adhesion
    Set([:precision_trit]),      # Bag 2-3 adhesion
    Set([:cognitive_trit])       # Bag 3-4 adhesion
]

# Create the structured decomposition
adhd_decomp = StrDecomp(
    decomp_shape = decomp_graph,
    diagram = bags,
    adhesions = adhesions,
    decomp_type = Decomposition
)
```

### 8.2 Sheaf Decision Problem

```julia
# Define a sheaf predicate: "Is ADHD explainable by ECS deficit?"
function ecs_explains_adhd(local_data)
    # Check if local ECS measures correlate with cognitive deficits
    faah = get(local_data, :FAAH, 1.0)
    aea = get(local_data, :AEA, 1.0)
    cb1 = get(local_data, :CB1_pfc, 1.0)
    
    # ADHD likely if: high FAAH, low AEA, low CB1
    ecs_deficit_score = faah - aea - cb1
    return ecs_deficit_score > 0.5
end

# Run sheaf decision on the decomposition
result = decide_sheaf_tree_shape(
    adhd_decomp,
    ecs_explains_adhd
)

# Result: true if ADHD is globally explainable by ECS deficit
# Uses the gluing axiom to verify local → global consistency
```

---

## 9. ACTIVE INFERENCE FORMULATION

### 9.1 Precision-Weighted Prediction Error

```julia
# Active inference for ADHD-ECS
struct ADHDActiveInferenceAgent
    # Beliefs about hidden states
    μ_ECS::Vector{Float64}      # Expected ECS parameters
    Σ_ECS::Matrix{Float64}      # Uncertainty covariance
    
    # Precision parameters (modulated by ECS)
    β_sensory::Float64          # Sensory precision
    β_cognitive::Float64        # Cognitive precision
    β_reward::Float64           # Reward precision
    
    # Model parameters
    A::Matrix{Float64}          # Likelihood mapping (hidden → observed)
    B::Matrix{Float64}          # Transition dynamics
end

function prediction_error(agent::ADHDActiveInferenceAgent, observation::Vector{Float64})
    # Precision-weighted prediction error
    predicted = agent.A * agent.μ_ECS
    error = observation - predicted
    
    # Weight by precision (ECS-modulated)
    Π = Diagonal([agent.β_sensory, agent.β_cognitive, agent.β_reward])
    weighted_error = Π * error
    
    return weighted_error
end

function update_beliefs!(agent::ADHDActiveInferenceAgent, error::Vector{Float64})
    # Gradient descent on free energy
    learning_rate = 0.1
    agent.μ_ECS += learning_rate * agent.A' * error
end

function free_energy(agent::ADHDActiveInferenceAgent, obs::Vector{Float64})
    error = prediction_error(agent, obs)
    
    # Accuracy term (prediction error)
    accuracy = 0.5 * dot(error, error)
    
    # Complexity term (KL divergence from prior)
    prior_μ = ones(length(agent.μ_ECS))  # Prior: balanced ECS
    complexity = 0.5 * sum((agent.μ_ECS - prior_μ).^2)
    
    return accuracy + 0.1 * complexity
end
```

### 9.2 ADHD as Precision Dysregulation

```julia
# ADHD model: reduced precision modulation
function create_adhd_agent()
    # Lower precision weights (broader uncertainty)
    return ADHDActiveInferenceAgent(
        μ_ECS = [0.8, 0.7, 1.2, 0.5, 0.6, 1.8, 1.5],  # Imbalanced ECS
        Σ_ECS = 2.0 * I(7),  # Higher uncertainty
        β_sensory = 0.5,     # Reduced sensory precision
        β_cognitive = 0.3,   # Reduced cognitive precision
        β_reward = 0.2,      # Reduced reward precision
        A = rand(3, 7),
        B = rand(7, 7)
    )
end

function create_control_agent()
    # Normal precision weights
    return ADHDActiveInferenceAgent(
        μ_ECS = [1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0],  # Balanced ECS
        Σ_ECS = 0.5 * I(7),  # Lower uncertainty
        β_sensory = 1.0,     # Normal sensory precision
        β_cognitive = 1.0,   # Normal cognitive precision
        β_reward = 1.0,      # Normal reward precision
        A = rand(3, 7),
        B = rand(7, 7)
    )
end

# Prediction: ADHD agent has higher free energy (worse model fit)
# and slower belief updating (poor learning from errors)
```

---

## 10. COMPETITOR THEORY: Endocannabinoid Precision Dysregulation Syndrome (EPDS)

### 10.1 Core Thesis

> **ADHD is not a deficit of attention or impulse control per se, but rather a dysregulation of the precision-weighting system modulated by the endocannabinoid system, leading to suboptimal allocation of cognitive resources.**

### 10.2 Key Claims

1. **Primary Deficit**: Reduced or chaotic endocannabinoid tone (AEA/2-AG)
   - Evidence: FAAH overexpression, CB1 receptor downregulation

2. **Mechanistic Pathway**: ECS → Precision → Cognition
   - CB1 on prefrontal pyramidal neurons gates prediction precision
   - Low CB1 = broad uncertainty = cannot narrow attention

3. **Sex Dimorphism**: Estrogen-CB1 interaction
   - Females: Estrogen upregulates CB1 → protective factor
   - Males: Testosterone affects FAAH → vulnerability factor
   - Explains 3:1 male:female ADHD ratio

4. **Adaptive Reframe**: EPDS as "Exploratory Cognitive Type"
   - High entropy policy (broad exploration) ≠ disorder
   - Mismatch with structured modern environments

### 10.3 Testable Predictions

| Prediction | Measurement | Expected Result (ADHD vs Control) |
|------------|-------------|-----------------------------------|
| Lower AEA | Plasma LC-MS/MS | ↓ 20-40% |
| Higher FAAH | Brain PET ([18F]FMPEP-d2) | ↑ 15-30% |
| Lower CB1 VT | PET ([18F]MK-9470) | ↓ in striatum |
| Higher PE variance | MMN amplitude variability | ↑ trial-to-trial |
| Sex × CB1 interaction | PET + hormone panel | Estrogen buffers CB1 loss |

### 10.4 Therapeutic Implications

| Intervention | Target | Predicted Effect |
|--------------|--------|------------------|
| FAAH inhibitor (PF-04457845) | ↑ AEA tone | Improved precision, attention |
| Low-dose CBD | CB1 allosteric modulator | Stabilized precision weighting |
| CB1 agonist (nabilone) | Direct CB1 activation | Narrowed attention focus |
| Estrogen (females) | CB1 upregulation | Protective/therapeutic in females |

---

## 11. PACKAGE ECOSYSTEM INTEGRATION

### Required Julia Packages

```julia
# Core Category Theory
using Catlab                    # ACSet schemas, categorical algebra
using Catlab.CategoricalAlgebra # Functors, natural transformations
using Catlab.WiringDiagrams     # Compositional systems

# Structured Decomposition
using StructuredDecompositions  # Tree decomposition, sheaf problems

# Dynamics
using AlgebraicDynamics         # Open dynamical systems
using DifferentialEquations     # ODE/SDE solvers

# Probabilistic Inference
using Turing                    # Probabilistic programming
using Gen                       # Programmable inference

# Causal Inference
using CausalInference           # DAGs, conditional independence
# DoWhy via PyCall              # Causal effect estimation (Python interop)

# Visualization
using AlgebraicViz              # Category theory diagrams
using Makie                     # General plotting
```

### Integration Pipeline

```
[Data Collection]
     ↓
[ACSet Instantiation] ←── Catlab.jl
     ↓
[Structured Decomposition] ←── StructuredDecompositions.jl
     ↓
[Causal Discovery] ←── CausalInference.jl
     ↓
[Active Inference Model] ←── Custom + Turing.jl
     ↓
[Counterfactual Queries] ←── DoWhy interop
     ↓
[CatColab Visualization] ←── Export to TypeScript
```

---

## 12. REFERENCES

1. Russo, E.B. (2016). Clinical Endocannabinoid Deficiency Reconsidered. *Cannabis and Cannabinoid Research*.
2. Friston, K. et al. (2024). Scale-free active inference. *arXiv*.
3. Kenny, P. (2025). Perception/Action Divergence in Active Inference. *Working paper*.
4. Mathys, C. et al. (2014). Hierarchical Gaussian Filter. *Frontiers in Human Neuroscience*.
5. Spivak, D.I. (2014). Category Theory for Scientists. *MIT Press*.
6. Patterson, E. et al. (2022). Categorical Data Structures for Technical Computing. *Compositionality*.
