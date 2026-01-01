# 🧠💿 BRAIN DANCE: 2025-12-24b (Continuation)

Thread: [T-019b5207-300a-704b-b75e-8bdf2557254c](https://ampcode.com/threads/T-019b5207-300a-704b-b75e-8bdf2557254c)

> *extending the trace into chemistry, active inference, and GFlowNets*

## Synopsis

Exploration of skill-aligned domains not yet covered: **chemistry MCP servers**, **chemical reaction networks**, **active inference**, and **GFlowNets for molecule generation**.

---

## Phase 3c: Chemistry & Synthesis MCP

**Exa call:**
```python
mcp__exa__web_search_exa(
    query="site:github.com MCP server chemical synthesis reaction networks XDL chemputer molecular",
    numResults=10
)
```

**Discovered:**

### Chemistry MCP Servers
| Repo | Description |
|------|-------------|
| [OSU-NLP-Group/ChemMCP](https://github.com/OSU-NLP-Group/ChemMCP) | Chemistry toolkit → AI co-scientist |
| [Augmented-Nature/ChEMBL-MCP-Server](https://github.com/Augmented-Nature/ChEMBL-MCP-Server) | ChEMBL database access via MCP |
| [JackKuo666/ChEMBL-MCP-Server](https://github.com/JackKuo666/ChEMBL-MCP-Server) | ChEMBL search via MCP |
| [JackKuo666/PubChem-MCP-Server](https://github.com/JackKuo666/PubChem-MCP-Server) | PubChem compound info via MCP |
| [ChatMol/molecule-mcp](https://github.com/ChatMol/molecule-mcp) | ⭐69 - Molecule MCP server |
| [s20ss/mcp_rdkit](https://github.com/s20ss/mcp_rdkit) | RDKit cheminformatics via MCP |
| [QuentinCody/catalysishub-mcp-server](https://github.com/QuentinCody/catalysishub-mcp-server) | Catalysis data via MCP |

### Cronin Group (Chemputer/XDL)
| Repo | Description |
|------|-------------|
| [croningp/ChemputerAntiviralXDL](https://github.com/croningp/ChemputerAntiviralXDL) | XDL files for antiviral synthesis |

### Synthesis Planning
| Repo | Description |
|------|-------------|
| [Laboratoire-de-Chemoinformatique/SynPlanner](https://github.com/laboratoire-de-chemoinformatique/synplanner) | Computer-aided synthesis planning |

**Skill alignment:** `turing-chemputer`, `crn-topology`, `assembly-index`

---

## Phase 3d: Chemical Reaction Networks

**Exa call:**
```python
mcp__exa__web_search_exa(
    query="site:github.com/topics chemical-reaction-networks systems-biology petri-nets dynamical-systems",
    numResults=10
)
```

**Discovered:**

### Julia CRN Packages
| Repo | Stars | Description |
|------|-------|-------------|
| [AlgebraicJulia/Petri.jl](https://github.com/AlgebraicJulia/Petri.jl) | ⭐43 | Petri net modeling framework |
| [anj1/ChemicalReactionNetworks.jl](https://github.com/anj1/ChemicalReactionNetworks.jl) | - | CRN theory algorithms |

### Python CRN Tools
| Repo | Stars | Description |
|------|-------|-------------|
| [etonello/crnpy](https://github.com/etonello/crnpy) | ⭐20 | Python CRN analysis library |
| [rxncon/rxncon](https://github.com/rxncon/rxncon) | ⭐9 | Reaction-contingency language |
| [PNNL-Comp-Mass-Spec/CRNT4SBML](https://github.com/PNNL-Comp-Mass-Spec/CRNT4SBML) | - | Bistability detection via SBML |
| [leihuang/rxnnet](https://github.com/leihuang/rxnnet) | - | Reaction network simulation |
| [Mathbiomed/CASTANET](https://github.com/Mathbiomed/CASTANET) | - | Analytical stationary distributions |

### Petri Net Optimization
| Repo | Description |
|------|-------------|
| [Jana-Marie-Weber/Reaction_net_opt](https://github.com/Jana-Marie-Weber/Reaction_net_opt) | RNFA + Petri net optimization |
| [max1s/Template-Based-Synthesis-Of-CRN](https://github.com/max1s/Template-Based-Synthesis-Of-Chemical-Reaction-Networks) | SMT-ODE solver for CRNs |

**Skill alignment:** `crn-topology`, `acsets-algebraic-databases` (Petri.jl uses ACSets)

---

## Phase 3e: Active Inference & Free Energy Principle

**Exa call:**
```python
mcp__exa__web_search_exa(
    query="site:github.com active-inference free-energy-principle predictive-processing bayesian-brain",
    numResults=10
)
```

**Discovered:**

### Active Inference Institute
| Repo | Description |
|------|-------------|
| [ActiveInferenceInstitute/CEREBRUM](https://github.com/activeinferenceinstitute/cerebrum) | Case-Enabled Reasoning Engine with Bayesian Representations |
| [ActiveInferenceInstitute/GEO-INFER](https://github.com/ActiveInferenceInstitute/GEO-INFER) | ⭐8 - Geospatial active inference |
| [ActiveInferenceInstitute/Parr_et_al_2022_ActInf_Textbook](https://github.com/ActiveInferenceInstitute/Parr_et_al_2022_ActInf_Textbook) | Active Inference textbook group |

### FEP/Active Inference Papers & Proofs
| Repo | Stars | Description |
|------|-------|-------------|
| [BerenMillidge/FEP_Active_Inference_Papers](https://github.com/BerenMillidge/FEP_Active_Inference_Papers) | - | Major FEP/active inference papers |
| [BerenMillidge/Predictive_Coding_Papers](https://github.com/BerenMillidge/Predictive_Coding_Papers) | - | Predictive coding paper collection |
| [snamjoshi/aif-proofs](https://github.com/snamjoshi/aif-proofs) | ⭐2 | Proofs for all active inference equations |
| [snamjoshi/aif-fep-db](https://github.com/snamjoshi/aif-fep-db) | ⭐5 | Active inference publication database |

### Implementations
| Repo | Description |
|------|-------------|
| [mbaltieri/GeneralisedFiltering](https://github.com/mbaltieri/GeneralisedFiltering) | Bayesian inversion of continuous hierarchical models |
| [open-thought/system-2-research](https://github.com/open-thought/system-2-research) | System 2 reasoning link collection |

**Skill alignment:** `active-inference`, `system2-attention`, `causal-inference`

---

## Phase 3f: GFlowNets for Molecule Generation

**Exa call:**
```python
mcp__exa__web_search_exa(
    query="site:github.com GFlowNet generative-flow-network causal-discovery molecule-generation",
    numResults=10
)
```

**Discovered:**

### Curated List
| Repo | Stars | Description |
|------|-------|-------------|
| [zdhNarsil/Awesome-GFlowNets](https://github.com/zdhNarsil/Awesome-GFlowNets) | ⭐493 | Curated GFlowNet resources |

### GFlowNet Implementations
| Repo | Stars | Description |
|------|-------|-------------|
| [mirunacrt/synflownet](https://github.com/mirunacrt/synflownet) | - | GFlowNet with chemical synthesis action space |
| [koziarskilab/RGFN](https://github.com/koziarskilab/rgfn) | ⭐26 | Synthesizable molecular generation (NeurIPS 2024) |
| [tsa87/TacoGFN-SBDD](https://github.com/tsa87/TacoGFN-SBDD) | - | Structure-based drug design (NeurIPS 2023) |
| [tsa87/cgflow](https://github.com/tsa87/cgflow) | ⭐4 | 3D molecule + synthesis pathway co-design (ICML 2025) |
| [garywei944/ChemFlow](https://github.com/garywei944/chemflow) | ⭐42 | Latent space structure discovery |
| [TheMatrixMaster/omics-guided-gfn](https://github.com/thematrixmaster/omics-guided-gfn) | ⭐12 | Multi-omic guided molecule search |
| [zarifikram/EGFN](https://github.com/zarifikram/EGFN) | ⭐5 | Evolution-guided GFlowNets |
| [flaviucipcigan/matgfn](https://github.com/flaviucipcigan/matgfn) | ⭐8 | Materials GFlowNet |
| [jule-c/flowr_root](https://github.com/jule-c/flowr_root) | ⭐39 | Flow-based generation |

**Skill alignment:** `gflownet`, `causal-inference`, `curiosity-driven`

---

## Summary

| Domain | Repos Discovered | Anchor Repo |
|--------|------------------|-------------|
| Chemistry MCP | 8 | ChatMol/molecule-mcp ⭐69 |
| CRN/Petri Nets | 10 | AlgebraicJulia/Petri.jl ⭐43 |
| Active Inference | 9 | ActiveInferenceInstitute org |
| GFlowNets | 10 | Awesome-GFlowNets ⭐493 |
| **Total** | **37** | - |

---

## New Topic Mappings

| Skill Cluster | GitHub Topics | Anchor Repos |
|---------------|---------------|--------------|
| Chemistry/Synthesis | cheminformatics, drug-discovery | ChemMCP, molecule-mcp |
| Reaction Networks | petri-nets, systems-biology | AlgebraicJulia/Petri.jl |
| Active Inference | active-inference, free-energy-principle | ActiveInferenceInstitute/* |
| GFlowNets | gflownet, generative-model | Awesome-GFlowNets ⭐493 |

---

## Integration Notes

### Chemistry MCP + turing-chemputer skill
```
# Enable Claude to:
1. Query ChEMBL/PubChem via MCP
2. Generate XDL synthesis plans
3. Validate via molecule-mcp
```

### CRN + acsets-algebraic-databases skill
```
# AlgebraicJulia/Petri.jl uses ACSets internally
# Direct integration with your acsets skills
```

### GFlowNet + gflownet skill
```
# Awesome-GFlowNets provides curated implementations
# synflownet bridges synthesis + generation
```
