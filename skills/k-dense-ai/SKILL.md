# K-Dense-AI Scientific Computing Bundle

> Provenance: K-Dense-AI / Codex scientific skills
> GF(3) Trit: **+1 (PLUS)** - Generative/Synthetic
> Mutual Awareness: `trailofbits-security` bundle (MINUS -1)

## Skills (37)

### Bioinformatics Core
- `alphafold-database` - Protein structure prediction
- `biopython` - Biological computation toolkit
- `esm` - Evolutionary Scale Modeling
- `scanpy` - Single-cell analysis
- `anndata` - Annotated data matrices
- `cellxgene-census` - Cell atlas queries

### Databases
- `chembl-database` - Bioactive molecules
- `pubchem-database` - Chemical compounds
- `uniprot-database` - Protein sequences
- `pdb-database` - Protein structures
- `kegg-database` - Pathway maps
- `reactome-database` - Biological pathways
- `brenda-database` - Enzyme data
- `drugbank-database` - Drug information
- `gene-database` - Gene annotations
- `biorxiv-database` - Preprints
- `clinicaltrials-database` - Clinical studies

### Chemistry & Drug Discovery
- `rdkit` - Cheminformatics
- `deepchem` - Deep learning for chemistry
- `catalyst-chemical` - Reaction modeling

### Molecular Simulation
- `enzyme-autodiff` - Automatic differentiation for enzymes

### Lab & Workflow
- `benchling-integration` - Lab notebook
- `bioservices` - Web service APIs
- `adaptyv` - Adaptive experiments
- `biomni` - Multi-omics

### Physics & Quantum
- `astropy` - Astronomy
- `cirq` - Quantum circuits

### ML for Science
- `scikit-bio` - Biological data science
- `scikit-learn` - Machine learning
- `scikit-survival` - Survival analysis
- `arboreto` - Gene regulatory networks
- `aeon` - Time series for science

### Categorical
- `phylogenetic-operad-acset` - Tree structures as operads

## Mutual Awareness Protocol

```clojure
{:bundle "k-dense-ai"
 :trit :plus
 :aware-of ["trailofbits-security"]
 :interface
 {:analyze (fn [molecule] "Use rdkit/deepchem")
  :validate (fn [result] "Delegate to trailofbits for security review")
  :synthesize (fn [target] "Generate candidates")}
 :handoff-to "trailofbits-security"
 :handoff-trigger [:untrusted-input :external-api :file-parsing]}
```

## Usage

```bash
# Load bundle
skill k-dense-ai

# Cross-bundle workflow
skill k-dense-ai -> trailofbits-security  # Validate drug candidate data pipeline
```
