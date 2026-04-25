---
name: python-scientific-commons
description: "Atlas of scientific-Python tooling — molecular informatics, omics, bio-databases, PDE/ODE simulators, RL/optimization, medical imaging, and lab automation. Use when picking a Python library for a scientific workflow, threading data across cheminformatics/genomics/imaging pipelines, or locating an EBI-OLS bio-database client."
---

# python-scientific-commons

Atlas of scientific-Python skills, grouped by domain. Each domain's canonical entry sits at the top; the rest are siblings reachable by name.

## Cheminformatics / drug discovery

`rdkit` · `datamol` · `medchem` · `molfeat` · `chembl-database` · `drugbank-database` · `pubchem-database` · `zinc-database` · `pytdc` · `diffdock` · `deepchem`

Primary entry: `rdkit`. Modern wrappers: `datamol` · `medchem`. Featurization: `molfeat`. Datasets: `pytdc`. Docking: `diffdock`. Catalog DBs: `chembl-database` · `drugbank-database` · `pubchem-database` · `zinc-database`.

## Omics / single-cell / genomics

`scanpy` · `anndata` · `lamindb` · `cellxgene-census` · `pydeseq2` · `scvi-tools` · `scikit-bio` · `biopython` · `bioservices` · `gget` · `geniml` · `gtars` · `gene-database` · `geo-database` · `ensembl-database` · `clinvar-database` · `clinpgx-database` · `gwas-database` · `string-database` · `reactome-database` · `kegg-database` · `opentargets-database`

Primary entry: `scanpy`. Anndata core: `anndata` · `lamindb`. Tooling: `scvi-tools` · `pydeseq2`. Genomic intervals: `geniml` · `gtars`. Sequences/proteins: `biopython` · `bioservices` · `gget` · `scikit-bio`. Reference DBs: the `*-database` family above.

## Mass-spec / metabolomics

`pyopenms` · `matchms` · `metabolomics-workbench-database` · `hmdb-database` · `brenda-database`

Primary entry: `pyopenms`. Spectral matching: `matchms`. Reference: `metabolomics-workbench-database` · `hmdb-database` · `brenda-database`.

## Medical imaging / clinical

`pydicom` · `pathml` · `histolab` · `pyhealth` · `clinical-decision-support` · `clinical-reports` · `clinicaltrials-database` · `fda-database`

Primary entry: `pydicom`. Histology: `pathml` · `histolab`. EHR + reports: `pyhealth` · `clinical-decision-support` · `clinical-reports`. Clinical reference: `clinicaltrials-database` · `fda-database`.

## Structural biology / proteins / PDB

`alphafold-database` · `pdb-database` · `uniprot-database` · `vertex-ai-protein-interleave` · `vertex-protein-bisimulation` · `adaptyv`

Primary entry: `alphafold-database`. Structure refs: `pdb-database` · `uniprot-database`. Inference pipelines: `vertex-ai-protein-interleave` · `vertex-protein-bisimulation` · `adaptyv`.

## Lab automation / experimental

`opentrons-integration` · `pylabrobot` · `benchling-integration` · `protocolsio-integration` · `dnanexus-integration` · `omero-integration` · `latchbio-integration` · `labarchive-integration`

Primary entry: `pylabrobot`. Cloud-lab: `latchbio-integration` · `dnanexus-integration`. Imaging stores: `omero-integration`.

## Neuroscience

`neuropixels-analysis` · `etetoolkit` · `neurokit2` · `comrade-vlbi`

Primary entry: `neuropixels-analysis`. Phylogenetic trees: `etetoolkit`. Physiological signal proc: `neurokit2`.

## PDE / dynamics / sim

`fluidsim` · `simpy` · `flowio` · `langevin-dynamics` · `geomstats-fisher-rao` · `pymoo` · `astropy`

Primary entry: `fluidsim`. Discrete event: `simpy`. Cytometry-style flow data: `flowio`. Stochastic dynamics: `langevin-dynamics`. Manifold geometry: `geomstats-fisher-rao`. Multi-objective: `pymoo`.

## ML / RL / optimization

`pytorch-lightning` · `transformers` · `vllm-deployment` · `torch_geometric` · `pufferlib` · `stable-baselines3` · `gym` · `gflownet` · `jaxlife-open-ended` · `multidispatch-rl` · `umap-learn` · `vaex` · `dask` · `polars` · `seaborn` · `matplotlib` · `plotly` · `scikit-learn` · `scikit-survival` · `statsmodels` · `pymc`

Primary entry: `pytorch-lightning`. LLM serving: `vllm-deployment` · `transformers`. Graph NN: `torch_geometric`. RL: `pufferlib` · `stable-baselines3` · `gym` · `gflownet`. ML-on-large-data: `dask` · `vaex` · `polars`. Embedding viz: `umap-learn`. Bayes: `pymc`. Stats: `statsmodels` · `scikit-learn` · `scikit-survival`. Plotting: `seaborn` · `matplotlib` · `plotly`.

## Quantum

`qutip` · `qiskit` · `cirq` · `pennylane`

Primary entry: `qiskit`. Open-system: `qutip`. Variational: `pennylane` · `cirq`.

## Cross-family threading

- **omics → ML**: `anndata` ↔ `scvi-tools` ↔ `pytorch-lightning` (probabilistic single-cell models)
- **chem → ML**: `rdkit` ↔ `molfeat` ↔ `torch_geometric` (graph molecule featurization)
- **structures → AI**: `alphafold-database` ↔ `vertex-ai-protein-interleave` ↔ `adaptyv`
- **dynamics → categorical**: `langevin-dynamics` ↔ `geomstats-fisher-rao` ↔ `koopman-generator` (Para(Optic) `▷` Play layer)
- **databases → DuckDB**: any `*-database` skill loads cleanly via `duckdb-guard` + `read_csv` for tabular reference data

## yb-translator parable

```
CONCEPT: scientific-Python tooling stack
BIOLOGY: cellular metabolic network with substrate-channeling enzyme complexes
ONTOLOGY: GO — metabolic process (GO:0008152), catalytic activity (GO:0003824),
          protein-containing complex (GO:0032991)
EXAMPLE: rdkit (input substrate processing) ⇒ molfeat (featurization, like ATP-coupling)
         ⇒ torch_geometric (transformation enzyme) ⇒ scvi-tools (model fitting,
         downstream regulation). Each tool is one enzyme; the pipeline is the network.
```

## Use when

- Picking the right scientific-Python library for a task
- Threading data across cheminformatics/omics/imaging substrates
- Locating an EBI/UniProt/Ensembl reference DB client
- Wrapping a Python pipeline as a Para(Optic) atom with `langevin-dynamics`-style forward + Bayesian backward

## Atlas family

- **REPL substrate**: `repl-commons`
- **Categorical substrate**: `para-mensch-commons`
- **Protocol substrate**: `acp-commons`
- **Scientific-Python substrate**: this skill
