---
name: vertex-ai-protein-interleave
description: >
  Bridge connecting Vertex AI / Google Cloud to protein-scale biology skills.
  Wires AlphaFold, ESM, DiffDock, DeepChem, and TorchDrug into Vertex AI
  Pipelines, Endpoints, and BigQuery genomics for protein design-predict-validate
  loops. Use when orchestrating protein engineering on GCP, deploying ESM as
  a managed endpoint, querying gnomAD via BigQuery, or running batch docking.
---

# Vertex AI x Protein-Scale Biology Interleave

Bridge connecting Google Cloud's orchestration (Vertex AI Pipelines, Endpoints, BigQuery) to the ASI protein skill cluster.

## ASI Protein Skill Cluster

```
alphafold-database (-1)  <- structure retrieval, pLDDT/PAE, 200M+ structures
esm (-1)                 <- ESM3/ESM C: sequence generation, inverse folding
diffdock (-1)            <- structure-based docking, pose prediction
deepchem (0)             <- ADMET prediction, GNNs, MoleculeNet, 30+ datasets
torchdrug (0)            <- GNNs, retrosynthesis, KG reasoning, 40+ datasets
adaptyv (+1)             <- wet-lab validation: binding, expression, stability
uniprot-database (0)     <- search, sequence retrieval, ID mapping
gget (+1)                <- rapid bioinformatics: AlphaFold, ARCHS4, Enrichr
```

Vertex AI adds: orchestration, serverless inference, genomic warehouse, cost optimization.

## 1. Design -> Predict -> Validate Loop (Vertex AI Pipelines)

```python
from kfp import dsl

@dsl.pipeline(name="protein-design-loop")
def protein_pipeline(target_sequence: str, iterations: int = 3):
    fold = dsl.ContainerOp(
        name="alphafold-predict",
        image="gcr.io/PROJECT/alphafold:latest",
        command=["python", "predict.py"],
        arguments=["--sequence", target_sequence, "--output", "/tmp/structure.pdb"]
    )
    dock = dsl.ContainerOp(
        name="diffdock",
        image="gcr.io/PROJECT/diffdock:latest",
        command=["python", "inference.py"],
        arguments=["--protein", fold.outputs["structure"], "--ligand", "/data/ligand.sdf"]
    ).after(fold)
    variants = dsl.ContainerOp(
        name="esm-inverse-fold",
        image="gcr.io/PROJECT/esm:latest",
        command=["python", "inverse_fold.py"],
        arguments=["--structure", fold.outputs["structure"], "--num_seqs", "100"]
    ).after(fold)
    filtered = dsl.ContainerOp(
        name="deepchem-admet",
        image="gcr.io/PROJECT/deepchem:latest",
        command=["python", "admet_screen.py"],
        arguments=["--sequences", variants.outputs["seqs"]]
    ).after(variants)
    dsl.ContainerOp(
        name="adaptyv-order",
        image="gcr.io/PROJECT/adaptyv-client:latest",
        command=["python", "order.py"],
        arguments=["--candidates", filtered.outputs["top_k"], "--assay", "binding"]
    ).after(filtered)
```

## 2. ESM Serverless Inference via Vertex AI Endpoints

```bash
docker build -t gcr.io/$PROJECT/esm-server:latest -f esm.Dockerfile .
docker push gcr.io/$PROJECT/esm-server:latest

gcloud ai models upload \
  --region=us-central1 \
  --display-name=esm3-protein-lm \
  --container-image-uri=gcr.io/$PROJECT/esm-server:latest \
  --container-predict-route=/predict \
  --container-health-route=/health

gcloud ai endpoints create --region=us-central1 --display-name=esm-endpoint
gcloud ai endpoints deploy-model ESM_ENDPOINT_ID \
  --region=us-central1 \
  --model=ESM_MODEL_ID \
  --machine-type=n1-standard-4 \
  --accelerator=count=1,type=nvidia-tesla-t4 \
  --min-replica-count=0 \
  --max-replica-count=4
```

## 3. BigQuery Genomics -> Protein ML Pipeline

```sql
-- gnomAD v3 in BigQuery: high-impact missense variants
SELECT
  reference_name, start_position, reference_bases, alternate_bases,
  vep.consequence_terms, vep.protein_id, vep.amino_acids,
  af.AF as allele_frequency
FROM `bigquery-public-data.gnomAD.v3_1_2_genomes`
CROSS JOIN UNNEST(vep) AS vep
CROSS JOIN UNNEST(allele_freq) AS af
WHERE
  'missense_variant' IN UNNEST(vep.consequence_terms)
  AND af.AF > 0.001
  AND vep.protein_id = @target_protein
ORDER BY af.AF DESC
LIMIT 10000;
```

```python
from google.cloud import aiplatform

aiplatform.init(project=PROJECT, location="us-central1")
job = aiplatform.CustomTrainingJob(
    display_name="gnomad-variant-phenotype",
    script_path="train_variant_model.py",
    container_uri="us-docker.pkg.dev/vertex-ai/training/pytorch-gpu.1-13:latest",
    requirements=["scikit-learn", "pandas", "biopython"],
)
model = job.run(
    dataset=aiplatform.TabularDataset(DATASET_ID),
    model_display_name="variant-phenotype-predictor",
    machine_type="n1-standard-8",
    accelerator_type="NVIDIA_TESLA_T4",
    accelerator_count=1,
)
```

## 4. AlphaFold Batch Inference Pipeline

```bash
gcloud ai pipelines run \
  --pipeline-job-spec-uri=gs://vertex-pipeline-components-public/alphafold/alphafold_pipeline.yaml \
  --parameter-values='
    project='"$PROJECT"',
    region=us-central1,
    input_fasta_gs_path=gs://my-bucket/sequences.fasta,
    output_gs_path=gs://my-bucket/alphafold-output/,
    use_gpu=true,
    model_preset=multimer
  '
```

```python
import duckdb
conn = duckdb.connect("asi.db")
conn.execute("""
  CREATE TABLE alphafold_batch AS
  SELECT * FROM read_json_auto('gs://my-bucket/alphafold-output/**/*.json')
""")
conn.execute("SELECT * FROM alphafold_batch WHERE mean_plddt > 90 ORDER BY mean_plddt DESC")
```

## 5. Vertex AI Matching Engine for Protein Similarity Search

```python
from google.cloud import aiplatform

index = aiplatform.MatchingEngineIndex.create_tree_ah_index(
    display_name="protein-embedding-index",
    contents_delta_uri=f"gs://{BUCKET}/protein-embeddings/",
    dimensions=1280,  # ESM3 embedding dimension
    approximate_neighbors_count=150,
    distance_measure_type="DOT_PRODUCT_DISTANCE",
)

endpoint = aiplatform.MatchingEngineIndexEndpoint.create(
    display_name="protein-similarity-endpoint",
    public_endpoint_enabled=True,
)
endpoint.deploy_index(index=index)
neighbors = endpoint.find_neighbors(
    deployed_index_id=DEPLOYED_INDEX_ID,
    queries=[query_embedding.tolist()],
    num_neighbors=10,
)
```

## 6. Cost-Optimized Batch Docking via Vertex AI

```python
batch_job = aiplatform.BatchPredictionJob.create(
    job_display_name="diffdock-batch-screen",
    model_name=DIFFDOCK_MODEL_ID,
    instances_format="jsonl",
    gcs_source=f"gs://{BUCKET}/ligand-protein-pairs.jsonl",
    predictions_format="jsonl",
    gcs_destination_prefix=f"gs://{BUCKET}/docking-results/",
    machine_type="n1-standard-8",
    accelerator_type="NVIDIA_TESLA_T4",
    accelerator_count=1,
    starting_replica_count=10,
    max_replica_count=50,
)
```

## Gap Registry

| Capability | ASI Skill | Vertex AI | Status |
|---|---|---|---|
| Structure retrieval (200M) | alphafold-database | Inference only | ASI owns retrieval |
| Protein sequence design | esm (ESM3) | Limited | ASI owns design |
| Molecular docking | diffdock | None | ASI owns this |
| ADMET prediction | deepchem | None | ASI owns this |
| Wet-lab validation | adaptyv | None | ASI owns this |
| BigQuery genomics | None | gnomAD, 1TB free | Vertex AI gap |
| Workflow orchestration | None | KFP Pipelines | Vertex AI gap |
| Scalable inference | Manual | Managed Endpoints | Vertex AI gap |
| Protein similarity search | None | Matching Engine | Vertex AI gap |
