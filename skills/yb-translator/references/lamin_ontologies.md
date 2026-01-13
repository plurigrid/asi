# Lamin.ai Bionty Ontologies Reference

**Source**: https://docs.lamin.ai/#ontologies

All 13 biological entity registries in lamin.ai are **coalgebras** with:
- **Comultiplication Δ**: `.children.all()` method
- **Counit ε**: `.name` attribute
- **Coassociativity**: Hierarchy traversal order independence
- **Counit laws**: Identity recovery via name extraction

---

## 1. Gene (HGNC, Ensembl, NCBI)

**Comultiplication**: gene → paralogs, orthologs
**Counit**: gene → gene.symbol
**API**: `bt.Gene.from_source(symbol="TP53")`
**Example**: TP53 → TP53 family members

---

## 2. Protein (UniProt)

**Comultiplication**: protein → isoforms, splice variants
**Counit**: protein → protein.name
**API**: `bt.Protein.from_source(ontology_id="UniProt:P04637")`
**Example**: P53 protein → isoforms (p53α, p53β, p53γ)

---

## 3. CellType (Cell Ontology - CL)

**Terms**: 2,932 cell types
**Comultiplication**: celltype → celltype.children.all()
**Counit**: celltype → celltype.name
**API**: `bt.CellType.from_source(ontology_id="CL:0000084")`
**Example**: T cell (CL:0000084) → CD4+ T cell, CD8+ T cell, γδ T cell

**Key bicomodule**: DN3 thymocyte (CL:0000807)
- Left coaction: Cell lineage hierarchy
- Right coaction: Tissue localization (thymus)

---

## 4. CellLine (Cell Line Ontology - CLO)

**Comultiplication**: cellline → derivatives, sublines
**Counit**: cellline → cellline.name
**API**: `bt.CellLine.from_source(ontology_id="CVCL:0030")`
**Example**: HeLa → HeLa S3, HeLa CCL-2, HeLa Kyoto

---

## 5. CellMarker

**Comultiplication**: marker → related markers, marker combinations
**Counit**: marker → marker.name
**API**: `bt.CellMarker.from_source(name="CD8")`
**Example**: CD8 → CD8A, CD8B

---

## 6. Tissue (UBERON Ontology)

**Terms**: 15,719 tissue types
**Comultiplication**: tissue → tissue.children.all()
**Counit**: tissue → tissue.name
**API**: `bt.Tissue.from_source(ontology_id="UBERON:0002048")`
**Example**: lung (UBERON:0002048) → right lung, left lung → lobes

**Coassociativity**: Direct to lobes = via left/right then lobes

---

## 7. Disease (MONDO, Human Disease Ontology)

**Terms**: 30,128 disease terms (MONDO)
**Comultiplication**: disease → disease.children.all()
**Counit**: disease → disease.name
**API**: `bt.Disease.from_source(ontology_id="MONDO:0005180")`
**Example**: Parkinson (MONDO:0005180) → early-onset, late-onset, juvenile

**Kan extensions**:
- Left Kan: Aggregate symptoms from subtypes → parent
- Right Kan: Distribute treatment from parent → subtypes

---

## 8. Phenotype (Human Phenotype Ontology - HPO)

**Comultiplication**: phenotype → phenotype.children.all()
**Counit**: phenotype → phenotype.name
**API**: `bt.Phenotype.from_source(ontology_id="HP:0000118")`
**Example**: Phenotypic abnormality → organ system abnormalities

---

## 9. Pathway (Gene Ontology, Pathway Ontology)

**Terms**: 47,856 terms (Gene Ontology)
**Comultiplication**: pathway → pathway.children.all()
**Counit**: pathway → pathway.name
**API**: `bt.Pathway.from_source(ontology_id="GO:0008150")`
**Example**: biological_process (GO:0008150) → metabolic, regulation, localization

**Coassociativity example**: carbohydrate metabolic process (GO:0005975)
- Path 1: biological → metabolic → carbohydrate_metabolic
- Path 2: biological → cellular → cellular_metabolic → carbohydrate_metabolic
- Both reach same term ✓

---

## 10. ExperimentalFactor (EFO)

**Comultiplication**: factor → factor.children.all()
**Counit**: factor → factor.name
**API**: `bt.ExperimentalFactor.from_source(ontology_id="EFO:0000001")`

---

## 11. DevelopmentalStage

**Comultiplication**: stage → next_stages (temporal decomposition)
**Counit**: stage → stage.name
**API**: `bt.DevelopmentalStage.from_source(...)`
**Example**: embryonic → fetal → postnatal → adult

**Sequential coalgebra**: Stages form temporal chain

---

## 12. Ethnicity (HANCESTRO)

**Comultiplication**: ethnicity → subgroups
**Counit**: ethnicity → ethnicity.name
**API**: `bt.Ethnicity.from_source(ontology_id="HANCESTRO:0004")`

---

## 13. Organism (NCBI Taxonomy)

**Comultiplication**: organism → organism.children.all()
**Counit**: organism → organism.name
**API**: `bt.Organism.from_source(ontology_id="NCBITaxon:40674")`
**Example**: Mammalia (40674) → Rodentia, Primates, Carnivora → families → species

**Phylogenetic tree as coalgebra**: Evolutionary hierarchy

---

## Common Operations (All Ontologies)

### Comultiplication (Δ)
```python
term = bt.CellType.from_source(ontology_id="CL:0000084")
children = term.children.all()  # Δ(term)
```

### Counit (ε)
```python
name = term.name  # ε(term)
```

### Coassociativity Check
```python
# Direct grandchildren
grandchildren_direct = term.grandchildren.all()

# Via children
grandchildren_via_children = [
    grandchild
    for child in term.children.all()
    for grandchild in child.children.all()
]

# Should be equivalent (up to order)
assert set(grandchildren_direct) == set(grandchildren_via_children)
```

### Parents (Inverse Δ)
```python
parents = term.parents  # Navigate up hierarchy
```

### Visualization
```python
term.view_parents()  # Visualize coalgebra structure
```

---

## Category Theory Mapping

| Lamin API | Category Theory | Coalgebra Symbol |
|-----------|----------------|------------------|
| `.children.all()` | Comultiplication | Δ: C → C ⊗ C |
| `.name` | Counit | ε: C → k |
| `.parents` | Coalgebra morphism | f: C → D |
| `.ontology_id` | Object label | - |
| Hierarchy | Coassociativity | (Δ ⊗ id)∘Δ = (id ⊗ Δ)∘Δ |
| Identity recovery | Counit laws | (ε ⊗ id)∘Δ = id |

---

## Bicomodule Examples

Entities appearing in **two ontological contexts**:

1. **DN3 thymocyte** (CL:0000807)
   - Left: Cell lineage (thymocyte → stages)
   - Right: Tissue location (thymus)

2. **CD8+ cytotoxic T cell** (CL:0000794)
   - Left: Cell type hierarchy
   - Right: Immune function

3. **Lung epithelial cell**
   - Left: Cell type
   - Right: Tissue (lung)

4. **Acetyl-CoA pathway** (GO:0019681)
   - Left: Metabolic process
   - Right: Cellular location

---

## References

- Lamin.ai documentation: https://docs.lamin.ai/
- Bionty module: https://docs.lamin.ai/bionty
- Cell Ontology: https://obophenotype.github.io/cell-ontology/
- Gene Ontology: http://geneontology.org/
- MONDO Disease Ontology: https://mondo.monarchinitiative.org/
- UBERON Tissue Ontology: http://uberon.github.io/
