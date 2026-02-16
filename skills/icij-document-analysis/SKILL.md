# ICIJ Document Analysis Skill

**Trit**: 0 (ERGODIC - Coordinator)
**Category**: investigative-journalism
**Source**: ICIJ (International Consortium of Investigative Journalists)

## Overview

Document processing pipeline for large-scale leak analysis. Based on ICIJ's methodologies from Panama Papers, Paradise Papers, and Pandora Papers investigations. Coordinates between forensic validation (-1) and graph generation (+1).

## Core Tools

### ICIJ Datashare

Self-hosted document search with NER pipelines.

```bash
# Docker installation
docker pull icij/datashare

# Run with local documents
docker run -p 8080:8080 \
  -v /path/to/documents:/home/datashare/data \
  icij/datashare

# Access at http://localhost:8080
```

**Features**:
- Full-text search (Elasticsearch backend)
- Named Entity Recognition (NER)
- Batch OCR processing
- Multi-language support
- Tagging and annotation

### Apache Tika

Universal document format extraction.

```bash
# Start Tika server
docker run -p 9998:9998 apache/tika

# Extract text
curl -T document.pdf http://localhost:9998/tika --header "Accept: text/plain"

# Extract metadata
curl -T document.pdf http://localhost:9998/meta --header "Accept: application/json"

# Detect language
curl -T document.pdf http://localhost:9998/language/stream
```

```python
from tika import parser

# Parse document
parsed = parser.from_file('/path/to/document.pdf')
text = parsed['content']
metadata = parsed['metadata']

# Batch processing
import os
from pathlib import Path

def process_directory(doc_dir):
    results = []
    for path in Path(doc_dir).rglob('*'):
        if path.is_file():
            try:
                parsed = parser.from_file(str(path))
                results.append({
                    'path': str(path),
                    'content': parsed.get('content', ''),
                    'metadata': parsed.get('metadata', {})
                })
            except Exception as e:
                results.append({'path': str(path), 'error': str(e)})
    return results
```

### Tesseract OCR

```bash
# Basic OCR
tesseract scanned_document.png output -l eng

# PDF with searchable text layer
tesseract scanned.pdf output pdf -l eng+fra

# Batch processing
find /documents -name "*.png" -exec tesseract {} {}.txt -l eng \;
```

```python
import pytesseract
from PIL import Image
from pdf2image import convert_from_path

# Image OCR
text = pytesseract.image_to_string(Image.open('document.png'))

# PDF OCR pipeline
def ocr_pdf(pdf_path):
    pages = convert_from_path(pdf_path, dpi=300)
    full_text = []
    for i, page in enumerate(pages):
        text = pytesseract.image_to_string(page)
        full_text.append(f"--- Page {i+1} ---\n{text}")
    return "\n".join(full_text)
```

### spaCy NER Pipeline

```python
import spacy

# Load model with NER
nlp = spacy.load("en_core_web_lg")

def extract_entities(text):
    doc = nlp(text)
    entities = {
        'persons': [],
        'organizations': [],
        'locations': [],
        'dates': [],
        'money': []
    }

    for ent in doc.ents:
        if ent.label_ == 'PERSON':
            entities['persons'].append(ent.text)
        elif ent.label_ == 'ORG':
            entities['organizations'].append(ent.text)
        elif ent.label_ in ('GPE', 'LOC'):
            entities['locations'].append(ent.text)
        elif ent.label_ == 'DATE':
            entities['dates'].append(ent.text)
        elif ent.label_ == 'MONEY':
            entities['money'].append(ent.text)

    return entities

# Deduplicate and normalize
def normalize_entities(entities):
    from collections import Counter
    return {
        k: Counter(v).most_common()
        for k, v in entities.items()
    }
```

## Document Processing Pipeline

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│   Ingest    │ ──▶ │   Extract   │ ──▶ │     NER     │ ──▶ │   Index     │
│  (Datashare)│     │   (Tika)    │     │   (spaCy)   │     │(Elasticsearch)│
└─────────────┘     └─────────────┘     └─────────────┘     └─────────────┘
       │                   │                   │                   │
       ▼                   ▼                   ▼                   ▼
┌─────────────┐     ┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│ File types  │     │  OCR if     │     │  Persons    │     │  Full-text  │
│ PDF, DOCX,  │     │  scanned    │     │  Orgs       │     │  search     │
│ XLSX, EML   │     │  (Tesseract)│     │  Locations  │     │  + facets   │
└─────────────┘     └─────────────┘     └─────────────┘     └─────────────┘
```

## DuckDB Schema

```sql
-- Document metadata
CREATE TABLE documents (
    id INTEGER PRIMARY KEY,
    bates_number VARCHAR UNIQUE,
    file_path VARCHAR,
    file_type VARCHAR,
    file_size BIGINT,
    page_count INTEGER,
    language VARCHAR,
    ocr_applied BOOLEAN DEFAULT FALSE,
    extracted_text TEXT,
    tika_metadata JSON,
    created_at TIMESTAMP,
    processed_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
    trit INTEGER DEFAULT 0
);

-- Extracted entities
CREATE TABLE entities (
    id INTEGER PRIMARY KEY,
    document_id INTEGER REFERENCES documents(id),
    entity_type VARCHAR,  -- 'PERSON', 'ORG', 'GPE', 'DATE', 'MONEY'
    entity_value VARCHAR,
    normalized_value VARCHAR,
    confidence FLOAT,
    char_start INTEGER,
    char_end INTEGER
);

-- Entity co-occurrence (for graph export)
CREATE TABLE entity_cooccurrence (
    id INTEGER PRIMARY KEY,
    entity_a_id INTEGER REFERENCES entities(id),
    entity_b_id INTEGER REFERENCES entities(id),
    document_id INTEGER REFERENCES documents(id),
    cooccurrence_type VARCHAR,  -- 'same_document', 'same_paragraph', 'same_sentence'
    count INTEGER DEFAULT 1
);

-- Processing status
CREATE TABLE processing_log (
    id INTEGER PRIMARY KEY,
    document_id INTEGER REFERENCES documents(id),
    stage VARCHAR,  -- 'ingest', 'extract', 'ocr', 'ner', 'index'
    status VARCHAR,  -- 'pending', 'processing', 'completed', 'failed'
    error_message TEXT,
    started_at TIMESTAMP,
    completed_at TIMESTAMP
);
```

## Integration with EpsteinGeoACSet

```julia
# Process EFTA document and extract to ACSet
function process_efta_document!(acset, bates_number::String, file_path::String)
    # Add document
    doc_id = add_part!(acset, :Document,
        doc_bates=bates_number,
        doc_type=get_file_type(file_path),
        doc_trit=Int8(0)
    )

    # Extract text (via Tika)
    text = extract_text_tika(file_path)

    # Run NER
    entities = extract_entities_spacy(text)

    # Link persons to existing contacts
    for person in entities["persons"]
        person_id = find_or_create_person!(acset, person)
        add_part!(acset, :DocumentMention,
            mention_doc=doc_id,
            mention_person=person_id,
            mention_context=get_context(text, person)
        )
    end

    # Link locations to properties
    for location in entities["locations"]
        if prop_id = match_property(acset, location)
            add_part!(acset, :DocumentLocation,
                docloc_doc=doc_id,
                docloc_property=prop_id
            )
        end
    end

    return doc_id
end
```

## Batch Processing Script

```python
#!/usr/bin/env python3
"""EFTA Corpus Batch Processor"""

import duckdb
from pathlib import Path
from tika import parser
import spacy
from concurrent.futures import ProcessPoolExecutor
import json

DB_PATH = "efta_documents.duckdb"
CORPUS_PATH = "/Users/bob/i/epstein-library/downloads/data-sets/"

nlp = spacy.load("en_core_web_lg")

def process_document(file_path):
    """Process single document through Tika + spaCy pipeline."""
    try:
        # Extract with Tika
        parsed = parser.from_file(str(file_path))
        text = parsed.get('content', '') or ''
        metadata = parsed.get('metadata', {})

        # NER with spaCy
        doc = nlp(text[:1000000])  # Limit to 1M chars
        entities = [(ent.text, ent.label_, ent.start_char, ent.end_char)
                    for ent in doc.ents]

        return {
            'path': str(file_path),
            'text': text,
            'metadata': metadata,
            'entities': entities,
            'status': 'success'
        }
    except Exception as e:
        return {
            'path': str(file_path),
            'error': str(e),
            'status': 'failed'
        }

def main():
    con = duckdb.connect(DB_PATH)

    # Get all PDF files
    files = list(Path(CORPUS_PATH).rglob("*.pdf"))
    print(f"Found {len(files)} PDF files")

    # Process in parallel
    with ProcessPoolExecutor(max_workers=4) as executor:
        results = list(executor.map(process_document, files))

    # Insert into DuckDB
    for result in results:
        if result['status'] == 'success':
            con.execute("""
                INSERT INTO documents (file_path, extracted_text, tika_metadata, processed_at)
                VALUES (?, ?, ?, CURRENT_TIMESTAMP)
            """, [result['path'], result['text'], json.dumps(result['metadata'])])

            doc_id = con.execute("SELECT last_insert_rowid()").fetchone()[0]

            for text, label, start, end in result['entities']:
                con.execute("""
                    INSERT INTO entities (document_id, entity_type, entity_value, char_start, char_end)
                    VALUES (?, ?, ?, ?, ?)
                """, [doc_id, label, text, start, end])

    con.close()
    print(f"Processed {len(results)} documents")

if __name__ == "__main__":
    main()
```

## GF(3) Triad

```
citizen-lab-forensics (-1) ⊗ icij-document-analysis (0) ⊗ graph-investigation (+1) = 0 ✓
```

## CLI Recipes

```bash
# Start full pipeline stack
docker-compose up -d  # Datashare + Tika + Elasticsearch

# Bulk import to Datashare
curl -X POST "http://localhost:8080/api/task/batchDownload" \
  -H "Content-Type: application/json" \
  -d '{"path": "/home/datashare/data"}'

# Export entities to CSV for Neo4j import
duckdb efta_documents.duckdb -c "
COPY (
  SELECT DISTINCT entity_value as name, entity_type as type
  FROM entities
  WHERE entity_type IN ('PERSON', 'ORG')
) TO 'entities.csv' WITH (HEADER TRUE)
"

# Export co-occurrences for graph edges
duckdb efta_documents.duckdb -c "
COPY (
  SELECT e1.entity_value as source, e2.entity_value as target,
         COUNT(*) as weight, 'MENTIONED_WITH' as type
  FROM entities e1
  JOIN entities e2 ON e1.document_id = e2.document_id AND e1.id < e2.id
  WHERE e1.entity_type = 'PERSON' AND e2.entity_type = 'PERSON'
  GROUP BY e1.entity_value, e2.entity_value
  HAVING COUNT(*) > 1
) TO 'cooccurrences.csv' WITH (HEADER TRUE)
"
```

## References

- ICIJ Datashare: https://datashare.icij.org/
- Apache Tika: https://tika.apache.org/
- Tesseract OCR: https://tesseract-ocr.github.io/
- spaCy NER: https://spacy.io/usage/linguistic-features#named-entities

## See Also

- `citizen-lab-forensics` - Device forensics (trit -1)
- `graph-investigation` - Entity graphing (trit +1)
- `pdf` - PDF extraction utilities
- `duckdb-ies` - Interactome analytics
