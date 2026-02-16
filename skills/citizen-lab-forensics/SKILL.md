# Citizen Lab Forensics Skill

**Trit**: -1 (MINUS - Validator)
**Category**: investigative-journalism
**Source**: Citizen Lab (University of Toronto), Amnesty Tech

## Overview

Digital forensics techniques for detecting device compromise, analyzing malware indicators, and investigating targeted surveillance. Based on methodologies from Citizen Lab's Pegasus Project and Predator investigations.

## Core Tools

### MVT (Mobile Verification Toolkit)

```bash
# Install
pip install mvt

# iOS backup analysis
mvt-ios check-backup --output /tmp/mvt-results ~/iPhone-backup/

# Android APK analysis
mvt-android check-apks --output /tmp/mvt-results /path/to/apks/

# Check against known IOCs
mvt-ios check-backup --iocs /path/to/pegasus.stix2 ~/backup/
```

**IOC Sources**:
- https://github.com/AmnestyTech/investigations
- https://github.com/citizenlab/malware-indicators

### ExifTool (Metadata Extraction)

```bash
# Extract all metadata
exiftool -a -u -g1 document.pdf

# Extract GPS coordinates
exiftool -gps:all image.jpg

# Remove metadata (for sanitization)
exiftool -all= document.pdf

# Recursive directory scan
exiftool -r -csv -ext pdf /path/to/documents/ > metadata.csv
```

### YARA Rules

```yara
rule Pegasus_String_Indicators {
    meta:
        author = "Citizen Lab"
        description = "Detects Pegasus spyware string patterns"
    strings:
        $s1 = "bh4.4" ascii
        $s2 = "/System/Library/Frameworks/JavaScriptCore.framework" ascii
        $s3 = "webkit.org" ascii
    condition:
        2 of them
}
```

```bash
# Scan with YARA
yara -r pegasus_rules.yar /path/to/scan/

# Compile rules
yarac rules/*.yar compiled_rules

# Scan with compiled rules
yara compiled_rules /path/to/scan/
```

### hachoir-metadata

```python
from hachoir.parser import createParser
from hachoir.metadata import extractMetadata

parser = createParser("/path/to/file")
metadata = extractMetadata(parser)

for line in metadata.exportPlaintext():
    print(line)
```

## Network Forensics

### DNS Cache Probing

```bash
# Check if domain was recently resolved
dig +short @target-dns-server suspicious-domain.com

# DNS history via passive DNS
curl "https://api.passivetotal.org/v2/dns/passive?query=domain.com"
```

### Certificate Pivoting

```bash
# Find related domains via certificate
curl "https://crt.sh/?q=%25.suspicious-domain.com&output=json" | jq

# Censys certificate search
censys search "parsed.names: suspicious-domain.com"
```

### Infrastructure Mapping

```python
# Using Censys Python library
from censys.search import CensysHosts

h = CensysHosts()
for host in h.search("services.http.response.body: 'unique-string'"):
    print(host["ip"], host["services"])
```

## IOC Formats

### STIX 2.1

```json
{
  "type": "indicator",
  "spec_version": "2.1",
  "id": "indicator--8e2e2d2b-17d4-4cbf-938f-98ee46b3cd3f",
  "created": "2025-01-15T00:00:00.000Z",
  "modified": "2025-01-15T00:00:00.000Z",
  "name": "Pegasus Process Name",
  "pattern": "[process:name = 'bh']",
  "pattern_type": "stix",
  "valid_from": "2025-01-15T00:00:00.000Z"
}
```

### MISP Format

```json
{
  "Event": {
    "info": "Pegasus Spyware Indicators",
    "Attribute": [
      {
        "type": "domain",
        "value": "malicious-c2.com",
        "category": "Network activity",
        "to_ids": true
      }
    ]
  }
}
```

## Integration with EpsteinGeoACSet

```julia
# Add forensic metadata to documents
add_part!(acset, :Document,
    doc_bates="EFTA00001234",
    doc_exif_extracted=true,
    doc_device_fingerprint="iPhone12,1",
    doc_gps_lat=18.3021,
    doc_gps_lon=-64.8181,
    doc_creation_software="Adobe Acrobat",
    doc_trit=Int8(-1)  # Validator role
)
```

## DuckDB Schema

```sql
CREATE TABLE forensic_indicators (
    id INTEGER PRIMARY KEY,
    indicator_type VARCHAR,  -- 'domain', 'hash', 'ip', 'process', 'file'
    indicator_value VARCHAR NOT NULL,
    source VARCHAR,          -- 'citizen_lab', 'amnesty_tech', 'custom'
    confidence FLOAT,
    first_seen TIMESTAMP,
    last_seen TIMESTAMP,
    stix_id VARCHAR,
    trit INTEGER DEFAULT -1
);

CREATE TABLE device_analysis (
    id INTEGER PRIMARY KEY,
    device_id VARCHAR,
    device_type VARCHAR,     -- 'ios', 'android'
    analysis_date TIMESTAMP,
    mvt_version VARCHAR,
    indicators_matched INTEGER,
    compromise_detected BOOLEAN,
    report_path VARCHAR
);
```

## GF(3) Triad

```
citizen-lab-forensics (-1) ⊗ icij-document-analysis (0) ⊗ graph-investigation (+1) = 0 ✓
```

## CLI Recipes

```bash
# Full iOS analysis pipeline
mvt-ios check-backup \
  --iocs https://raw.githubusercontent.com/AmnestyTech/investigations/master/2021-07-18_nso/pegasus.stix2 \
  --output ./mvt-report \
  ~/iPhone-backup/

# Bulk metadata extraction to DuckDB
exiftool -r -csv -ext pdf -ext jpg -ext docx /evidence/ > metadata.csv
duckdb evidence.duckdb "CREATE TABLE metadata AS SELECT * FROM read_csv_auto('metadata.csv')"

# YARA scan with JSON output
yara -r -w rules/*.yar /evidence/ 2>/dev/null | \
  jq -Rs 'split("\n") | map(select(length > 0)) | map(split(" ") | {rule: .[0], file: .[1]})'
```

## References

- Citizen Lab: https://citizenlab.ca/
- Amnesty Tech: https://www.amnesty.org/en/tech/
- MVT Documentation: https://docs.mvt.re/
- YARA Documentation: https://yara.readthedocs.io/

## See Also

- `boxxy-reverse-engineering` - Firmware extraction
- `radare2-hatchery` - Binary analysis
- `variant-analysis` - Pattern-based vulnerability hunting
- `icij-document-analysis` - Document processing (trit 0)
- `graph-investigation` - Entity graphing (trit +1)
