# joker - Sims Save File Parser for Boxxy

**joker** is a comprehensive command-line tool for parsing and analyzing The Sims package files across all generations (Sims 2, 3, and 4).

## Features

- **DBPF Parsing**: Full support for Sims 2 (1.0/1.1), Sims 3 (2.0), and Sims 4 (2.0 with Type IDs)
- **Format Detection**: Automatically identifies game version from file format
- **Resource Enumeration**: Lists all resources with metadata (type, group, ID, size, compression)
- **Batch Analysis**: Scan directories to find all Sims save files
- **Multi-Format Support**: Handles .sims, .sims2, .package, .sims3pack, .ts4script

## Installation

```bash
go build -o bin/joker ./cmd/joker
```

## Usage

### Parse and Analyze a Package File

```bash
./bin/joker parse ~/Documents/TheSims3/Saves/UserSaveGame.sims3pack
```

Output:
```
=== Sims Package Analysis ===

File: UserSaveGame.sims3pack
Game Version: Sims 3
DBPF Version: 2.0
Total Resources: 1247
File Size: 52428800 bytes

Index Information:
  Index Count: 1247
  Index Offset: 0x031a2c40
  Created: 1703078520
  Modified: 1703162840

Resource Types Found:
  Type 0x043bec01: 142 resources
  Type 0x0210dc99: 18 resources
  Type 0x0215ca48: 95 resources
...

Compressed Resources: 892
Uncompressed Resources: 355
```

### List All Resources

```bash
./bin/joker list ~/Documents/TheSims3/Saves/UserSaveGame.sims3pack | head -20
```

### Scan for Sims Saves

```bash
./bin/joker info ~/Documents/TheSims3/Saves/
```

## DBPF Format Specification

### Header (96 bytes)

| Offset | Size | Field |
|--------|------|-------|
| 0x00   | 4    | Magic ("DBPF") |
| 0x04   | 4    | Major Version |
| 0x08   | 4    | Minor Version |
| 0x0C   | 16   | Reserved |
| 0x1C   | 4    | File Size |
| 0x20   | 4    | Index Count |
| 0x24   | 4    | Index Offset |
| 0x28   | 4    | Index Size |
| 0x2C   | 4    | Hole Index Count |
| 0x30   | 4    | Hole Index Offset |
| 0x34   | 4    | Hole Index Size |
| 0x38   | 4    | Created Date (Unix timestamp) |
| 0x3C   | 4    | Modified Date (Unix timestamp) |
| 0x40   | 4    | Index Minor |

### Resource Entry (24-32 bytes)

| Field | Size | Version |
|-------|------|---------|
| ResourceType | 4 | All |
| ResourceGroup | 4 | All |
| ResourceID | 8 | All |
| Offset | 4 | All |
| CompressedSize | 4 | All |
| RawSize | 4 | All |
| TypeID | 4 | Sims 4 only |

### Compression Methods

- **Sims 2/3**: QFS (Quick File System) / RefPack compression
- **Sims 4**: ZLIB compression (40-50% better ratio)

## Game Version Detection

| DBPF Version | Index Minor | Game |
|--------------|-------------|------|
| 1.0 - 1.1    | 0           | Sims 2 |
| 2.0          | 0           | Sims 3 |
| 2.0          | 1           | Sims 4 |

## Boxxy Integration

joker is registered as a Boxxy skill with GF(3) trit -1 (Validator role):

```go
skill := sims_parser.NewSimsParserSkill()
manifest := skill.Manifest()
// Integrates with ASI skill registry
```

## Supported File Formats

| Game | Extensions | DBPF Version |
|------|-----------|--------------|
| The Sims 2 | .sims, .sims2 | 1.0 - 1.1 |
| The Sims 3 | .package, .sims3pack | 2.0 |
| The Sims 4 | .package, .ts4script | 2.0 (v7.1) |

## License

MIT License

## Author

Boxxy team
