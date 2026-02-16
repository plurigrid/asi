---
name: sqlite-scanner
description: Scan filesystems for SQLite databases by magic-byte detection. Wraps simonw/sqlite-scanner (Go binary via PyPI/uvx). Use for forensic inventory, honeypot canary detection, VM disk auditing, and database cataloging.
license: MIT
compatibility: Requires uvx (uv tool runner) or `go install github.com/simonw/sqlite-scanner@latest`. Integrates with Boxxy skill system for GF(3) triadic consensus.
metadata:
  version: 0.1.1
  upstream: github.com/simonw/sqlite-scanner
  author: Simon Willison (upstream), Claude via Boxxy (integration)
  gf3-trit: -1
  trit-role: MINUS (Verifier)
  detection-method: "SQLite magic header (first 16 bytes: 'SQLite format 3\\x00')"
  capabilities: "scan-directories, detect-sqlite, json-output, jsonl-output, size-reporting"
allowed-tools: "Bash(uvx:*,go:*,sqlite-scanner:*) Read"
---

# sqlite-scanner - SQLite Database Filesystem Scanner

## Overview

**sqlite-scanner** wraps Simon Willison's Go CLI tool that identifies SQLite databases by reading the first 16 bytes of every file and comparing against the magic header `SQLite format 3\x00`. No file extension guessing — pure binary signature detection.

**Role**: MINUS verifier in triadic consensus — validates filesystem state by detecting hidden/renamed SQLite databases.

## Quick Start

```bash
# One-shot via uvx (no install needed)
uvx sqlite-scanner ~/

# With JSON output and sizes
uvx sqlite-scanner --json --size /path/to/scan

# Streaming JSONL for pipeline consumption
uvx sqlite-scanner --jsonl --size ~/Library ~/Documents
```

## When to Use

- **Forensic inventory**: Find all SQLite databases on a system regardless of extension
- **VM disk auditing**: Scan mounted VM disk images for database artifacts
- **Honeypot validation**: Verify canary SQLite files are planted correctly
- **Pre-migration cataloging**: Inventory databases before system moves
- **Stealer artifact detection**: Find browser/app databases in unexpected locations

## When NOT to Use

- Querying database contents (use DuckDB or sqlite3)
- Modifying databases (use appropriate write tools)
- Scanning network shares (latency makes magic-byte reads slow)

## CLI Reference

| Flag | Default | Description |
|------|---------|-------------|
| `--workers N` | `NumCPU()` | Parallel worker goroutines |
| `--size` | `false` | Include file size in output |
| `--json` | `false` | Pretty-printed JSON array |
| `--jsonl` | `false` | Newline-delimited JSON |
| `--version` | - | Print version |

**Positional args**: One or more directories to scan. Defaults to `.` if none given.

## Output Formats

### Plain text (default)
```
/Users/bob/Library/Safari/History.db
/Users/bob/Library/Messages/chat.db
```

### JSON (`--json --size`)
```json
{"entries": [
  {"path": "/Users/bob/Library/Safari/History.db", "size": 1048576},
  {"path": "/Users/bob/Library/Messages/chat.db", "size": 524288}
]}
```

### JSONL (`--jsonl --size`)
```
{"path":"/Users/bob/Library/Safari/History.db","size":1048576}
{"path":"/Users/bob/Library/Messages/chat.db","size":524288}
```

## Detection Method

```go
var sqliteMagic = []byte("SQLite format 3\x00")

func checkSQLiteMagic(path string) bool {
    f, _ := os.Open(path)
    buf := make([]byte, 16)
    io.ReadFull(f, buf)
    return bytes.Equal(buf, sqliteMagic)
}
```

Worker-pool pattern: `filepath.WalkDir` feeds paths channel, N workers read 16 bytes each, matches stream to output immediately.

## GF(3) Conservation

sqlite-scanner is assigned **trit = -1 (MINUS)** for verification role:

```
Verifier (-1) + Coordinator (0) + Generator (+1) = 0 (mod 3)
[sqlite-scanner]  [jo-clojure]     [hy-regime]
```

Triad semantics:
- **sqlite-scanner** detects/validates SQLite presence (MINUS)
- **jo-clojure** orchestrates scan → query → report pipeline (ERGODIC)
- **hy-regime** generates analysis reports from discovered databases (PLUS)

## Boxxy Activities

### scan-host
Scan host filesystem for all SQLite databases.
```clojure
(sqlite-scanner/scan ["/Users/bob"] {:json true :size true :workers 8})
```

### scan-vm-disk
Mount and scan a VM disk image.
```clojure
(sqlite-scanner/scan-mounted disk-mount-path {:jsonl true})
```

### canary-audit
Verify honeypot canary databases are in place.
```clojure
(sqlite-scanner/verify-canaries canary-paths scan-results)
```

## Architecture

- **upstream**: `github.com/simonw/sqlite-scanner` (single main.go, ~250 LOC)
- **distribution**: PyPI wheels via `go-to-wheel` (8 platform targets)
- **invocation**: `uvx sqlite-scanner` (zero-install) or `go install`
- **concurrency**: Go worker pool, `runtime.NumCPU()` default workers
- **integration**: Joker `.joke` activities wrap via `joker.os/exec`

## References

- [Blog post](https://simonwillison.net/2026/Feb/4/distributing-go-binaries/) — Distribution pattern
- [GitHub](https://github.com/simonw/sqlite-scanner) — Source
- [PyPI](https://pypi.org/project/sqlite-scanner/) — Package
- [go-to-wheel](https://github.com/simonw/go-to-wheel) — Build tool
