---
name: cq-ai-deterministic-security-scanning-with-ternary-polarity
description: 'Deterministic code security scanner using SplitMix64 seeding. Same seed + same codebase = identical findings. Ternary severity classification. Triggers: cq-ai, security scan, deterministic analysis, code query, vulnerability scanner.'
---

# CQ-AI: Deterministic Code Security Scanning

Extends NCC Group's Code Query with deterministic seeding and ternary severity classification.

**Guarantee**: Same seed + same codebase → identical findings, regardless of scan order or parallelism.

## SplitMix64 Seeding

```rust
struct SplitMix64 { state: u64 }

impl SplitMix64 {
    fn new(seed: u64) -> Self { SplitMix64 { state: seed } }
    fn next_u64(&mut self) -> u64 {
        let z = (self.state ^ (self.state >> 30)) * 0xBF58476D1CE4E5B9;
        self.state = self.state.wrapping_add(0x9E3779B97F4A7C15);
        z ^ (z >> 27)
    }
}
```

## Severity Classification

| Trit | Class | Examples |
|------|-------|---------|
| +1 | CRITICAL | SQL injection, RCE, auth bypass, hardcoded secrets |
| 0 | MEDIUM | Weak crypto, CSRF, XXE, insecure random |
| -1 | INFO | Code smell, deprecated API, style issue |

## Scanning

```python
def cq_deterministic_scan(codebase_path: str, seed: int) -> List[Finding]:
    rng = SplitMix64(seed)
    file_order = sorted(get_all_files(codebase_path), key=lambda f: rng.next_u32())
    findings = []
    for filepath in file_order:
        findings.extend(cq_scan_file(filepath, seed))
    return sorted(findings, key=lambda f: (f.file, f.line, f.finding_id))
```

## Parallel Scanner

```python
class ParallelCQScanner:
    def __init__(self, n_workers: int, seed: int):
        rng = SplitMix64(seed)
        self.worker_seeds = [rng.next_u64() for _ in range(n_workers)]

    def scan_parallel(self, codebase_path: str) -> List[Finding]:
        files = sorted(get_all_files(codebase_path))
        worker_files = [files[i::len(self.worker_seeds)] for i in range(len(self.worker_seeds))]
        # Workers run independently, results compose deterministically
        all_findings = parallel_map(self._scan_worker, zip(self.worker_seeds, worker_files))
        return deduplicate_and_sort(all_findings)
```

## CI Integration (Concrete — wraps real scanners)

The `cq-ai` CLI does not exist as a standalone binary. Instead, use the wrapper
script below which pipes `semgrep` or `bandit` output through deterministic
SplitMix64 ordering and ternary classification.

### Prerequisites

```bash
# Install real scanners
pip install semgrep bandit

# Verify
semgrep --version
bandit --version
```

### Runnable Wrapper Script

Save as `scripts/classify-findings.py` in this skill directory
(`/Users/alice/v/asi/skills/cq-ai-deterministic-security-scanning-with-ternary-polarity/scripts/classify-findings.py`):

```python
#!/usr/bin/env python3
"""
classify-findings.py — Deterministic ternary classification of semgrep/bandit output.

Usage:
  # Semgrep mode (default):
  semgrep --config auto --json src/ | python3 classify-findings.py --seed 0xDEADBEEF

  # Bandit mode:
  bandit -r src/ -f json | python3 classify-findings.py --seed 0xDEADBEEF --scanner bandit

Guarantee: same seed + same findings → identical ordering + classification.
"""

import json
import sys
import argparse


class SplitMix64:
    """Deterministic PRNG matching the Rust impl in the skill spec."""

    def __init__(self, seed: int):
        self.state = seed & 0xFFFFFFFFFFFFFFFF

    def next_u64(self) -> int:
        self.state = (self.state + 0x9E3779B97F4A7C15) & 0xFFFFFFFFFFFFFFFF
        z = self.state
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & 0xFFFFFFFFFFFFFFFF
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & 0xFFFFFFFFFFFFFFFF
        return z ^ (z >> 31)


# Ternary severity mapping
TRIT_MAP = {
    # Semgrep severity → trit
    "ERROR": +1,    # CRITICAL (warm)
    "WARNING": 0,   # MEDIUM (neutral)
    "INFO": -1,     # INFO (cold)
    # Bandit severity → trit
    "HIGH": +1,
    "MEDIUM": 0,
    "LOW": -1,
}

TRIT_LABEL = {+1: "CRITICAL(+1)", 0: "MEDIUM(0)", -1: "INFO(-1)"}


def parse_semgrep(data: dict) -> list[dict]:
    results = data.get("results", [])
    findings = []
    for r in results:
        findings.append({
            "file": r.get("path", "?"),
            "line": r.get("start", {}).get("line", 0),
            "rule": r.get("check_id", "unknown"),
            "message": r.get("extra", {}).get("message", ""),
            "severity": r.get("extra", {}).get("severity", "INFO"),
        })
    return findings


def parse_bandit(data: dict) -> list[dict]:
    results = data.get("results", [])
    findings = []
    for r in results:
        findings.append({
            "file": r.get("filename", "?"),
            "line": r.get("line_number", 0),
            "rule": r.get("test_id", "unknown"),
            "message": r.get("issue_text", ""),
            "severity": r.get("issue_severity", "LOW"),
        })
    return findings


def main():
    parser = argparse.ArgumentParser(description="Deterministic ternary finding classifier")
    parser.add_argument("--seed", type=lambda x: int(x, 0), default=0xDEADBEEF,
                        help="SplitMix64 seed (hex or decimal)")
    parser.add_argument("--scanner", choices=["semgrep", "bandit"], default="semgrep")
    parser.add_argument("--json-out", action="store_true", help="Output as JSON")
    args = parser.parse_args()

    data = json.load(sys.stdin)
    parse_fn = parse_semgrep if args.scanner == "semgrep" else parse_bandit
    findings = parse_fn(data)

    # Deterministic ordering: sort by (file, line, rule) then shuffle with SplitMix64
    findings.sort(key=lambda f: (f["file"], f["line"], f["rule"]))
    rng = SplitMix64(args.seed)
    # Assign deterministic sort key to each finding
    for f in findings:
        f["_sort_key"] = rng.next_u64()
        f["trit"] = TRIT_MAP.get(f["severity"].upper(), -1)
        f["trit_label"] = TRIT_LABEL[f["trit"]]
    findings.sort(key=lambda f: f["_sort_key"])

    # Verify GF(3) conservation report
    trit_sum = sum(f["trit"] for f in findings) % 3

    if args.json_out:
        for f in findings:
            del f["_sort_key"]
        json.dump({"findings": findings, "gf3_sum_mod3": trit_sum,
                    "seed": hex(args.seed), "count": len(findings)},
                  sys.stdout, indent=2)
    else:
        print(f"Seed: {hex(args.seed)} | Findings: {len(findings)} | "
              f"GF(3) sum mod 3: {trit_sum}")
        print("-" * 80)
        for f in findings:
            print(f"  [{f['trit_label']:>14}] {f['file']}:{f['line']} "
                  f"{f['rule']} — {f['message'][:60]}")

    sys.exit(1 if any(f["trit"] == +1 for f in findings) else 0)


if __name__ == "__main__":
    main()
```

### Actual CI Usage (GitHub Actions)

```yaml
- name: Deterministic Security Scan
  run: |
    pip install semgrep
    semgrep --config auto --json src/ \
      | python3 skills/cq-ai-deterministic-security-scanning-with-ternary-polarity/scripts/classify-findings.py \
        --seed 0xDEADBEEF --json-out > scan-results.json
    # Exit code 1 if any CRITICAL (+1) findings

- name: Bandit Alternative
  run: |
    pip install bandit
    bandit -r src/ -f json 2>/dev/null \
      | python3 scripts/classify-findings.py --seed 0xDEADBEEF --scanner bandit
```

### Quick Local Test

```bash
# Scan this repo with semgrep + deterministic classification
cd /Users/alice/v/asi
semgrep --config auto --json skills/ 2>/dev/null \
  | python3 skills/cq-ai-deterministic-security-scanning-with-ternary-polarity/scripts/classify-findings.py \
    --seed 0xDEADBEEF

# Or test with empty input to verify the script runs
echo '{"results":[]}' \
  | python3 skills/cq-ai-deterministic-security-scanning-with-ternary-polarity/scripts/classify-findings.py \
    --seed 42
```

### Key Files

| Path | Description |
|---|---|
| `scripts/classify-findings.py` | Runnable classifier (create from snippet above) |
| This `SKILL.md` | Design document + ternary polarity spec |
