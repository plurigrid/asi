---
name: cq-ai-deterministic-security-scanning-with-ternary-polarity
description: Deterministic code security scanner using SplitMix64 seeding. Same seed + same codebase = identical findings. Ternary severity classification. Triggers: cq-ai, security scan, deterministic analysis, code query, vulnerability scanner.
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

## CI Integration

```yaml
- name: Security Scan
  run: cq-ai scan --seed 0xDEADBEEF --workers 4 src/
```
