---
name: bandwidth-benchmark
description: "Measure encoding/decoding throughput across Syrup implementations for bandwidth benchmarking"
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

Syrup Bandwidth Benchmark skill for measuring encoding/decoding throughput across Syrup implementations. Provides bandwidth benchmarks for comparing serialization performance.

Use when:
- Benchmarking Syrup serialization performance
- Comparing throughput across implementations (Zig, Rust, Clojure)
- Measuring encoding/decoding speeds
