---
name: jepsen-testing
description: Jepsen-style correctness testing for distributed systems under faults (partitions, crashes, clock skew) using concurrent operation histories and formal checkers (linearizability/serializability and Elle-style anomalies). Use when designing, implementing, or running Jepsen tests, or interpreting histories/violations.
---

# Jepsen Testing

## Intake

- Identify the system under test and the exact client surface (Redis, S3, Kafka, HTTP, gRPC).
- Define what "acknowledged" means for each operation (what does the client treat as committed).
- Write the claimed consistency guarantees as a checkable property (linearizable register, RYW, monotonic reads, serializable txns).
- Specify the failure model to test (crash-stop, partitions, clock skew, disk stalls, restarts).
- Decide whether the test must be multi-surface (write via Redis, read via S3) to validate cross-frontend coherence.

## Workload Design

- Prefer the smallest workload that can falsify the claim.
- Use a mix of reads and writes that creates ambiguous interleavings.
- Add a "witness" invariant that is easy to explain:
- Lost acknowledged write.
- Read sees a value that cannot be explained by any sequential execution respecting real-time order.
- List-append: element lost/duplicated or observed order implies a cycle.

## Checker Selection

- Register or map semantics: use a linearizability checker.
- Transactional / multi-object semantics: use Elle-style anomaly detection (write cycles, dirty reads, lost updates).
- If linearizability is too strong for the product, explicitly select a weaker model and encode it (do not silently downgrade).

## Fault (Nemesis) Selection

- Partitions: majority/minority splits, bridge partitions, flapping partitions.
- Process faults: kill and restart, node reboot, rolling restarts.
- Time faults: clock offsets and jumps if the system relies on time.
- Storage faults: fsync latency, I/O stalls, disk-full behavior (only if safe and reversible).

## Run and Minimize

- Start with a short, low-concurrency run until the harness is stable.
- When a failure appears, minimize by reducing:
- Keys, operation count, and concurrency.
- Fault intensity and schedule complexity.
- Preserve determinism (fixed seeds, fixed partition schedule) so a failing history can be reproduced.

## Reporting

- State the exact claim under test and the precise pass/fail property.
- Include the workload, nemesis schedule, and a minimal failing history excerpt.
- Distinguish availability failures (timeouts) from safety failures (incorrect ok results).


