---
name: otel-tracing
description: OpenTelemetry tracing for agent observations and SPI verification
version: 1.0.0
---

# OpenTelemetry Tracing Skill

**Trit**: -1 (VALIDATOR)
**Bundle**: infrastructure
**Role**: Verification of execution traces and distributed contexts.

## Overview

This skill provides a standard interface for emitting OpenTelemetry spans from agent actions. It is crucial for:
1.  **SPI Verification**: Tracing execution paths to ensure determinism.
2.  **Debugging**: Visualizing distributed agent interactions.
3.  **Performance**: Measuring latency in ACSet bridge operations.

## Integration

### Python

```python
from opentelemetry import trace
from opentelemetry.sdk.trace import TracerProvider
from opentelemetry.sdk.trace.export import ConsoleSpanExporter, SimpleSpanProcessor

def init_tracer(service_name="agent-skill"):
    provider = TracerProvider()
    processor = SimpleSpanProcessor(ConsoleSpanExporter())
    provider.add_span_processor(processor)
    trace.set_tracer_provider(provider)
    return trace.get_tracer(service_name)

tracer = init_tracer()

with tracer.start_as_current_span("agent_action") as span:
    span.set_attribute("agent.trit", -1)
    span.set_attribute("agent.id", "minus_validator")
    # ... perform action ...
```

## SPI Verification Pattern

To verify Strong Parallelism Invariance (SPI), traces must be deterministic given a seed.

```python
def verify_spi_trace(seed, trace_id):
    expected_hash = compute_spi_hash(seed)
    actual_hash = hash(trace_id)
    assert expected_hash == actual_hash
```

## Neo4j Mapping

*   **Nodes**: `Span`, `Trace`
*   **Relationships**: `PARENT_OF`, `NEXT_SIBLING`
*   **Properties**: `start_time`, `end_time`, `attributes` (JSON)

## Commands

*   `trace-agent <agent_id>`: Start a trace for an agent.
*   `export-traces`: Dump traces to JSON.
