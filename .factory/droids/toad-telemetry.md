---
name: toad-telemetry
description: Converted from plurigrid/asi skill: toad-telemetry
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Toad Telemetry Skill

OpenTelemetry instrumentation for Batrachian Toad AI agent terminal.

## Overview

Provides deep observability into Toad agent sessions:
- **Per-tool spans**: Every tool call (Bash, Read, Write, etc.) gets its own span
- **Turn tracking**: Prompt → response cycles with timing
- **Session lifecycle**: Start/stop with agent metadata
- **Error tracking**: Exceptions and error states captured

## Installation

```bash
# Install Toad
uv tool install batrachian-toad --python 3.14

# Install OTEL SDK in Toad's environment
uv pip install opentelemetry-sdk opentelemetry-exporter-otlp \
  --python ~/.local/share/uv/tools/batrachian-toad/bin/python3

# Install toad_telemetry library
mkdir -p ~/.local/lib/toad_telemetry
cp instrumentation.py ~/.local/lib/toad_telemetry/
cp __init__.py ~/.local/lib/toad_telemetry/

# Install wrapper script
cp toadia ~/.local/bin/
chmod +x ~/.local/bin/toadia
```

## Usage

### Via Wrapper Script (Recommended)

```bash
# Run toad with telemetry enabled
toadia -a claude .

# Run ACP agent with telemetry
toadia acp "my-command" .

# Disable telemetry
TOAD_TELEMETRY_ENABLED=0 toadia -a claude .
```

### Programmatic

```python
from toad_telemetry import instrument_toad, ToadTelemetryConfig

config = ToadTelemetryConfig(
    service_name="my-toad-session",
    endpoint="http://localhost:4317",
    agent_name="claude",
    project_dir="/path/to/project",
)

instrument_toad(config)

# Now run toad normally
from toad.cli import main
main()
```

## Environment Variables

| Variable | Default | Description |
|----------|---------|-------------|
| `OTEL_EXPORTER_OTLP_ENDPOINT` | `http://localhost:4317` | OTLP collector endpoint |
| `TOAD_TELEMETRY_ENABLED` | `1` | Enable/disable telemetry |
| `TOAD_TELEMETRY_CONSOLE` | `0` | Print spans to console |
| `TOAD_SERVICE_NAME` | `toad` | Service name in traces |

## Quick Start with Jaeger

```bash
# Start Jaeger
docker run -d --name jaeger \
  -p 16686:16686 \
  -p 4317:4317 \
  jaegertr