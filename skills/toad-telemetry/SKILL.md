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
  jaegertracing/all-in-one:latest

# Run toadia
toadia -a claude .

# View traces at http://localhost:16686
```

## Span Attributes

### Tool Spans (`tool.<name>`)

- `toad.tool.id` - Unique tool call ID
- `toad.tool.name` - Tool name (Bash, Read, Write, etc.)
- `toad.tool.kind` - Tool category
- `toad.tool.status` - Completion status
- `toad.tool.duration_ms` - Execution time
- `toad.tool.error` - Error message (if any)
- `toad.session.id` - Session identifier
- `toad.agent` - Agent name

### Turn Spans (`agent.turn`)

- `toad.prompt.length` - Input prompt character count
- `toad.turn.stop_reason` - Why the turn ended
- `toad.turn.duration_ms` - Total turn time
- `toad.agent` - Agent name

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                      Toad TUI                               │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐  │
│  │   Prompt    │  │ Conversation│  │     Agent ACP       │  │
│  └─────────────┘  └─────────────┘  └──────────┬──────────┘  │
│                                               │             │
│  ┌────────────────────────────────────────────┴───────────┐ │
│  │              toad_telemetry (monkey-patch)             │ │
│  │  ┌───────────────────┐  ┌──────────────────────────┐   │ │
│  │  │ rpc_session_update│  │       send_prompt        │   │ │
│  │  │   (tool spans)    │  │      (turn spans)        │   │ │
│  │  └─────────┬─────────┘  └────────────┬─────────────┘   │ │
│  └────────────┼─────────────────────────┼─────────────────┘ │
└───────────────┼─────────────────────────┼───────────────────┘
                │                         │
                ▼                         ▼
         ┌──────────────────────────────────┐
         │        OTEL Collector            │
         │  (Jaeger / Tempo / Honeycomb)    │
         └──────────────────────────────────┘
```

## How It Works

The instrumentation uses deferred monkey-patching via Python import hooks to avoid circular imports:

1. `instrument_toad()` installs an import hook that waits for `toad.app` to load
2. Once Toad is fully initialized, it patches `Agent.rpc_session_update` and `Agent.send_prompt`
3. `rpc_session_update` receives all ACP protocol events (tool_call, tool_call_update, etc.)
4. Each tool call gets a span that tracks its lifecycle from start to completion
5. `send_prompt` wraps each agent turn with timing and stop reason

## Files

- `SKILL.md` - This documentation
- `__init__.py` - Package entry point
- `instrumentation.py` - Core monkey-patching and OTEL integration
- `toadia` - Wrapper script with Jaeger quickstart help

## Backends

### Jaeger (Local Development)

```bash
docker run -d --name jaeger \
  -p 16686:16686 \
  -p 4317:4317 \
  jaegertracing/all-in-one:latest
```

### Grafana Tempo

```bash
# With Grafana stack
docker-compose up -d  # includes tempo, grafana
# View in Grafana Explore with Tempo datasource
```

### Honeycomb (Cloud)

```bash
OTEL_EXPORTER_OTLP_ENDPOINT=https://api.honeycomb.io:443 \
OTEL_EXPORTER_OTLP_HEADERS="x-honeycomb-team=YOUR_API_KEY" \
toadia -a claude .
```

## Troubleshooting

### "OpenTelemetry not available"

Install the SDK in Toad's Python environment:
```bash
uv pip install opentelemetry-sdk opentelemetry-exporter-otlp \
  --python ~/.local/share/uv/tools/batrachian-toad/bin/python3
```

### No spans appearing

1. Check collector is running: `docker ps | grep jaeger`
2. Enable console export: `TOAD_TELEMETRY_CONSOLE=1 toadia ...`
3. Verify telemetry enabled: `TOAD_TELEMETRY_ENABLED=1`

### gRPC connection errors

Try HTTP exporter (port 4318 instead of 4317):
```bash
OTEL_EXPORTER_OTLP_ENDPOINT=http://localhost:4318 toadia -a claude .
```

## Related Skills

- `otel-cli` - Command-line OTEL span emission
- `claude_telemetry` - Similar instrumentation for Claude Code CLI


## ACP atlas

Part of: `acp-commons`.
