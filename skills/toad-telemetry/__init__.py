"""
toad_telemetry - OpenTelemetry instrumentation for Batrachian Toad

Provides per-tool span tracking for AI agent interactions via Toad's ACP protocol.
Hooks into Textual's message system to intercept ToolCall/ToolCallUpdate events.

Usage:
    # Monkey-patch Toad before running
    from toad_telemetry import instrument_toad
    instrument_toad()
    
    # Or use the wrapper script: toadia
"""

from .instrumentation import (
    instrument_toad,
    uninstrument_toad,
    ToadTelemetryConfig,
    get_tracer,
)

__version__ = "0.1.0"
__all__ = [
    "instrument_toad",
    "uninstrument_toad",
    "ToadTelemetryConfig",
    "get_tracer",
]
