"""
Core instrumentation for Toad OpenTelemetry integration.

Monkey-patches Toad's ACP Agent to emit OTEL spans for:
- Session lifecycle (start/stop)
- Tool calls (with timing, status, errors)
- Agent turns (prompt -> response cycle)

Uses deferred patching to avoid circular import issues.
"""

import os
import time
import functools
import atexit
from dataclasses import dataclass, field
from typing import Any, Callable, Optional
from contextlib import contextmanager

# Lazy imports for optional OTEL dependency
_tracer = None
_span_stack: dict[str, Any] = {}  # tool_call_id -> span


@dataclass
class ToadTelemetryConfig:
    """Configuration for Toad telemetry."""
    service_name: str = "toad"
    endpoint: str = field(default_factory=lambda: os.environ.get(
        "OTEL_EXPORTER_OTLP_ENDPOINT", "http://localhost:4317"
    ))
    insecure: bool = True
    console_export: bool = field(default_factory=lambda: os.environ.get(
        "TOAD_TELEMETRY_CONSOLE", "0"
    ) == "1")
    enabled: bool = field(default_factory=lambda: os.environ.get(
        "TOAD_TELEMETRY_ENABLED", "1"
    ) == "1")
    
    # Span attributes
    agent_name: str = ""
    project_dir: str = ""


_config: Optional[ToadTelemetryConfig] = None
_original_rpc_session_update: Optional[Callable] = None
_original_send_prompt: Optional[Callable] = None
_instrumented: bool = False
_deferred_patch_installed: bool = False


def get_tracer():
    """Get or create the OTEL tracer."""
    global _tracer
    if _tracer is not None:
        return _tracer
    
    try:
        from opentelemetry import trace
        from opentelemetry.sdk.trace import TracerProvider
        from opentelemetry.sdk.trace.export import BatchSpanProcessor, ConsoleSpanExporter
        from opentelemetry.sdk.resources import Resource, SERVICE_NAME
        
        config = _config or ToadTelemetryConfig()
        
        resource = Resource.create({
            SERVICE_NAME: config.service_name,
            "toad.agent": config.agent_name,
            "toad.project": config.project_dir,
        })
        
        provider = TracerProvider(resource=resource)
        
        # Console exporter for debugging
        if config.console_export:
            provider.add_span_processor(BatchSpanProcessor(ConsoleSpanExporter()))
        
        # OTLP exporter
        try:
            from opentelemetry.exporter.otlp.proto.grpc.trace_exporter import OTLPSpanExporter
            otlp_exporter = OTLPSpanExporter(
                endpoint=config.endpoint,
                insecure=config.insecure,
            )
            provider.add_span_processor(BatchSpanProcessor(otlp_exporter))
        except ImportError:
            # Fall back to HTTP if gRPC not available
            try:
                from opentelemetry.exporter.otlp.proto.http.trace_exporter import OTLPSpanExporter as HTTPExporter
                http_endpoint = config.endpoint.replace(":4317", ":4318")
                if not http_endpoint.endswith("/v1/traces"):
                    http_endpoint = f"{http_endpoint}/v1/traces"
                otlp_exporter = HTTPExporter(endpoint=http_endpoint)
                provider.add_span_processor(BatchSpanProcessor(otlp_exporter))
            except ImportError:
                pass
        
        trace.set_tracer_provider(provider)
        _tracer = trace.get_tracer("toad_telemetry", "0.1.0")
        return _tracer
        
    except ImportError as e:
        # OTEL not installed, return a no-op tracer
        return _NoOpTracer()


class _NoOpSpan:
    """No-op span for when OTEL is not available."""
    def set_attribute(self, key: str, value: Any) -> None:
        pass
    
    def set_status(self, status: Any) -> None:
        pass
    
    def record_exception(self, exception: Exception) -> None:
        pass
    
    def end(self) -> None:
        pass
    
    def __enter__(self):
        return self
    
    def __exit__(self, *args):
        pass


class _NoOpTracer:
    """No-op tracer for when OTEL is not available."""
    def start_span(self, name: str, **kwargs) -> _NoOpSpan:
        return _NoOpSpan()
    
    @contextmanager
    def start_as_current_span(self, name: str, **kwargs):
        yield _NoOpSpan()


def _get_tool_name(tool_call: dict) -> str:
    """Extract tool name from tool call."""
    if "toolName" in tool_call:
        return tool_call["toolName"]
    if "name" in tool_call:
        return tool_call["name"]
    return "unknown_tool"


def _get_tool_kind(tool_call: dict) -> str:
    """Extract tool kind from tool call."""
    return tool_call.get("kind", "unknown")


def _create_patched_rpc_session_update(original_func):
    """Create wrapper for rpc_session_update that adds telemetry."""
    @functools.wraps(original_func)
    def wrapper(self, sessionId: str, update: dict, _meta: dict | None = None):
        tracer = get_tracer()
        config = _config or ToadTelemetryConfig()
        
        if not config.enabled:
            return original_func(self, sessionId, update, _meta)
        
        session_update_type = update.get("sessionUpdate", "unknown")
        
        # Handle tool_call start
        if session_update_type == "tool_call":
            tool_call_id = update.get("toolCallId", "unknown")
            tool_name = _get_tool_name(update)
            tool_kind = _get_tool_kind(update)
            
            span = tracer.start_span(
                f"tool.{tool_name}",
                attributes={
                    "toad.tool.id": tool_call_id,
                    "toad.tool.name": tool_name,
                    "toad.tool.kind": tool_kind,
                    "toad.session.id": sessionId,
                    "toad.agent": config.agent_name,
                }
            )
            _span_stack[tool_call_id] = {
                "span": span,
                "start_time": time.time(),
                "tool_name": tool_name,
            }
        
        # Handle tool_call_update (completion/error)
        elif session_update_type == "tool_call_update":
            tool_call_id = update.get("toolCallId", "unknown")
            status = update.get("status", "unknown")
            
            if tool_call_id in _span_stack:
                span_info = _span_stack[tool_call_id]
                span = span_info["span"]
                
                # Add completion attributes
                span.set_attribute("toad.tool.status", status)
                span.set_attribute("toad.tool.duration_ms", 
                    (time.time() - span_info["start_time"]) * 1000)
                
                # Check for errors
                if error := update.get("error"):
                    try:
                        from opentelemetry.trace import StatusCode
                        span.set_status(StatusCode.ERROR, str(error))
                    except ImportError:
                        pass
                    span.set_attribute("toad.tool.error", str(error))
                
                # End span on completion
                if status in ("completed", "error", "cancelled"):
                    span.end()
                    del _span_stack[tool_call_id]
        
        return original_func(self, sessionId, update, _meta)
    
    return wrapper


def _create_patched_send_prompt(original_func):
    """Create wrapper for send_prompt that tracks turn timing."""
    @functools.wraps(original_func)
    async def wrapper(self, prompt: str):
        tracer = get_tracer()
        config = _config or ToadTelemetryConfig()
        
        if not config.enabled:
            return await original_func(self, prompt)
        
        with tracer.start_as_current_span(
            "agent.turn",
            attributes={
                "toad.prompt.length": len(prompt),
                "toad.agent": config.agent_name,
            }
        ) as span:
            start_time = time.time()
            try:
                result = await original_func(self, prompt)
                span.set_attribute("toad.turn.stop_reason", result or "unknown")
                return result
            except Exception as e:
                span.record_exception(e)
                try:
                    from opentelemetry.trace import StatusCode
                    span.set_status(StatusCode.ERROR, str(e))
                except ImportError:
                    pass
                raise
            finally:
                span.set_attribute("toad.turn.duration_ms", 
                    (time.time() - start_time) * 1000)
    
    return wrapper


def _apply_patches():
    """Apply patches to Toad's Agent class. Called after toad is fully loaded."""
    global _original_rpc_session_update, _original_send_prompt, _instrumented
    
    if _instrumented:
        return True
    
    try:
        from toad.acp.agent import Agent
        
        # Patch rpc_session_update
        _original_rpc_session_update = Agent.rpc_session_update
        Agent.rpc_session_update = _create_patched_rpc_session_update(_original_rpc_session_update)
        
        # Patch send_prompt  
        _original_send_prompt = Agent.send_prompt
        Agent.send_prompt = _create_patched_send_prompt(_original_send_prompt)
        
        _instrumented = True
        return True
        
    except Exception as e:
        import warnings
        warnings.warn(f"Could not apply Toad patches: {e}")
        return False


def _install_deferred_patch():
    """Install import hook to patch Toad after it's loaded."""
    global _deferred_patch_installed
    
    if _deferred_patch_installed:
        return
    
    import sys
    
    class ToadPatchFinder:
        """Import hook that patches toad.acp.agent after it's loaded."""
        
        def find_module(self, fullname, path=None):
            # We're looking for when toad.app is imported (entry point)
            if fullname == "toad.app":
                return self
            return None
        
        def load_module(self, fullname):
            # Remove ourselves to avoid infinite recursion
            if self in sys.meta_path:
                sys.meta_path.remove(self)
            
            # Import the real module
            import importlib
            module = importlib.import_module(fullname)
            
            # Now toad is loaded, apply our patches
            _apply_patches()
            
            return module
    
    # Install the import hook
    sys.meta_path.insert(0, ToadPatchFinder())
    _deferred_patch_installed = True


def _cleanup():
    """Cleanup function to end any remaining spans."""
    for tool_id, span_info in list(_span_stack.items()):
        try:
            span_info["span"].end()
        except Exception:
            pass
    _span_stack.clear()


def instrument_toad(config: Optional[ToadTelemetryConfig] = None) -> bool:
    """
    Instrument Toad with OpenTelemetry tracing.
    
    Uses deferred patching via import hooks to avoid circular imports.
    Patches are applied when toad.app is imported.
    
    Args:
        config: Optional configuration. Uses environment variables if not provided.
    
    Returns:
        True if instrumentation was set up (patches will be applied later).
    """
    global _config
    
    _config = config or ToadTelemetryConfig()
    
    if not _config.enabled:
        return False
    
    # Register cleanup handler
    atexit.register(_cleanup)
    
    # Check if toad is already loaded
    import sys
    if "toad.acp.agent" in sys.modules:
        # Toad already loaded, patch directly
        return _apply_patches()
    else:
        # Install deferred patch
        _install_deferred_patch()
        return True


def uninstrument_toad() -> bool:
    """
    Remove Toad instrumentation.
    
    Returns:
        True if uninstrumentation succeeded, False otherwise.
    """
    global _original_rpc_session_update, _original_send_prompt, _instrumented
    
    if not _instrumented:
        return True
    
    try:
        from toad.acp.agent import Agent
        
        if _original_rpc_session_update is not None:
            Agent.rpc_session_update = _original_rpc_session_update
            _original_rpc_session_update = None
        
        if _original_send_prompt is not None:
            Agent.send_prompt = _original_send_prompt
            _original_send_prompt = None
        
        _instrumented = False
        _cleanup()
        
        return True
        
    except ImportError:
        return False
