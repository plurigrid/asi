"""ExoPriors Scry MCP Server — stdio transport.

Wraps the ExoPriors Scry API (https://api.exopriors.com) as four MCP tools:
  scry_query, scry_embed, scry_estimate, scry_schema

Run:  python scry_mcp.py
"""

from __future__ import annotations

import json
import ssl
import sys
from typing import Any

import httpx
from mcp.server import Server
from mcp.server.stdio import stdio_server
from mcp.types import TextContent, Tool

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

BASE_URL = "https://api.exopriors.com"
import os as _os
_API_KEY = _os.environ.get("EXOPRIORS_API_KEY", "exopriors_public_readonly_v1_2025")
AUTH_HEADER = {"Authorization": f"Bearer {_API_KEY}"}
TIMEOUT = httpx.Timeout(60.0, connect=10.0)

# ---------------------------------------------------------------------------
# HTTP client helpers
# ---------------------------------------------------------------------------


def _make_ssl_context() -> ssl.SSLContext:
    """Build an SSL context that works with Cloudflare endpoints.

    Python 3.14 ships OpenSSL 3.5.x which defaults to TLS 1.3 only in some
    builds.  Cloudflare usually handles TLS 1.3 fine, but if the handshake
    fails we loosen the minimum to TLS 1.2 as a fallback.
    """
    ctx = ssl.create_default_context()
    # Ensure TLS 1.2 is allowed alongside 1.3
    ctx.minimum_version = ssl.TLSVersion.TLSv1_2
    return ctx


def _build_client() -> httpx.AsyncClient:
    proxy = _os.environ.get("EXOPRIORS_SOCKS_PROXY")
    return httpx.AsyncClient(
        base_url=BASE_URL,
        headers=AUTH_HEADER,
        timeout=TIMEOUT,
        http2=True,
        verify=_make_ssl_context(),
        **({"proxy": proxy} if proxy else {}),
    )


async def _request(
    method: str,
    path: str,
    *,
    content: str | None = None,
    json_body: dict[str, Any] | None = None,
    content_type: str | None = None,
) -> dict[str, Any]:
    """Fire a single API request and return parsed JSON."""
    headers: dict[str, str] = {}
    if content_type:
        headers["Content-Type"] = content_type

    async with _build_client() as client:
        resp = await client.request(
            method,
            path,
            content=content.encode() if content else None,
            json=json_body,
            headers=headers,
        )
        resp.raise_for_status()
        return resp.json()


# ---------------------------------------------------------------------------
# MCP server definition
# ---------------------------------------------------------------------------

server = Server("exopriors-scry")


@server.list_tools()
async def list_tools() -> list[Tool]:
    return [
        Tool(
            name="scry_query",
            description=(
                "Execute a SQL query against the ExoPriors Scry warehouse. "
                "Returns columns, rows, row_count, and duration_ms."
            ),
            inputSchema={
                "type": "object",
                "properties": {
                    "sql": {
                        "type": "string",
                        "description": "SQL query to execute.",
                    },
                    "include_vectors": {
                        "type": "boolean",
                        "description": "Include vector columns in results (default false).",
                        "default": False,
                    },
                },
                "required": ["sql"],
            },
        ),
        Tool(
            name="scry_embed",
            description=(
                "Store a named text embedding in ExoPriors Scry. "
                "Uses the voyage-4-lite model."
            ),
            inputSchema={
                "type": "object",
                "properties": {
                    "text": {
                        "type": "string",
                        "description": "Text to embed.",
                    },
                    "name": {
                        "type": "string",
                        "description": "Handle name for the stored embedding.",
                    },
                },
                "required": ["text", "name"],
            },
        ),
        Tool(
            name="scry_estimate",
            description=(
                "Estimate the cost and execution time of a SQL query "
                "without actually running it."
            ),
            inputSchema={
                "type": "object",
                "properties": {
                    "sql": {
                        "type": "string",
                        "description": "SQL query to estimate.",
                    },
                },
                "required": ["sql"],
            },
        ),
        Tool(
            name="scry_schema",
            description="Retrieve the ExoPriors Scry warehouse schema.",
            inputSchema={
                "type": "object",
                "properties": {},
            },
        ),
    ]


@server.call_tool()
async def call_tool(name: str, arguments: dict[str, Any]) -> list[TextContent]:
    try:
        if name == "scry_query":
            sql = arguments["sql"]
            include_vectors = arguments.get("include_vectors", False)
            path = "/v1/scry/query"
            if include_vectors:
                path += "?include_vectors=true"
            result = await _request(
                "POST",
                path,
                content=sql,
                content_type="text/plain",
            )

        elif name == "scry_embed":
            result = await _request(
                "POST",
                "/v1/scry/embed",
                json_body={
                    "text": arguments["text"],
                    "name": arguments["name"],
                    "model": "voyage-4-lite",
                },
            )

        elif name == "scry_estimate":
            result = await _request(
                "POST",
                "/v1/scry/estimate",
                json_body={"sql": arguments["sql"]},
            )

        elif name == "scry_schema":
            result = await _request("GET", "/v1/scry/schema")

        else:
            return [TextContent(type="text", text=f"Unknown tool: {name}")]

        # Strip vector arrays from query results when not requested
        if name == "scry_query" and not arguments.get("include_vectors", False):
            if "rows" in result and "columns" in result:
                vec_indices = {
                    i
                    for i, col in enumerate(result["columns"])
                    if col.get("type", "").startswith("FLOAT[")
                    or col.get("type", "") == "EMBEDDING"
                }
                if vec_indices:
                    result["columns"] = [
                        c
                        for i, c in enumerate(result["columns"])
                        if i not in vec_indices
                    ]
                    result["rows"] = [
                        [v for i, v in enumerate(row) if i not in vec_indices]
                        for row in result["rows"]
                    ]

        return [TextContent(type="text", text=json.dumps(result, indent=2))]

    except httpx.HTTPStatusError as exc:
        body = exc.response.text
        return [
            TextContent(
                type="text",
                text=f"HTTP {exc.response.status_code}: {body}",
            )
        ]
    except Exception as exc:
        return [TextContent(type="text", text=f"Error: {exc}")]


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


async def main() -> None:
    async with stdio_server() as (read_stream, write_stream):
        await server.run(read_stream, write_stream, server.create_initialization_options())


if __name__ == "__main__":
    import asyncio

    asyncio.run(main())
