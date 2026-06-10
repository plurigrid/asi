---
name: cc-trace
description: 'Intercept and debug Claude Code API requests using mitmproxy. Inspect system prompts, tool definitions, token usage, and streaming responses. Triggers: cc-trace, mitmproxy, API interception, Claude Code debugging, traffic inspection.'
---

# CC-Trace: Claude Code API Interception

Capture and analyze Claude Code's API traffic using mitmproxy.

## Quick Start

```bash
# Start mitmproxy filtering Claude API traffic
mitmweb --web-port 8081 --set flow_filter='~d api.anthropic.com' --save-stream-file ~/claude-flows.mitm

# In another terminal, launch Claude through the proxy
proxy_claude
```

## Shell Function

Add to `~/.zshrc` or `~/.bashrc`:

```bash
proxy_claude() {
    export HTTP_PROXY=http://127.0.0.1:8080
    export HTTPS_PROXY=http://127.0.0.1:8080
    export NODE_EXTRA_CA_CERTS="$HOME/.mitmproxy/mitmproxy-ca-cert.pem"
    export NODE_TLS_REJECT_UNAUTHORIZED=0
    claude
}
```

## Certificate Setup (macOS)

```bash
# Generate cert (start mitmproxy once, then quit)
mitmproxy --set flow_filter='~d api.anthropic.com'

# Trust cert in system keychain
sudo security add-trusted-cert -d -p ssl -p basic -k /Library/Keychains/System.keychain ~/.mitmproxy/mitmproxy-ca-cert.pem
```

## Filter Syntax

| Filter | Description |
|--------|-------------|
| `~d api.anthropic.com` | Only Anthropic API |
| `~m POST` | Only POST requests |
| `~s "tool_use"` | Responses containing tool_use |
| `~b "system"` | Body contains "system" |
| Combine | `~d api.anthropic.com & ~m POST & ~b "tool_use"` |

## Programmatic Analysis

```bash
# Dump all captured requests
mitmdump -r ~/claude-flows.mitm -n --set flow_detail=2

# Show last prompt sent
bash scripts/show-last-prompt.sh
```

## Python Addon Example

```python
from mitmproxy import http
import json

def response(flow: http.HTTPFlow):
    if "api.anthropic.com" in flow.request.pretty_host:
        req = json.loads(flow.request.get_text())
        print(f"Model: {req.get('model')}, Messages: {len(req.get('messages', []))}, Tools: {len(req.get('tools', []))}")
```

## Bundled Scripts

| Script | Purpose |
|--------|---------|
| `scripts/verify-setup.sh` | Check mitmproxy install, cert trust, shell config |
| `scripts/parse-streamed-response.ts` | Parse Anthropic SSE format |
| `scripts/extract-slash-commands.py` | Extract user messages from flows |
| `scripts/show-last-prompt.sh` | Show most recent user prompt |

## Troubleshooting

```bash
security find-certificate -c mitmproxy -a  # verify cert
lsof -i :8080                               # check port
curl -x http://127.0.0.1:8080 https://api.anthropic.com 2>&1 | head -5
```
