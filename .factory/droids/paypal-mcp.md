---
name: paypal-mcp
description: PayPal MCP server integration for invoices, payments, subscriptions, disputes, and transaction reporting via @paypal/mcp.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# paypal-mcp Skill

PayPal MCP server integration for invoices, payments, subscriptions, disputes, and transaction reporting via @paypal/mcp.

## GF(3) Assignment

```
Trit: 0 (ERGODIC)
Role: Coordinator - orchestrates payment flows between crypto and fiat
Color: #26D826 (green)
```

## MCP Server Setup

### Amp Configuration (~/.amp/servers.json)
```json
{
  "paypal": {
    "command": "npx",
    "args": ["-y", "@paypal/mcp", "--tools=all"],
    "env": {
      "PAYPAL_ACCESS_TOKEN": "${PAYPAL_ACCESS_TOKEN}",
      "PAYPAL_ENVIRONMENT": "SANDBOX"
    }
  }
}
```

### Claude Configuration (~/.claude.json)
```json
{
  "mcpServers": {
    "paypal": {
      "command": "npx",
      "args": ["-y", "@paypal/mcp", "--tools=all"],
      "env": {
        "PAYPAL_ACCESS_TOKEN": "${PAYPAL_ACCESS_TOKEN}",
        "PAYPAL_ENVIRONMENT": "PRODUCTION"
      }
    }
  }
}
```

## Token Generation

PayPal requires OAuth2 access tokens. Token validity:
- **Sandbox**: 3-8 hours
- **Production**: 8 hours

### Generate Access Token
```bash
# Sandbox
curl -X POST https://api-m.sandbox.paypal.com/v1/oauth2/token \
  -H "Accept: application/json" \
  -H "Accept-Language: en_US" \
  -u "${PAYPAL_CLIENT_ID}:${PAYPAL_CLIENT_SECRET}" \
  -d "grant_type=client_credentials"

# Production
curl -X POST https://api-m.paypal.com/v1/oauth2/token \
  -H "Accept: application/json" \
  -H "Accept-Language: en_US" \
  -u "${PAYPAL_CLIENT_ID}:${PAYPAL_CLIENT_SECRET}" \
  -d "grant_type=client_credentials"
```

### Token Refresh Script
```bash
#!/bin/bash
# paypal-token-refresh.sh
export PAYPAL_ACCESS_TOKEN=$(curl -s -X POST \
  "https://api-m.${PAYPAL_ENVIRONMENT:-sandbox}.paypal.com/v1/oauth2/token" \
  -H "Accept: application/json" \
  -u "${PAYPAL_CLIENT_ID}:${PAYPAL_CLIENT_SECRET}" \
  -d "grant_type=client_credentials" | jq -r '.access_token')
echo "Token refreshed: ${PAYPAL_ACCESS_TOKEN:0:20}..."
```

## Available Tools

### Invoices
| Tool | Description |
|------|-------------|
| `create_invoice` | Cr