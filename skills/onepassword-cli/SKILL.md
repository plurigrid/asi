---
name: onepassword-cli
description: 1Password CLI (op) for secure secret management, credential injection, and shell plugin auth. Use when users need secrets, API keys, env vars, or authenticating third-party CLIs.
version: 1.0.0
trit: 0
role: ERGODIC
tags: [secrets, 1password, credentials, security, auth]
deployed: 2026-02-19
---

# 1Password CLI Skill

Manage secrets via `op` CLI integrated with the 1Password desktop app.

## Prerequisites

- `op` installed via `flox install _1password-cli`
- 1Password desktop app with **Settings → Developer → Integrate with 1Password CLI** enabled
- Authenticated session: `eval $(op signin)`

## Session Management

**CRITICAL**: Always initialize the session before any `op` command:

```bash
eval $(op signin)
```

Without this, `op` commands fail with "account is not signed in". The `eval` sets the `OP_SESSION_*` env var in the current shell.

Verify with:
```bash
op whoami
```

## Core Commands

| Command | Purpose |
|---------|---------|
| `op vault list` | List all vaults |
| `op item list` | List all items across vaults |
| `op item get "Name"` | Get full item details |
| `op item get "Name" --field password --reveal` | Get specific field value |
| `op read op://Vault/Item/Field` | Secret reference (scriptable) |
| `op document get "Name"` | Download stored documents |
| `op inject -i template -o output` | Fill templates with secrets |
| `op run --env-file .env -- cmd` | Inject secrets as env vars |

## Secret References

The `op://` URI scheme for embedding secrets in configs and scripts:

```bash
# Read a single secret
op read "op://VaultName/ItemName/field"

# Export to env var
export API_KEY=$(op read "op://VaultName/ItemName/credential")

# Use in one-liners
op run --env-file .env -- docker compose up
```

### Template Injection

Create a template file with `op://` references:
```yaml
# config.template.yml
api_key: op://VaultName/APIService/credential
db_password: op://VaultName/Database/password
```

Then inject:
```bash
op inject -i config.template.yml -o config.yml
```

## Shell Plugins

Authenticate third-party CLIs through 1Password instead of plaintext tokens:

```bash
# Initialize a plugin (e.g., GitHub CLI)
op plugin init gh

# After setup, gh authenticates via 1Password automatically
gh repo list
```

Available plugins include: `gh`, `aws`, `openai`, `mysql`, `psql`, `vercel`, `stripe`, `flyctl`, `heroku`, `brew`, `cargo`, `snyk`, `docker`, and 60+ more.

List all: `op plugin list`

## Item CRUD

```bash
# Create a new item
op item create --category=login \
  --title="My Service" \
  --vault="Shared" \
  --field username=admin \
  --field password=secret123

# Edit an item
op item edit "My Service" --field password=newpass

# Delete an item
op item delete "My Service"

# Search items
op item list --tags="production" --vault="VaultName"
```

## Workflow Patterns

### Inject Secrets into a Process
```bash
# .env.template
DB_HOST=op://VaultName/Database/host
DB_PASS=op://VaultName/Database/password

# Run with secrets injected (never touch disk)
op run --env-file .env.template -- ./start-server.sh
```

### CI/CD with Service Accounts
```bash
# Create service account token (one-time)
op service-account create "CI Bot" --vault VaultName

# In CI, use OP_SERVICE_ACCOUNT_TOKEN env var
export OP_SERVICE_ACCOUNT_TOKEN="..."
op read "op://VaultName/Deploy Key/credential"
```

### Rotate Credentials
```bash
op item edit "API Key" --field credential=$(openssl rand -hex 32)
```

## Account Info

Verify your current setup:
```bash
op whoami
op vault list
```

## Error Handling

| Error | Fix |
|-------|-----|
| "account is not signed in" | Run `eval $(op signin)` |
| "no item found" | Check vault name and item title spelling |
| "You do not have permission" | Verify vault access in 1Password app |
| Session expires | Re-run `eval $(op signin)` |

## JSON Output

Add `--format json` to any command for machine-parseable output:

```bash
op item list --format json | jq '.[].title'
op item get "My Item" --format json | jq '.fields[] | select(.label=="password") | .value'
```
