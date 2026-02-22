---
name: osf-datasets
description: Access Open Science Framework (OSF) datasets via CLI using osfclient and the OSF v2 API
---

# OSF Datasets

CLI access to Open Science Framework datasets via `osfclient` and the REST API.

## Setup

```bash
pip install osfclient
```

## Authentication

```bash
# Option A: Personal Access Token (preferred) — generate at osf.io/settings/tokens
export OSF_TOKEN=<pat>

# Option B: credentials
export OSF_USERNAME=user@example.com
export OSF_PASSWORD=pass
```

Or per-directory `.osfcli.config`:

```ini
[osf]
username = user@example.com
project = abc12
```

## Project ID

The 5-character alphanumeric slug from any `osf.io/<id>` URL. Example: `osf.io/abc12` → project ID is `abc12`.

## Core Commands

| Command | Purpose |
|---|---|
| `osf -p <id> ls` | List all files |
| `osf -p <id> clone [dir]` | Download entire project |
| `osf -p <id> fetch osfstorage/path.csv local.csv` | Download single file |
| `osf -p <id> upload local.csv osfstorage/path.csv` | Upload file |
| `osf -p <id> geturl osfstorage/path.csv` | Get web URL |

Remote paths are prefixed with the storage provider, typically `osfstorage/`.

## Direct API Access

Base URL: `https://api.osf.io/v2/`

**Important**: Use `--globoff` with curl — OSF query params use `[]` which curl interprets as glob ranges.

```bash
# List project files
curl -sL --globoff "https://api.osf.io/v2/nodes/<id>/files/osfstorage/" | jq '.data[].attributes.name'

# Get project metadata
curl -sL --globoff "https://api.osf.io/v2/nodes/<id>/" | jq '.data.attributes'

# Search public nodes by title
curl -sL --globoff "https://api.osf.io/v2/nodes/?filter[title]=keyword&page[size]=20" | jq '.data[] | {id, title: .attributes.title}'

# Browse subfolder (use folder ID from parent listing)
curl -sL --globoff "https://api.osf.io/v2/nodes/<id>/files/osfstorage/<folder_id>/" | jq '.data[].attributes.name'

# With auth
curl -sL --globoff -H "Authorization: Bearer $OSF_TOKEN" "https://api.osf.io/v2/nodes/<id>/files/osfstorage/"
```

File download links are in `data[].links.download` — follow redirects with `curl -L -o`.

## Workflow: Bulk Dataset Fetch

```bash
# 1. Find the project
osf -p abc12 ls

# 2. Clone everything
osf -p abc12 clone ./dataset

# 3. Or fetch selectively
osf -p abc12 fetch osfstorage/data/experiment1.csv ./experiment1.csv
```

## Guidelines

- Public projects need no auth; private ones require `OSF_TOKEN` or credentials
- `clone` mirrors the remote directory structure locally
- `fetch` requires both remote and local path arguments
- The API paginates at 10 items by default; use `?page[size]=100` for larger listings
- Rate limits apply — add brief sleeps for batch operations
