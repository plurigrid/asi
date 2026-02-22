#!/usr/bin/env bash
# Browse OSF project files via API (no osfclient needed)
# Usage: osf-browse.sh <project_id> [path]
set -euo pipefail

PROJECT_ID="${1:?Usage: osf-browse.sh <project_id> [path]}"
SUBPATH="${2:-}"

BASE="https://api.osf.io/v2/nodes/${PROJECT_ID}/files/osfstorage/${SUBPATH}"
AUTH_HEADER=""
[ -n "${OSF_TOKEN:-}" ] && AUTH_HEADER="Authorization: Bearer $OSF_TOKEN"

curl -sfL --globoff ${AUTH_HEADER:+-H "$AUTH_HEADER"} "$BASE" | \
  jq -r '.data[] | "\(.attributes.kind)\t\(.attributes.size // "-")\t\(.attributes.name)\t\(.links.download // "-")"' | \
  column -t -s $'\t'
