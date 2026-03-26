#!/usr/bin/env bash
# Search public OSF projects by keyword
# Usage: osf-search.sh <keyword> [page_size]
set -euo pipefail

KEYWORD="${1:?Usage: osf-search.sh <keyword> [page_size]}"
PAGE_SIZE="${2:-10}"

curl -sfL --globoff "https://api.osf.io/v2/nodes/?filter[title]=${KEYWORD}&page[size]=${PAGE_SIZE}" | \
  jq -r '.data[] | "\(.id)\t\(.attributes.title)\t\(.attributes.date_modified)\t\(.attributes.description[:80] // "-")"' | \
  column -t -s $'\t'
