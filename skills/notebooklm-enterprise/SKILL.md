---
name: notebooklm-enterprise
description: "NotebookLM Enterprise API via Discovery Engine — notebook CRUD, source management, audio overviews, flashcard pipeline integration"
version: 1.1.0
trit: 0
trit_label: ERGODIC
---

# NotebookLM Enterprise API

**Trit**: 0 (ERGODIC — coordinates knowledge between sources and consumers)

Accessed through the **Discovery Engine API** (`discoveryengine.googleapis.com`), not a standalone API.

## Interaction with nblm-flashcards skill

This skill is the **provider** of notebooks consumed by `nblm-flashcards`:

```
notebooklm-enterprise (this skill)     nblm-flashcards
────────────────────────────────────    ─────────────────────
Create notebook                    →   Read notebook sources
Add DeepWiki URLs as sources       →   Generate flashcards via Gemini
Check ingestion status             →   Batch per source (5/call)
Share with users                   →   Merge decks across notebooks
Audio overview generation          →   Emacs drill (M-x nblm-drill-all)
```

### GF(3) Triad

```
notebooklm-enterprise (0) + nblm-flashcards (+1) + drill-verification (-1) = 0
```

## Base URL

```
https://global-discoveryengine.googleapis.com/v1alpha
```

All endpoints use **project number** (not project ID):
```
projects/302712368086/locations/global/notebooks/{NOTEBOOK_ID}
```

## Active Notebooks (plurigrid/bmorphism ecosystem)

| Notebook | ID | Sources | Purpose |
|----------|----|---------|---------|
| Original flashcard deck | `9ca780dc-4e0f-4f57-9262-a6090af028e4` | 300 | Core bmorphism + plurigrid repos |
| Backfill 1/4 | `ce99b119-74f6-4e24-bd14-333aade95950` | 300 | Gap repos chunk 1 |
| Backfill 2/4 | (see backfill-state.json) | 300 | Gap repos chunk 2 |
| Backfill 3/4 | `aa69ef7a-3fb2-4ba0-863e-d74ef3b670eb` | 300 | Gap repos chunk 3 |
| Backfill 4/4 | `57c2d969-ebc9-4402-b8b1-c2c2d83abd40` | 44 | Gap repos chunk 4 |
| Peer Reality Citations | `240d5525-47f3-443e-bc65-000d374636e0` | — | Academic papers |
| Gay.jl Color Generation | `9102a46e-7443-4d54-a2ed-f36446fd229b` | — | Deterministic color |
| Aptos On-Chain | `2d199255-1322-45b7-b91b-6067787f3f84` | — | Move contracts |
| Plurigrid Portal | `8c6a2293-0987-4515-ab7e-55fec1348f36` | — | Infrastructure |

## API Quick Reference

### Create Notebook
```bash
curl -X POST "${BASE}/notebooks" \
  -H "Authorization: Bearer ${TOKEN}" \
  -d '{"title": "My Notebook"}'
```

### Add Sources (batch of 5)
```bash
curl -X POST "${BASE}/notebooks/${NB}/sources:batchCreate" \
  -H "Authorization: Bearer ${TOKEN}" \
  -d '{"userContents": [{"webContent": {"url": "https://deepwiki.com/org/repo"}}]}'
```

**Critical**: field is `webContent.url`, not `uri`, not `googleDriveSource`.

### Get Notebook + Sources
```bash
curl -s "${BASE}/notebooks/${NB}" -H "Authorization: Bearer ${TOKEN}"
```

### Share
```bash
curl -X POST "${BASE}/notebooks/${NB}:share" \
  -H "Authorization: Bearer ${TOKEN}" \
  -d '{"accountAndRoles": [{"email": "user@example.com", "role": "PROJECT_ROLE_WRITER"}]}'
```

### Audio Overview
```bash
curl -X POST "${BASE}/notebooks/${NB}/audioOverviews" \
  -H "Authorization: Bearer ${TOKEN}" -d '{}'
```

## Source URL Rules

**Works**: DeepWiki URLs, direct PDFs, PMC, arXiv, Frontiers, PLOS, Nature
**Fails**: DOI redirects (`doi.org/...`), ScienceDirect, paywalled publishers

For the flashcard pipeline, all sources are DeepWiki URLs: `https://deepwiki.com/{org}/{repo}`

## Babashka Pipeline Integration

The backfill pipeline (`n/nblm_backfill.bb`) automates this skill's operations:

```bash
bb n/nblm_backfill.bb --dry-run    # plan: chunk 944 repos into 4 notebooks
bb n/nblm_backfill.bb              # create notebooks + add sources
bb n/nblm_backfill.bb --status     # check ingestion across all notebooks
bb n/nblm_backfill.bb --generate   # trigger nblm-flashcards for each notebook
```

State persisted at `~/worlds/n/flashcards/backfill-state.json`.

## GCP Context

| Field | Value |
|-------|-------|
| Project ID | `merovingians` |
| Project Number | `302712368086` |
| API | `discoveryengine.googleapis.com` |
| Version | `v1alpha` only |
| Auth | `gcloud auth print-access-token` |

## Gotchas

1. Use project **number** not ID in API paths
2. `v1alpha` only — no v1 or v1beta
3. No list-sources endpoint — sources in GET notebook response
4. Batch size 5-10 for source adds
5. Ingestion is async — poll for `SOURCE_STATUS_COMPLETE`
6. DOI URLs always fail (no redirect following)
7. Duplicate sources silently accepted
8. Audio overview: empty `{}` body only, field names rejected
9. Audio has no download API — listen in notebook UI only
10. Podcast API returns 404 despite docs

## Related Skills

- `nblm-flashcards` — Flashcard generation + Emacs drill (PLUS, consumer)
- `deepwiki-mcp` — Source documentation URLs (ERGODIC, source provider)
- `babashka` — Pipeline orchestration
- `gh-cli` — Repo discovery for gap analysis
- `vertex-ai` — Gemini model access for flashcard generation
