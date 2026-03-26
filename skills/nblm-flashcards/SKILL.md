---
name: nblm-flashcards
description: "Generate and drill flashcards from NotebookLM Enterprise notebooks via Gemini (Vertex AI), with Emacs UI and babashka backfill pipeline"
version: 1.1.0
trit: 1
trit_label: PLUS
---

# NotebookLM Enterprise Flashcard Generator + Drill

**Trit**: +1 (PLUS — knowledge extraction and spaced repetition from notebook sources)

## What This Does

Extracts knowledge from the entire plurigrid/bmorphism ecosystem (1,244 repos across 5 NBLM notebooks) into drillable flashcards.

```
GitHub repos (1,244 total)
    |
    v
DeepWiki URLs → NBLM Enterprise (5 notebooks × 300 sources)
    |
    v
Discovery Engine API → fetch source titles
    |
    v
Gemini 2.5 Flash (Vertex AI) → batched generation
    |  5 sources/batch, 10 cards/source, token auto-refresh
    v
flashcards.json + quiz.json (per notebook)
    |
    v
bb n/nblm_merge.bb → all-flashcards.json (deduped)
    |
    v
Emacs drill (M-x nblm-drill-all)
```

## Interaction with notebooklm-enterprise skill

This skill is the **consumer** of notebooks managed by `notebooklm-enterprise`:

| notebooklm-enterprise (ERGODIC) | nblm-flashcards (PLUS) |
|----------------------------------|------------------------|
| Creates notebooks | Reads notebook sources |
| Adds DeepWiki URLs as sources | Generates flashcards from sources |
| Manages source ingestion status | Batches Gemini calls per source |
| Shares notebooks with users | Merges decks across notebooks |

### GF(3) Triad

```
notebooklm-enterprise (0) + nblm-flashcards (+1) + [verifier] (-1) = 0
```

The verifier role is filled by the Emacs drill itself — missed cards feed back as verification signal.

## Notebooks (as of 2026-03-25)

| Notebook | ID | Sources | Role |
|----------|----|---------|------|
| Original | `9ca780dc-4e0f-4f57-9262-a6090af028e4` | 300 | bmorphism + plurigrid core |
| Backfill 1/4 | `ce99b119-74f6-4e24-bd14-333aade95950` | 300 | Gap repos chunk 1 |
| Backfill 2/4 | (see backfill-state.json) | 300 | Gap repos chunk 2 |
| Backfill 3/4 | `aa69ef7a-3fb2-4ba0-863e-d74ef3b670eb` | 300 | Gap repos chunk 3 |
| Backfill 4/4 | `57c2d969-ebc9-4402-b8b1-c2c2d83abd40` | 44 | Gap repos chunk 4 |

## Pipeline

All scripts live in `~/worlds/n/`:

```bash
# Generate flashcards from a single notebook
hy n/nblm_flashcards.hy --notebook-id <UUID> --per-source 10 --batch-size 5

# Backfill: create notebooks for uncovered repos
bb n/nblm_backfill.bb              # create + add sources
bb n/nblm_backfill.bb --status     # check ingestion
bb n/nblm_backfill.bb --generate   # generate flashcards per notebook

# Merge all decks
bb n/nblm_merge.bb

# Drill in Emacs
emacs -nw --load ~/worlds/n/nblm-drill.el
# M-x nblm-drill-all    (full merged deck)
# M-x nblm-drill-repo   (filter by org/repo)
```

## Key Parameters

| Arg | Default | What |
|-----|---------|------|
| `--per-source` | 10 | Flashcards per notebook source |
| `--batch-size` | 5 | Sources per Gemini call (50 cards/call sweet spot) |
| `--difficulty` | hard | easy / medium / hard |
| `--model` | gemini-2.5-flash | Vertex AI model |

## Architecture

- Token auto-refreshes every 30 min (gcloud tokens expire at 1hr)
- Truncated JSON repaired by finding last complete `}` and closing array
- Discovery Engine `v1alpha` for notebook source listing
- Gemini via Vertex AI REST (`generateContent`), region `us-central1`
- `maxOutputTokens: 65536`, `temperature: 0.7`
- GCP project: `merovingians` (302712368086)

## Ecosystem Coverage

| Org | Repos | Coverage |
|-----|-------|----------|
| `bmorphism/` | 406 | 100% (across original + backfill) |
| `plurigrid/` | 586 | 100% (across original + backfill) |
| Third-party | 131 | 100% (backfill chunks 1-4) |
| **Total** | **1,244** | **100%** |

## Related Skills

- `notebooklm-enterprise` — NBLM API (notebook CRUD, source management)
- `deepwiki-mcp` — DeepWiki documentation for source URLs
- `babashka` — Pipeline orchestration (backfill, merge)
- `gh-cli` — Repo discovery for gap analysis
- `gh-interactome` — Author/repo network for cross-repo flashcards
