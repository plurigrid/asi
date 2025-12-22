# Firecrawl Snapshot (GitHub)

This directory contains Firecrawl-extracted metadata for GitHub URLs referenced by local project docs.

Files:
- github_seed_urls.txt: seed list of GitHub URLs harvested from project docs.
- github/index.json: extracted metadata (title, summary, topics, repo, status).
- github/index.md: human-readable index.
- github/sonify_firecrawl.rb: sonification script (reads github/index.json).
- firecrawl_sonification.wav: rendered audio output.
- firecrawl_sonification.json: event metadata for the rendered audio.
- firecrawl_sonification_parallel.wav: parallel-layered sonification output.
- firecrawl_sonification_parallel.json: event metadata for the parallel output.
- external/: non-GitHub Firecrawl results and merged index.
  - external/external_sonification_parallel.wav: parallel sonification for external URLs.
- combined/: merged GitHub + external index and parallel sonification.

Notes:
- Some URLs returned "not found" (status = not_found). See index.json for details.
- All outputs are ASCII-only by default.

To re-run sonification:
- ruby .topos/firecrawl/github/sonify_firecrawl.rb
- ruby .topos/firecrawl/github/sonify_firecrawl_parallel.rb
