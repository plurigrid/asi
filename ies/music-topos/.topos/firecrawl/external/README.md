# Firecrawl Snapshot (External URLs)

This folder contains Firecrawl extraction results for non-GitHub URLs referenced by local project docs.

Files:
- external_seed_urls.txt: all extracted non-GitHub URLs from docs.
- external_seed_urls.filtered.txt: filtered list (63 URLs) used for Firecrawl.
- raw/: raw batch outputs from Firecrawl extract calls.
- index.json: merged index for requested URLs (generated).
- index.md: human-readable index.
- sonify_external_parallel.rb: parallel sonification script (reads index.json).
- external_sonification_parallel.wav: rendered audio output.
- external_sonification_parallel.json: event metadata for the rendered audio.

Notes:
- Firecrawl sometimes returns extra URLs (subpages or related content). The merged index filters to requested URLs only.
- All generated files are ASCII-only.

To regenerate the index after new raw batches:
- python .topos/firecrawl/external/merge_external.py

To regenerate external sonification:
- ruby .topos/firecrawl/external/sonify_external_parallel.rb
