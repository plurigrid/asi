# Firecrawl Snapshot (Combined)

This folder merges GitHub and external Firecrawl indices into a single combined index and sonification.

Files:
- index.json: merged index (GitHub + external)
- index.md: human-readable index
- merge_combined.py: generator script
- sonify_combined_parallel.rb: parallel sonification script
- combined_sonification_parallel.wav: rendered audio output
- combined_sonification_parallel.json: event metadata

To regenerate:
- python .topos/firecrawl/combined/merge_combined.py
- ruby .topos/firecrawl/combined/sonify_combined_parallel.rb
