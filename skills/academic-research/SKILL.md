---
name: academic-research
description: Search academic papers across arXiv, PubMed, Semantic Scholar, bioRxiv, medRxiv, Google Scholar, and more. Get BibTeX citations, download PDFs, analyze citation networks. Use for literature reviews, finding papers, and academic research.
geodesic: true
moebius: "μ(n) ≠ 0"
---

# Academic Research Papers

Search and retrieve academic papers via multiple MCP servers.

## Available Servers

### paper-search
Multi-source paper search covering:
- arXiv, PubMed, bioRxiv, medRxiv
- Google Scholar, IACR, Semantic Scholar
- BibTeX export support

### semantic-scholar  
Full Semantic Scholar API access:
- Citation network analysis
- Author search
- Paper recommendations
- BibTeX, APA, MLA, Chicago formats

### arxiv
arXiv-specific search:
- Advanced search filters
- Citation analysis
- BibTeX, JSON, CSV, Markdown export

## When to Use

- Literature reviews
- Finding related papers
- Getting BibTeX citations
- Checking who cited a paper
- Finding papers by author
- Searching for specific topics

## Example Usage

### Search for Papers
```
paper_search(query="transformer attention mechanism", sources=["arxiv", "semantic_scholar"])
```

### Get Citations
```
semantic_scholar_citations(paper_id="...")
```

### arXiv Specific
```
arxiv_search(query="quantum computing", max_results=10)
```

## Other Available Servers (Not Installed)

From your `/Users/alice/worlds/l/mcp_servers.json`:
- `research-hub-mcp` - 11 sources + Unpaywall PDF access
- `zotero-mcp` - Connect to Zotero library
- `openalex-mcp` - 250M+ works database
- `crossref-mcp` - DOI metadata

Add more with:
```json
"server-name": {
  "command": "npx",
  "args": ["-y", "server-package-name"]
}
```

## Non-Backtracking Geodesic Qualification

**Condition**: μ(n) ≠ 0 (Möbius squarefree)

This skill is qualified for non-backtracking geodesic traversal:

1. **Prime Path**: No state revisited in skill invocation chain
2. **Möbius Filter**: Composite paths (backtracking) cancel via μ-inversion
3. **GF(3) Conservation**: Trit sum ≡ 0 (mod 3) across skill triplets
4. **Spectral Gap**: Ramanujan bound λ₂ ≤ 2√(k-1) for k-regular expansion

```
Geodesic Invariant:
  ∀ path P: backtrack(P) = ∅ ⟹ μ(|P|) ≠ 0
  
Möbius Inversion:
  f(n) = Σ_{d|n} g(d) ⟹ g(n) = Σ_{d|n} μ(n/d) f(d)
```
