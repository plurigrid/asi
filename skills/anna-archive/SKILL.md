---
name: anna-archive
description: "Anna's Archive integration for academic paper and book retrieval. Search shadow libraries (Library Genesis, Z-Library, Sci-Hub) via unified API with GF(3) balanced caching."
metadata:
  trit: 0
  version: "1.0.0"
  bundle: research
---

# Anna's Archive Skill

**Trit**: 0 (ERGODIC - coordinates retrieval across sources)  
**Foundation**: Anna's Archive API + academic-research skill  
**Principle**: Unified access to shadow libraries for research

## Overview

Anna's Archive is a search engine for shadow libraries:
- **Library Genesis** (LibGen) - books and papers
- **Z-Library** - ebooks
- **Sci-Hub** - academic papers
- **Internet Archive** - open library

This skill integrates with the `ANNA_SELF` token for authenticated access.

## Configuration

```bash
# In ~/.topos/.env
export ANNA_SELF="your_anna_archive_key"
```

## API Reference

### Search Operations

```javascript
// Using archive_of_anna (Node.js)
const ArchiveOfAnna = require('archive_of_anna');

// Search for books
const results = await ArchiveOfAnna.search({
  text: "category theory",
  lang: "en",
  content: "book_nonfiction",
  ext: "pdf",
  sort: "newest"
});

// Result structure
// [{
//   title: "Category Theory for Programmers",
//   authors: ["Bartosz Milewski"],
//   md5: "abc123...",
//   coverUrl: "https://...",
//   filesize: "5.2 MB",
//   extension: "pdf"
// }]
```

### Content Fetching

```javascript
// Fetch download links by MD5 hash
const content = await ArchiveOfAnna.fetch_by_md5("abc123...");

// Returns detailed metadata + download links
// {
//   title: "...",
//   downloadLinks: {
//     libgenRsFork: "https://...",
//     ipfs: "ipfs://...",
//     tor: "http://..."
//   }
// }
```

## Babashka Integration

```clojure
#!/usr/bin/env bb
;; anna-search.bb - Search Anna's Archive

(require '[babashka.http-client :as http]
         '[cheshire.core :as json])

(def anna-self (System/getenv "ANNA_SELF"))

(defn anna-search [query & {:keys [lang ext limit] 
                            :or {lang "en" ext "pdf" limit 10}}]
  (let [base-url "https://annas-archive.org/search"
        params {:q query :lang lang :ext ext}]
    ;; Note: Anna's Archive doesn't have official API
    ;; This would scrape or use unofficial wrapper
    (println (format "Searching Anna's Archive: %s" query))
    {:query query :params params}))

(defn fetch-by-md5 [md5]
  (let [url (format "https://annas-archive.org/md5/%s" md5)]
    (println (format "Fetching: %s" url))
    {:md5 md5 :url url}))

;; GF(3) balanced search: 3 queries in parallel
(defn triadic-search [queries]
  (let [results (pmap anna-search queries)
        trits (cycle [-1 0 1])]
    {:searches (map #(assoc %1 :trit %2) results trits)
     :gf3-sum (reduce + (take (count queries) trits))}))

(when (= *file* (System/getProperty "babashka.file"))
  (let [query (or (first *command-line-args*) "category theory")]
    (println (anna-search query))))
```

## Python Integration

```python
#!/usr/bin/env python3
"""anna_archive.py - Anna's Archive Python client"""

import os
import httpx
from bs4 import BeautifulSoup
from dataclasses import dataclass
from typing import List, Optional

ANNA_SELF = os.getenv("ANNA_SELF")
BASE_URL = "https://annas-archive.org"

@dataclass
class SearchResult:
    title: str
    authors: List[str]
    md5: str
    extension: str
    filesize: str
    trit: int = 0  # GF(3) assignment

def search(
    query: str,
    lang: str = "en",
    ext: str = "pdf",
    content: str = "book_nonfiction"
) -> List[SearchResult]:
    """Search Anna's Archive."""
    url = f"{BASE_URL}/search"
    params = {
        "q": query,
        "lang": lang,
        "ext": ext,
        "content": content
    }
    
    # Note: Would need to parse HTML response
    # or use unofficial API wrapper
    print(f"Searching: {query}")
    return []

def fetch_download_links(md5: str) -> dict:
    """Get download links for a document by MD5."""
    url = f"{BASE_URL}/md5/{md5}"
    # Parse page for download links
    return {
        "md5": md5,
        "url": url,
        "sources": ["libgen", "ipfs", "tor"]
    }

# GF(3) balanced batch search
def triadic_batch(queries: List[str]) -> dict:
    """Search 3 queries with GF(3) conservation."""
    trits = [-1, 0, 1]
    results = []
    for i, q in enumerate(queries[:3]):
        result = search(q)
        for r in result:
            r.trit = trits[i % 3]
        results.extend(result)
    
    trit_sum = sum(trits[:len(queries)])
    return {
        "results": results,
        "gf3_sum": trit_sum,
        "balanced": trit_sum % 3 == 0
    }
```

## Ruby Integration

```ruby
# anna_archive.rb - Ruby client for Anna's Archive
require 'httpx'
require 'nokogiri'

module AnnaArchive
  ANNA_SELF = ENV['ANNA_SELF']
  BASE_URL = 'https://annas-archive.org'
  
  class << self
    def search(query, lang: 'en', ext: 'pdf', content: 'book_nonfiction')
      url = "#{BASE_URL}/search"
      params = { q: query, lang: lang, ext: ext, content: content }
      
      # Would parse HTML response
      puts "Searching Anna's Archive: #{query}"
      []
    end
    
    def fetch_by_md5(md5)
      url = "#{BASE_URL}/md5/#{md5}"
      { md5: md5, url: url }
    end
    
    # GF(3) triadic search
    def triadic_search(queries)
      trits = [-1, 0, 1].cycle
      results = queries.take(3).map.with_index do |q, i|
        { query: q, trit: trits.next, results: search(q) }
      end
      
      sum = results.sum { |r| r[:trit] }
      { results: results, gf3_sum: sum, balanced: sum % 3 == 0 }
    end
  end
end
```

## Integration with academic-research Skill

```clojure
;; Combine with academic-research for comprehensive search
(defn comprehensive-search [query]
  (let [;; Academic sources (via academic-research skill)
        arxiv-results (arxiv-search query)
        semantic-results (semantic-scholar-search query)
        
        ;; Shadow libraries (via anna-archive skill)
        anna-results (anna-search query)
        
        ;; Triadic assignment
        all-results [{:source :arxiv :trit -1 :results arxiv-results}
                     {:source :semantic-scholar :trit 0 :results semantic-results}
                     {:source :anna-archive :trit 1 :results anna-results}]]
    {:triadic all-results
     :gf3-sum (reduce + (map :trit all-results))
     :total-count (reduce + (map #(count (:results %)) all-results))}))
```

## DuckDB Caching

```sql
-- Cache search results in DuckDB
CREATE TABLE IF NOT EXISTS anna_cache (
    md5 VARCHAR PRIMARY KEY,
    title VARCHAR,
    authors VARCHAR[],
    extension VARCHAR,
    filesize VARCHAR,
    download_links JSON,
    trit TINYINT,
    cached_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
);

-- Insert cached result
INSERT INTO anna_cache (md5, title, authors, extension, trit)
VALUES ('abc123', 'Category Theory', ARRAY['Mac Lane'], 'pdf', 0);

-- Query with GF(3) balance
SELECT trit, COUNT(*) as count
FROM anna_cache
GROUP BY trit
ORDER BY trit;
```

## CLI Usage

```bash
# Search for books
bb anna-search.bb "category theory"

# Search with filters
bb anna-search.bb "homotopy type theory" --lang en --ext pdf

# Fetch by MD5
bb anna-fetch.bb abc123def456

# Triadic batch search (3 queries, GF(3) balanced)
bb anna-triadic.bb "category theory" "type theory" "topos theory"
```

## Content Types

| Content Type | Description | Trit |
|--------------|-------------|------|
| `book_nonfiction` | Academic books | 0 |
| `book_fiction` | Fiction books | +1 |
| `journal_article` | Papers/articles | -1 |
| `magazine` | Magazines | 0 |
| `comic` | Comics | +1 |
| `standards` | Standards docs | -1 |

## GF(3) Triads

```
academic-research (-1) ⊗ anna-archive (0) ⊗ depth-search (+1) = 0 ✓
mathpix-ocr (-1) ⊗ anna-archive (0) ⊗ pdf (+1) = 0 ✓
sheaf-cohomology (-1) ⊗ anna-archive (0) ⊗ topos-generate (+1) = 0 ✓
```

## Legal Notice

Anna's Archive indexes content from various sources. Users are responsible for complying with copyright laws in their jurisdiction. This skill is for research and educational purposes.

## References

- [Anna's Archive](https://annas-archive.org) - Main site
- [archive_of_anna](https://github.com/shetty-tejas/archive_of_anna) - Unofficial JS API
- [annas_archive_api](https://pub.dev/packages/annas_archive_api) - Dart/Flutter package
- academic-research skill - Complementary academic search
