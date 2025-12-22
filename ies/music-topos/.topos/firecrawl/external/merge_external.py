#!/usr/bin/env python3
import json
from pathlib import Path
from urllib.parse import urlparse, urlunparse

def normalize(url: str) -> str:
    url = url.strip()
    if url.endswith('/') and '://' in url and not url.endswith('://'):
        # Keep trailing slash only if there is a query or fragment
        if '?' not in url and '#' not in url:
            url = url[:-1]
    return url

def ascii_clean(value: str) -> str:
    return value.encode('ascii', 'ignore').decode('ascii')

def candidate_urls(orig_url: str) -> list:
    urls = []
    norm = normalize(orig_url)
    urls.append(norm)

    parsed = urlparse(orig_url)
    if parsed.fragment:
        nofrag = parsed._replace(fragment='')
        urls.append(normalize(urlunparse(nofrag)))

    if parsed.netloc == 'spinframework.dev':
        path = parsed.path or '/'
        if not path.startswith('/v3/'):
            v3_path = '/v3' + (path if path.startswith('/') else '/' + path)
            v3 = parsed._replace(path=v3_path)
            urls.append(normalize(urlunparse(v3)))
            if parsed.fragment:
                v3_nofrag = v3._replace(fragment='')
                urls.append(normalize(urlunparse(v3_nofrag)))

    # de-dup while preserving order
    deduped = []
    seen = set()
    for u in urls:
        if u not in seen:
            seen.add(u)
            deduped.append(u)
    return deduped

def fragment_candidates(base_url: str, results_map: dict) -> list:
    base = normalize(base_url)
    matches = []
    for key, items in results_map.items():
        if key.startswith(base + '#'):
            matches.extend(items)
    return matches

base = Path(__file__).resolve().parent
seed_all = base.parent / 'external_seed_urls.txt'
seed_filtered = base.parent / 'external_seed_urls.filtered.txt'
raw_dir = base / 'raw'
index_json = base / 'index.json'
index_md = base / 'index.md'

requested = []
if seed_filtered.exists():
    requested = [line.strip() for line in seed_filtered.read_text().splitlines() if line.strip()]

requested_norm = [normalize(u) for u in requested]

results_map = {}
for raw_file in sorted(raw_dir.glob('*.json')):
    data = json.loads(raw_file.read_text())
    for item in data.get('results', []):
        url = item.get('url', '')
        norm = normalize(url)
        results_map.setdefault(norm, []).append(item)

items = []
found = 0
empty = 0
missing = 0

def has_content(item: dict) -> bool:
    return bool((item.get('title') or '').strip() or (item.get('summary') or '').strip())

for orig_url, norm_url in zip(requested, requested_norm):
    candidates = results_map.get(norm_url, [])
    if not any(has_content(c) for c in candidates):
        for alt in candidate_urls(orig_url):
            if alt == norm_url:
                continue
            alt_candidates = results_map.get(alt, [])
            if not any(has_content(c) for c in alt_candidates):
                parsed_alt = urlparse(alt)
                if parsed_alt.netloc == 'spinframework.dev':
                    frag = fragment_candidates(alt, results_map)
                    if any(has_content(c) for c in frag):
                        alt_candidates = frag
            if any(has_content(c) for c in alt_candidates):
                candidates = alt_candidates
                break
            if not candidates and alt_candidates:
                candidates = alt_candidates
    chosen = None
    for c in candidates:
        title = (c.get('title') or '').strip()
        summary = (c.get('summary') or '').strip()
        if title or summary:
            chosen = c
            break
    if chosen is None and candidates:
        chosen = candidates[0]

    if chosen is None:
        status = 'missing'
        title = ''
        summary = ''
        topics = []
        missing += 1
    else:
        title = (chosen.get('title') or '').strip()
        summary = (chosen.get('summary') or '').strip()
        topics = chosen.get('topics') or []
        if title or summary:
            status = 'ok'
            found += 1
        else:
            status = 'empty'
            empty += 1

    items.append({
        'url': ascii_clean(orig_url),
        'title': ascii_clean(title),
        'summary': ascii_clean(summary),
        'topics': [ascii_clean(t) for t in topics if isinstance(t, str)],
        'status': status,
    })

from datetime import datetime, timezone

index = {
    'generated_at': datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),
    'seed_all': str(seed_all),
    'seed_filtered': str(seed_filtered),
    'requested_count': len(requested),
    'found_count': found,
    'empty_count': empty,
    'missing_count': missing,
    'timeouts': [],
    'items': items,
}

index_json.write_text(json.dumps(index, indent=2) + '\n')

# Markdown index
lines = [
    '# Firecrawl Index (External URLs)',
    '',
    f'Requested: {len(requested)} | Found: {found} | Empty: {empty} | Missing: {missing}',
    '',
    '| Status | URL | Title | Summary |',
    '| --- | --- | --- | --- |',
]
for item in items:
    lines.append(f"| {item['status']} | {item['url']} | {item['title']} | {item['summary']} |")

index_md.write_text('\n'.join(lines) + '\n')
print(f'Wrote {index_json}')
print(f'Wrote {index_md}')
