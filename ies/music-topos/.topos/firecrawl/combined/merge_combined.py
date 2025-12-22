#!/usr/bin/env python3
import json
from pathlib import Path
from datetime import datetime, timezone

def ascii_clean(value: str) -> str:
    return value.encode('ascii', 'ignore').decode('ascii')

base = Path(__file__).resolve().parent
root = base.parent

github_index = root / 'github' / 'index.json'
external_index = root / 'external' / 'index.json'

if not github_index.exists() or not external_index.exists():
    raise SystemExit('Missing github or external index.json')

github = json.loads(github_index.read_text())
external = json.loads(external_index.read_text())

items = []
for item in github.get('items', []):
    items.append({
        'source': 'github',
        'url': ascii_clean(item.get('url', '')),
        'title': ascii_clean(item.get('title', '')),
        'summary': ascii_clean(item.get('summary', '')),
        'topics': [ascii_clean(t) for t in (item.get('topics') or []) if isinstance(t, str)],
        'repo': ascii_clean(item.get('repo', '')),
        'status': item.get('status', '') or 'ok',
    })

for item in external.get('items', []):
    items.append({
        'source': 'external',
        'url': ascii_clean(item.get('url', '')),
        'title': ascii_clean(item.get('title', '')),
        'summary': ascii_clean(item.get('summary', '')),
        'topics': [ascii_clean(t) for t in (item.get('topics') or []) if isinstance(t, str)],
        'repo': '',
        'status': item.get('status', '') or 'ok',
    })

index = {
    'generated_at': datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),
    'github_index': str(github_index),
    'external_index': str(external_index),
    'count': len(items),
    'items': items,
}

out_json = base / 'index.json'
out_md = base / 'index.md'

out_json.write_text(json.dumps(index, indent=2) + '\n')

lines = [
    '# Firecrawl Index (Combined)',
    '',
    f'Total items: {len(items)}',
    '',
    '| Source | Status | URL | Title | Summary |',
    '| --- | --- | --- | --- | --- |',
]
for item in items:
    lines.append(f"| {item['source']} | {item['status']} | {item['url']} | {item['title']} | {item['summary']} |")

out_md.write_text('\n'.join(lines) + '\n')

print(f'Wrote {out_json}')
print(f'Wrote {out_md}')
