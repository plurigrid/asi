---
name: amazon-shopping-mcp
description: Amazon product search, cart management, price tracking, and shopping list via Playwright + DuckDB MCP server
---

# Amazon Shopping MCP

Headless Chromium browser automation for Amazon.com with local DuckDB product cache and shopping list.

## Server Location

```
/Users/alice/v/mcp/amazon-shopping/
```

## MCP Registration

```json
{
  "amazon-shopping": {
    "type": "stdio",
    "command": "/bin/sh",
    "args": ["-c", "cd /Users/alice/v/mcp/amazon-shopping && unset PYTHONPATH && exec uv run python -m amazon_shopping_mcp.server"]
  }
}
```

## Stack

- **FastMCP 2.14.x** — MCP server framework (pinned `<3`)
- **Playwright** — headless Chromium for Amazon browsing
- **DuckDB** — product cache, price history, shopping list at `~/v/amazon-shopping.duckdb`
- **Python 3.14** via uv

## Tools (12)

### Browser / Amazon

| Tool | Args | Description |
|------|------|-------------|
| `search_amazon` | `query`, `max_results=5` | Search Amazon, returns ASIN/title/price/rating |
| `get_product_details` | `asin` | Full product page: features, description, availability |
| `add_to_cart` | `asin` | Click Add to Cart (headless session, not logged in by default) |
| `view_cart` | — | List cart items + subtotal |
| `screenshot_page` | — | Screenshot to `/tmp/amazon_screenshot.png` |
| `navigate_url` | `url` | Go to any URL, return title + 2000 char text preview |

### Shopping List (DuckDB)

| Tool | Args | Description |
|------|------|-------------|
| `list_add` | `asin`, `title`, `qty=1`, `notes=""` | Add to local list |
| `list_view` | — | Show all items with status |
| `list_update_status` | `item_id`, `status` | Set `TODO`/`BUY`/`BOUGHT`/`SKIP` |
| `list_remove` | `item_id` | Delete from list |

### Price Tracking

| Tool | Args | Description |
|------|------|-------------|
| `price_history` | `asin` | All observed prices over time |
| `cached_products` | `query=""` | Search local product cache (empty = all) |

## DuckDB Schema

```sql
products (asin PK, title, price_cents, currency, rating, review_count, url, category, image_url, last_seen)
price_history (asin, price_cents, currency, observed_at)
shopping_list (id PK, asin, title, qty, notes, status, added_at)
```

Every `search_amazon` and `get_product_details` call auto-caches to `products` and appends to `price_history`.

## Env Vars

| Var | Default | Description |
|-----|---------|-------------|
| `AMAZON_SHOPPING_DB` | `~/v/amazon-shopping.duckdb` | DuckDB path |

## Workflow Examples

### Research + buy list
1. `search_amazon("thunderbolt 4 cable 2m")` — get top 5 results
2. `get_product_details("B0CXRSWRBR")` — read features, check availability
3. `list_add("B0CXRSWRBR", "Cable Matters TB4 2m", qty=2)` — track locally
4. `price_history("B0CXRSWRBR")` — check price trend over time

### Cart operations
1. `add_to_cart("B0CXRSWRBR")` — add to Amazon cart
2. `view_cart()` — check cart subtotal
3. `screenshot_page()` — visual verification

### Offline queries
- `cached_products("thunderbolt")` — search previously seen products
- `list_view()` — review full shopping list
- `price_history("B0CDH4FGZY")` — price trend for Anker TB4

## Limitations

- **Not logged in** by default — cart is anonymous session. Login requires manual cookie injection or interactive auth.
- **Amazon anti-bot** — headless Chrome may hit CAPTCHAs on heavy use. Use `screenshot_page` to debug.
- **Prices in cents** — stored as integers (2999 = $29.99) to avoid float rounding.
- **Single browser context** — tools share one Chromium page. Concurrent calls may race.

## Development

```bash
cd /Users/alice/v/mcp/amazon-shopping
unset PYTHONPATH
uv sync                              # install deps
uv run playwright install chromium   # install browser (once)
uv run python -m amazon_shopping_mcp.server  # run server
```

## Companion Artifact

Shopping list org file: `~/v/amazon-shopping.org` — manually curated product research with ASINs, prices, and notes.
