---
name: playwright
description: Browser automation via Playwright MCP. Use for web scraping, taking screenshots, interacting with web pages, testing web UIs, and automating browser tasks. Headless browser support.
compatibility: Requires npx and @anthropic-ai/mcp-server-playwright package.
---

# Playwright Browser Automation

Control browsers via Playwright MCP server.

## When to Use

- Web scraping and data extraction
- Taking screenshots of web pages
- Interacting with web UIs (clicking, typing, navigating)
- Testing web applications
- Automating browser-based workflows
- Filling forms and submitting data

## Setup

MCP server configured in `~/.mcp.json`:
```json
{
  "playwright": {
    "command": "npx",
    "args": ["-y", "@anthropic-ai/mcp-server-playwright"]
  }
}
```

## Common Tools

### Navigation
- `navigate_page` - Go to a URL
- `new_page` - Open new browser tab
- `list_pages` - Show open pages

### Interaction
- `click` - Click elements
- `fill` - Type into input fields
- `select` - Choose from dropdowns
- `press` - Press keyboard keys

### Capture
- `take_screenshot` - Screenshot current page
- `get_page_content` - Get page HTML
- `get_text` - Extract visible text

### Evaluation
- `evaluate` - Run JavaScript in page context

## Example Workflows

### Screenshot a Page
1. `navigate_page(url="https://example.com")`
2. `take_screenshot()`

### Fill a Form
1. `navigate_page(url="https://example.com/form")`
2. `fill(selector="#email", value="user@example.com")`
3. `fill(selector="#password", value="secret")`
4. `click(selector="button[type=submit]")`

### Extract Data
1. `navigate_page(url="https://example.com/data")`
2. `get_text(selector=".results")`

## Tips

- Use CSS selectors or XPath for element targeting
- Wait for page loads before interacting
- Browser runs headless by default
- Screenshots are useful for debugging
