---
name: playwright-unworld
description: "Playwright-Unworld Skill: Deterministic Web Automation"
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Playwright-Unworld Skill: Deterministic Web Automation

**Status**: 🚀 Production Ready
**Trit**: +1 (PLUS - generative/automation)
**Principle**: Browser state derived from seed chains, not external timing
**Foundation**: Unworld derivation + Playwright API

---

## Overview

**Playwright-Unworld** applies derivational principles to web automation:

```
Genesis Seed → Browser Context Seed → Navigation → Selector Path → Screenshots/PDFs
              ↓                         ↓              ↓
           GF(3) balanced         State-derived    Reproducible
```

No external clocks, no flaky waits, no race conditions. All derived deterministically.

---

## Core Architecture

### 1. Browser Context Derivation

```julia
# Each browser context derives from seed
function derive_browser_context(genesis_seed::UInt64, index::Int)
    # Derive unique context seed
    context_seed = chain_seed(genesis_seed, index)

    # Context properties derived from seed
    viewport_width = 800 + (context_seed % 800)
    viewport_height = 600 + (context_seed % 600)
    timezone = select_timezone(context_seed)
    locale = select_locale(context_seed)

    BrowserContext(
        viewport = (viewport_width, viewport_height),
        timezone = timezone,
        locale = locale,
        seed = context_seed
    )
end
```

**Key Property**: Same seed → same context every time (reproducible)

### 2. Selector Chain Derivation

Instead of fragile CSS/XPath strings, derive selectors from seeds:

```julia
@present SchSelectorChain(FreeSchema) begin
    Selector::Ob
    Component::Ob
    Role::Ob

    component_of::Hom(Selector, Component)
    role_of::Hom(Selector, Role)
    css_path::Attr(Selector, String)
    robustness::Attr(Selector, Float64)  # 0-1 confidence
end

@acset_type SelectorChain(SchSelectorChain, index=[:component_of])

# Derive selector from seed + page structure
function derive_selector(seed::UInt64, page_structure::ACSet)
    candidates = enumerate_selectors(page_structure)

   