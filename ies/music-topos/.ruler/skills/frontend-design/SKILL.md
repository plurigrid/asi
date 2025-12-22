# frontend-design - AI-Guided UI/UX Design Skill

## Overview

Frontend design skill for all AI coding assistants. Provides consistent design principles, component patterns, and accessibility guidelines across Claude, Codex, Cursor, and Copilot.

## Installation

```bash
# Via ai-agent-skills (Codex)
npx ai-agent-skills install frontend-design --agent codex

# Via ruler (all agents)
ruler sync --skill frontend-design
```

## Design Principles

### 1. Color via Gay.jl SPI

All colors are deterministic via SplitMix64:

```javascript
// seed 0x42D (1069) for consistent palette
const seed = 0x42D;
const colors = gaySPI.palette(seed, 5);

// Example palette:
// #E67F86 - Primary (warm coral)
// #D06546 - Secondary (rust orange)
// #1316BB - Accent (deep blue)
// #3CB371 - Success (medium sea green)
// #FFD700 - Warning (gold)
```

### 2. Component Patterns

```tsx
// Balanced Ternary State Component
interface TAPState {
  mode: 'BACKFILL' | 'VERIFY' | 'LIVE';
  color: string;
}

function StateIndicator({ state }: { state: TAPState }) {
  const colorMap = {
    BACKFILL: '#0000FF',  // Blue (-1)
    VERIFY: '#00FF00',    // Green (0)
    LIVE: '#FF0000'       // Red (+1)
  };

  return (
    <div
      className="state-indicator"
      style={{ backgroundColor: colorMap[state.mode] }}
    />
  );
}
```

### 3. Accessibility (WCAG 2.1 AA)

- Contrast ratio ≥ 4.5:1 for normal text
- Contrast ratio ≥ 3:1 for large text
- Focus indicators visible
- Keyboard navigation complete
- Screen reader compatible

## Layout Patterns

### Golden Ratio Grid

```css
.container {
  display: grid;
  grid-template-columns: 1fr 1.618fr;  /* φ = 1.618... */
  gap: var(--spacing-golden);
}

:root {
  --spacing-golden: 1.618rem;
  --spacing-inverse: 0.618rem;
}
```

### Fibonacci Spacing

```css
:root {
  --space-1: 0.25rem;   /* 1 */
  --space-2: 0.5rem;    /* 2 */
  --space-3: 0.75rem;   /* 3 */
  --space-5: 1.25rem;   /* 5 */
  --space-8: 2rem;      /* 8 */
  --space-13: 3.25rem;  /* 13 */
  --space-21: 5.25rem;  /* 21 */
}
```

## Animation Principles

### Spectral Gap Timing

```css
:root {
  --duration-fast: 100ms;     /* Instant feedback */
  --duration-normal: 250ms;   /* Standard transitions */
  --duration-slow: 400ms;     /* Complex animations */
  --easing-spectral: cubic-bezier(0.25, 0.1, 0.25, 1);
}

/* 1/4 probability for verification animations */
.verify-transition {
  animation: verify-pulse 1s infinite;
  animation-timing-function: steps(4);  /* 4 discrete steps */
}
```

## MCP Integration

The skill integrates with MCP servers for live design tokens:

```json
{
  "mcpServers": {
    "gay": {
      "command": "julia",
      "args": ["--project=@gay", "-e", "using Gay; Gay.serve_mcp()"],
      "env": { "GAY_SEED": "1069" }
    }
  }
}
```

### Fetching Design Tokens

```javascript
// Use Gay MCP to get deterministic colors
const response = await mcp.call('gay/color_at', {
  seed: 1069,
  index: componentIndex
});

const { L, C, H } = response;  // OKLCH color space
```

## File Structure

```
src/
├── components/
│   ├── Button.tsx
│   ├── Card.tsx
│   └── StateIndicator.tsx
├── styles/
│   ├── tokens.css       # Design tokens
│   ├── components.css   # Component styles
│   └── utilities.css    # Utility classes
└── hooks/
    └── useGayColor.ts   # SPI color hook
```

## TAP-Aware Theming

```typescript
type Theme = {
  mode: 'light' | 'dark';
  tapState: 'BACKFILL' | 'VERIFY' | 'LIVE';
  seed: number;
};

function getThemeColors(theme: Theme) {
  const baseColors = gaySPI.palette(theme.seed, 10);

  return {
    primary: baseColors[0],
    secondary: baseColors[1],
    accent: baseColors[2],
    tapIndicator: TAP_COLORS[theme.tapState],
    background: theme.mode === 'dark' ? '#1a1a2e' : '#ffffff',
    text: theme.mode === 'dark' ? '#e0e0e0' : '#1a1a2e'
  };
}
```

## See Also

- `gay-mcp/SKILL.md` - Core color generation
- `codex-self-rewriting/SKILL.md` - Self-modification
- `glass-bead-game/SKILL.md` - Interdisciplinary connections
