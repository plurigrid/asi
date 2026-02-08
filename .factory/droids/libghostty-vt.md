---
name: libghostty-vt
description: 'libghostty-vt'
model: inherit
tools: ["Read", "Edit", "Execute", "WebSearch"]
---

# libghostty-vt

Zero-dependency VT sequence parser from Ghostty. Mitchell Hashimoto's embeddable terminal core.

## Status

**NOT YET RELEASED** (as of 2025-09) - Zig API available for testing, C API coming.

## What It Is

`libghostty-vt` extracts Ghostty's proven VT parsing into a standalone library:
- Parse ANSI/VT sequences
- Maintain terminal state
- Zero dependencies (no libc required!)
- SIMD-optimized (>100 MB/s plain text)

## Architecture

```
Raw Bytes → UTF8Decoder → Parser (DFA) → Stream → Actions
                           │
                     State Machine
                     (14 states)
```

### Parser States

| State | Purpose |
|-------|---------|
| `ground` | Normal text printing |
| `escape` | ESC detected (0x1B) |
| `csi_entry` | CSI sequence start |
| `csi_param` | Parsing CSI parameters |
| `osc_string` | OSC data collection |
| `dcs_passthrough` | DCS data collection |

### Action Types

```zig
const Action = union(enum) {
    print: u21,              // Unicode codepoint
    execute: u8,             // C0/C1 control
    csi_dispatch: CSI,       // Control Sequence Introducer
    esc_dispatch: ESC,       // Escape sequence
    osc_dispatch: *osc.Parser,
    dcs_hook: DCS,
    dcs_put: u8,
    dcs_unhook: void,
};
```

## Key Files (ghostty-org/ghostty)

```
src/terminal/Parser.zig      # State machine
src/terminal/stream.zig      # Stream wrapper + SIMD
src/terminal/osc.zig         # OSC parser
src/terminal/parse_table.zig # Compile-time transition table
src/simd/vt.zig              # SIMD acceleration
```

## Performance

| Optimization | Impact |
|--------------|--------|
| Pre-computed state table | O(1) transitions |
| SIMD text processing | 10-100x for plain text |
| Fast-path CSI parsing | Skips state machine |
| Fixed-size buffers | No allocation |

## Use Cases

- Terminal emulators (tmux, zellij, Ghostty)
- IDE terminals (VS Code, JetBrains)
- Cloud terminals (Vercel, Render)
- TUI frameworks
- Terminal recording/playback

## Whe