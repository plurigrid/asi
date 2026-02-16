---
name: terminal-css
description: "Provides Textual TCSS patterns for terminal widgets and ACP content styling. Use when building terminal UIs with color-first design, styling Agent Client Protocol output, or integrating Dracula-themed terminal rendering."
allowed-tools:
  - Read
  - Grep
  - glob
---

# Terminal CSS Skill

Foundation patterns for Textual terminal styling from the toad codebase.

## When to Use

- Building Textual terminal widgets with proper TCSS styling
- Styling Agent Client Protocol (ACP) tool output (text, diffs, terminals)
- Implementing Dracula color theme for terminal ANSI rendering
- Creating conversation UIs with agent responses, thoughts, and tool calls
- Designing state-based styling (success/error/loading/finalized)

## When NOT to Use

- General CSS/HTML web styling (this is Textual-specific TCSS)
- Non-terminal Textual widgets (use standard Textual docs)
- Building ACP protocol handlers (use `acp/protocol.py` directly)
- Backend terminal emulation logic (see `ansi.py`, `TerminalState`)

## Overview

This skill extracts terminal and ACP content styling patterns from the `toad` codebase (batrachianai/toad) for use in building color-first Textual applications.

## Core Terminal Widget Hierarchy

```
Terminal (base)
├── TerminalTool (ACP tool execution)
├── ShellTerminal (interactive shell)
└── CommandPane (command output)
```

## TCSS Foundation Patterns

### Terminal Base Styling

```tcss
/* From toad.tcss - Terminal within Conversation */
Terminal {
    width: 1fr;
    height: auto;
    padding: 0 1 0 0;
    margin: 1 0;
    overflow: scroll;
    scrollbar-size: 0 0;
}

/* TerminalTool - ACP tool execution terminals */
TerminalTool {
    height: auto;
    border: panel $text-secondary 90%;
    padding: 1 1 0 1;

    &.-success {
        border: panel $text-success 90%;
    }
    &.-error {
        border: panel $error-muted;
        border-title-color: $text-error;
        border-subtitle-align: right;
        border-subtitle-style: bold;
    }
    &.-finalized {
        /* Added when terminal is finalized (no more writes) */
    }
}
```

### ACP Content Styling

```tcss
/* ACPToolCallContent - renders ToolCallContent from ACP */
ACPToolCallContent {
    Markdown {
        margin: 0;
        padding-left: 0;
        MarkdownBlock:last-of-type {
            margin-bottom: 0;
        }
    }
}

/* ToolCall widget styling */
ToolCall {
    padding: 0 0 0 1;
    width: 1fr;
    layout: stream;
    height: auto;

    .icon {
        width: auto;
        margin-right: 1;
    }
    #tool-content {
        display: none;
    }
    &.-has-content #tool-content {
        margin-top: 1;
    }
    &.-expanded {
        #tool-content {
            display: block;
        }
    }
}
```

### Color Variables (Semantic)

```tcss
/* Toad uses Textual's design system variables */
$text-primary       /* Primary text color */
$text-secondary     /* Secondary/muted text */
$text-success       /* Success state (green) */
$text-error         /* Error state (red) */
$text-accent        /* Accent color for highlights */
$text-muted         /* Highly muted text */

$primary            /* Primary UI color */
$secondary          /* Secondary UI color */
$error              /* Error color */
$error-muted        /* Muted error */
$warning            /* Warning color */
$accent             /* Accent color */

$background         /* Background color */
$foreground         /* Foreground color */
```

### Dracula Terminal Theme

```python
# From app.py - ANSI color palette for terminal rendering
DRACULA_TERMINAL_THEME = terminal_theme.TerminalTheme(
    background=(40, 42, 54),      # #282A36
    foreground=(248, 248, 242),   # #F8F8F2
    normal=[
        (33, 34, 44),             # black - #21222C
        (255, 85, 85),            # red - #FF5555
        (80, 250, 123),           # green - #50FA7B
        (241, 250, 140),          # yellow - #F1FA8C
        (189, 147, 249),          # blue - #BD93F9
        (255, 121, 198),          # magenta - #FF79C6
        (139, 233, 253),          # cyan - #8BE9FD
        (248, 248, 242),          # white - #F8F8F2
    ],
    bright=[
        (98, 114, 164),           # bright black - #6272A4
        (255, 110, 110),          # bright red - #FF6E6E
        (105, 255, 148),          # bright green - #69FF94
        (255, 255, 165),          # bright yellow - #FFFFA5
        (214, 172, 255),          # bright blue - #D6ACFF
        (255, 146, 223),          # bright magenta - #FF92DF
        (164, 255, 255),          # bright cyan - #A4FFFF
        (255, 255, 255),          # bright white - #FFFFFF
    ],
)
```

## ACP Protocol Content Types

From `protocol.py`, the content types that need styling:

```python
# ToolCallContent variants
type ToolCallContent = (
    ToolCallContentContent   # type: "content" - text/markdown
    | ToolCallContentDiff    # type: "diff" - file diffs
    | ToolCallContentTerminal  # type: "terminal" - terminal embed
)

# ContentBlock variants (for messages)
type ContentBlock = (
    TextContent              # text
    | ImageContent           # image
    | AudioContent           # audio
    | EmbeddedResourceContent  # embedded resource
    | ResourceLinkContent    # resource link
)

# ToolKind for styling based on operation type
type ToolKind = Literal[
    "read",      # File read operations
    "edit",      # File edit operations
    "delete",    # File delete operations
    "move",      # File move operations
    "search",    # Search operations
    "execute",   # Command execution
    "think",     # Thinking/reasoning
    "fetch",     # Network fetch
    "switch_mode",  # Mode switching
    "other",     # Other operations
]

# ToolCallStatus for state styling
type ToolCallStatus = Literal[
    "pending",      # Waiting to start
    "in_progress",  # Currently running
    "completed",    # Successfully finished
    "failed",       # Failed
]
```

## Widget Composition Pattern

```python
# From acp_content.py - rendering ToolCallContent
class ACPToolCallContent(containers.VerticalGroup):
    def compose(self) -> ComposeResult:
        for content in self._content:
            match content:
                case {"type": "content", "content": {"type": "text", "text": text}}:
                    yield widgets.Markdown(text)
                case {"type": "diff", "oldText": old, "newText": new, "path": path}:
                    yield DiffView(path, path, old or "", new)
                case {"type": "terminal", "terminalId": terminal_id}:
                    # Terminal widget is mounted separately
                    pass
```

## Diff View Styling

```tcss
/* DiffView for file diffs in tool output */
DiffView {
    .diff-group {
        margin-bottom: 0;
    }
}

/* Line annotations */
/* + = addition (green) */
/* - = deletion (red) */
/* / = modification */
/* (space) = context */
```

## State Classes

```tcss
/* Terminal state classes */
.-finalized    /* Terminal no longer accepts input */
.-success      /* Command completed successfully (exit 0) */
.-error        /* Command failed (non-zero exit) */
.-busy         /* Terminal is busy/processing */

/* Content visibility */
.-hidden       /* Hidden element */
.-expanded     /* Expanded content */
.-has-content  /* Has content to show */

/* Agent states */
.-loading      /* Loading state */
.-maximized    /* Maximized view */
```

## Conversation Context Styling

```tcss
Conversation {
    AgentResponse {
        min-height: 1;
        padding: 0 1 0 0;
        overflow-x: auto;
        scrollbar-size-horizontal: 0;
        layout: stream;
    }

    AgentThought {
        background: $primary-muted 20%;
        color: $text-primary;
        min-height: 1;
        margin: 1 1 1 0;
        padding: 0 1 0 1;
        border: blank transparent;
        max-height: 10;
        overflow-y: auto;
        scrollbar-visibility: hidden;

        &.-loading {
            background: transparent !important;
            padding: 0;
            margin: 0;
        }
        &.-maximized {
            max-height: 100h;
            scrollbar-visibility: visible;
        }
        &:focus {
            border: tall $primary;
        }
    }

    UserInput {
        border-left: blank $secondary;
        background: $secondary 15%;
        padding: 1 1 1 0;
        margin: 1 1 1 0;
    }

    ShellResult {
        border-left: blank $primary;
        background: $foreground 4%;
        padding: 1 0;
        margin: 1 1 1 0;
        #prompt {
            margin: 0 1 0 0;
            color: $text-primary;
        }
    }
}
```

## Border Patterns

```tcss
/* Textual border types used in toad */
border: panel $color           /* Panel-style border */
border: tall $color            /* Tall border */
border: round $color           /* Rounded border */
border: heavy $color           /* Heavy border */
border: wide $color            /* Wide border */
border: blank $color           /* Invisible but space-taking */
border: solid $color           /* Solid border */
border: outer $color           /* Outer border (for cursor) */

/* Border modifiers */
border: panel $text-secondary 90%;   /* With opacity */
border: wide $error 50%;             /* Semi-transparent */
```

## Usage

When building ACP UIs with color-first design:

1. Use semantic color variables (`$text-primary`, `$text-success`, etc.)
2. Apply state classes for dynamic styling (`.-success`, `.-error`)
3. Match ToolKind to appropriate visual treatment
4. Use the Dracula theme as base terminal palette
5. Layer content types appropriately (text → diff → terminal)

## Related Skills

| Skill | Trit | Relationship |
|-------|------|--------------|
| `terminal` | 0 | Core terminal emulation (libghostty-vt, tmux, zsh) |
| `libghostty-embed` | +1 | Per-vat terminal embedding with Goblins |
| `libghostty-streaming` | +1 | Terminal streaming protocols |
| `gay-mcp` | +1 | Deterministic color generation (SplitMix64) |
| `colored-vertex-model` | 0 | Color projection properties |
| `glamorous-gay` | +1 | Gay.jl + Glamorous Toolkit integration |
| `crdt-vterm` | 0 | Collaborative terminal sessions via CRDT |

### Skill Composition

```
terminal-css (+1) ⊗ terminal (0) ⊗ libghostty-embed (-1) = 0 ✓
terminal-css (+1) ⊗ gay-mcp (+1) ⊗ crdt-vterm (-2 mod 3) = 0 ✓
```

Use `gay-mcp` for deterministic color generation, `terminal` for VT sequence handling, and `terminal-css` for TCSS styling patterns.

## Related Files

- `toad/src/toad/toad.tcss` - Main stylesheet
- `toad/src/toad/widgets/terminal.py` - Base Terminal widget
- `toad/src/toad/widgets/terminal_tool.py` - TerminalTool for ACP
- `toad/src/toad/widgets/acp_content.py` - ACP content renderer
- `toad/src/toad/acp/protocol.py` - ACP type definitions
- `toad/src/toad/app.py` - Dracula theme definition
