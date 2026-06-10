---
name: libghostty-aci
description: 'Integrates libghostty terminal emulation with Agent-Computer Interface (ACI) patterns:'
---
# libghostty-aci: Terminal ACI Integration

**Trit**: 0 (ERGODIC - transport layer)
**Color**: #46F27F (Coordinator stream)
**Seed**: 1069

---

## Overview

Integrates libghostty terminal emulation with Agent-Computer Interface (ACI) patterns:

| Integration | Trit | Color | Library |
|-------------|------|-------|---------|
| Emacs vterm/eat | -1 | #E7B367 | libghostty-vt |
| MCP Terminal | 0 | #46F27F | libghostty embedding |
| Daphne ASGI | +1 | #F0D127 | WebSocket streaming |

GF(3): -1 + 0 + 1 = 0 ✓

---

## libghostty Type Mapping

### Core Types (from lib_vt.zig)

```zig
// Terminal state machine
pub const Terminal = terminal.Terminal;
pub const Screen = terminal.Screen;
pub const Parser = terminal.Parser;

// Display elements
pub const Cell = page.Cell;
pub const Style = terminal.Style;
pub const Cursor = Screen.Cursor;

// Input handling
pub const input = struct {
    pub const Key = key.Key;
    pub const KeyEvent = key.KeyEvent;
    pub const KeyMods = key.Mods;
    pub const encodeKey = key_encode.encode;
    pub const encodePaste = paste.encode;
};

// Escape sequences
pub const CSI = Parser.Action.CSI;
pub const DCS = Parser.Action.DCS;
pub const osc = terminal.osc;
```

### Embedding Types (from embedded.zig)

```zig
// Application lifecycle
pub const App.Options = extern struct {
    wakeup_callback: *const fn (*anyopaque) callconv(.C) void,
    action_callback: *const fn (*anyopaque, Action) callconv(.C) bool,
    clipboard_read: *const fn (*anyopaque, Clipboard) callconv(.C) void,
    clipboard_write: *const fn (Clipboard, [*:0]const u8, usize) callconv(.C) void,
    clipboard_write_small: *const fn (Clipboard, [*]const u8, usize) callconv(.C) void,
};

// Surface management
pub const Surface = struct {
    pub fn setSize(self: *Surface, width: usize, height: usize) void;
    pub fn handleInput(self: *Surface, event: KeyEvent) void;
    pub fn render(self: *Surface) RenderState;
};
```

---

## Emacs Integration (-1 MINUS)

### vterm Backend

```elisp
;; Use libghostty-vt for VT parsing instead of libvterm
(defcustom vterm-backend 'ghostty
  "Terminal emulation backend: 'libvterm or 'ghostty"
  :type '(choice (const libvterm) (const ghostty)))

(defun ghostty-vt-make-terminal (width height)
  "Create ghostty terminal with dimensions."
  (let ((term (ghostty-vt-new)))
    (ghostty-vt-resize term width height)
    term))

(defun ghostty-vt-process-output (term data)
  "Feed data through ghostty parser."
  (ghostty-vt-feed term data)
  (ghostty-vt-get-screen term))
```

### eat Integration

```elisp
;; eat (Emulate A Terminal) can use ghostty for parsing
(defun eat-ghostty-adapter (process output)
  "Adapt ghostty-vt output to eat display."
  (let ((parsed (ghostty-parse-stream output)))
    (eat-render-cells (ghostty-cells-to-eat parsed))))
```

### Key Encoding

```elisp
;; Use ghostty key encoding for terminal input
(defun ghostty-encode-key (key mods)
  "Encode key event for terminal using ghostty."
  (ghostty-input-encode-key
   (ghostty-make-key-event key mods)))
```

---

## MCP Terminal Server (0 ERGODIC)

### Terminal Streaming Protocol

```typescript
// MCP server exposing terminal capabilities
interface GhosttyMCPServer {
  tools: {
    "terminal/create": {
      params: { width: number; height: number; };
      returns: { session_id: string; };
    };
    "terminal/write": {
      params: { session_id: string; data: string; };
      returns: { cells_changed: number; };
    };
    "terminal/read": {
      params: { session_id: string; };
      returns: { screen: Cell[][]; cursor: Position; };
    };
    "terminal/resize": {
      params: { session_id: string; width: number; height: number; };
      returns: { success: boolean; };
    };
    "terminal/input": {
      params: { session_id: string; key: string; mods: string[]; };
      returns: { encoded: string; };
    };
  };
}
```

### Rust MCP Implementation

```rust
use ghostty_vt::{Terminal, Parser, Screen};

struct GhosttyMCP {
    terminals: HashMap<String, Terminal>,
}

impl GhosttyMCP {
    fn create_terminal(&mut self, width: u16, height: u16) -> String {
        let id = Uuid::new_v4().to_string();
        let term = Terminal::new(width, height);
        self.terminals.insert(id.clone(), term);
        id
    }

    fn write(&mut self, id: &str, data: &[u8]) -> usize {
        let term = self.terminals.get_mut(id)?;
        term.process(data);
        term.screen().damage_count()
    }

    fn read(&self, id: &str) -> Screen {
        self.terminals.get(id)?.screen().clone()
    }
}
```

### WebSocket Streaming

```rust
async fn terminal_websocket(ws: WebSocket, term_id: String) {
    let (mut sink, mut stream) = ws.split();

    // Input handler
    tokio::spawn(async move {
        while let Some(msg) = stream.next().await {
            if let Ok(Message::Binary(data)) = msg {
                term.process(&data);
            }
        }
    });

    // Output streamer (60fps)
    loop {
        let screen = term.screen();
        let json = serde_json::to_string(&screen)?;
        sink.send(Message::Text(json)).await?;
        tokio::time::sleep(Duration::from_millis(16)).await;
    }
}
```

---

## Daphne ASGI Integration (+1 PLUS)

### Django Channels Terminal

```python
# consumers.py
from channels.generic.websocket import AsyncWebsocketConsumer
import ghostty_vt  # Python bindings

class TerminalConsumer(AsyncWebsocketConsumer):
    async def connect(self):
        self.terminal = ghostty_vt.Terminal(80, 24)
        await self.accept()

    async def receive(self, text_data=None, bytes_data=None):
        if bytes_data:
            # Process input through ghostty
            self.terminal.process(bytes_data)

            # Send screen update
            screen = self.terminal.screen_json()
            await self.send(text_data=screen)

    async def disconnect(self, close_code):
        del self.terminal
```

### ASGI Middleware

```python
# middleware.py
class GhosttyTerminalMiddleware:
    """ASGI middleware for terminal WebSocket connections."""

    def __init__(self, app):
        self.app = app

    async def __call__(self, scope, receive, send):
        if scope["type"] == "websocket" and scope["path"].startswith("/terminal/"):
            await self.handle_terminal(scope, receive, send)
        else:
            await self.app(scope, receive, send)

    async def handle_terminal(self, scope, receive, send):
        term = ghostty_vt.Terminal(80, 24)

        while True:
            message = await receive()
            if message["type"] == "websocket.receive":
                data = message.get("bytes", b"")
                term.process(data)

                await send({
                    "type": "websocket.send",
                    "text": term.screen_json()
                })
```

### Daphne Configuration

```python
# asgi.py
import os
from django.core.asgi import get_asgi_application
from channels.routing import ProtocolTypeRouter, URLRouter
from channels.auth import AuthMiddlewareStack

os.environ.setdefault('DJANGO_SETTINGS_MODULE', 'myproject.settings')

application = ProtocolTypeRouter({
    "http": get_asgi_application(),
    "websocket": AuthMiddlewareStack(
        URLRouter([
            path("terminal/<session_id>/", TerminalConsumer.as_asgi()),
        ])
    ),
})

# Run with: daphne -b 0.0.0.0 -p 8000 myproject.asgi:application
```

---

## Cross-Integration: Terminal Mesh

```
┌─────────────────────────────────────────────────────────────┐
│                    ACI Terminal Mesh                         │
├─────────────────────────────────────────────────────────────┤
│                                                              │
│  Emacs (-1)         MCP Server (0)        Daphne (+1)       │
│  #E7B367            #46F27F               #F0D127           │
│  ┌─────────┐        ┌─────────┐          ┌─────────┐       │
│  │ vterm   │◄──────►│ ghostty │◄────────►│ Django  │       │
│  │ eat     │        │   MCP   │          │Channels │       │
│  └─────────┘        └─────────┘          └─────────┘       │
│       │                  │                    │             │
│       └──────────────────┼────────────────────┘             │
│                          │                                   │
│                    libghostty-vt                             │
│                    (Zero Dependencies)                       │
│                                                              │
└─────────────────────────────────────────────────────────────┘
```

---

## Building libghostty

### As Zig Module

```zig
// build.zig
const ghostty_vt = b.dependency("ghostty-vt", .{
    .target = target,
    .optimize = optimize,
});

exe.root_module.addImport("vt", ghostty_vt.module("ghostty-vt"));
```

### As C Library

```bash
cd ghostty
zig build -Doptimize=ReleaseFast -Dtarget=native-native-musl lib

# Outputs: zig-out/lib/libghostty-vt.a
# Headers: zig-out/include/ghostty_vt.h
```

### Python Bindings (cffi)

```python
from cffi import FFI
ffi = FFI()

ffi.cdef("""
    typedef struct ghostty_terminal ghostty_terminal_t;

    ghostty_terminal_t* ghostty_terminal_new(uint16_t width, uint16_t height);
    void ghostty_terminal_free(ghostty_terminal_t* term);
    void ghostty_terminal_process(ghostty_terminal_t* term, const uint8_t* data, size_t len);
    const char* ghostty_terminal_screen_json(ghostty_terminal_t* term);
""")

lib = ffi.dlopen("libghostty-vt.so")
```

---

## GF(3) Triads

```
libghostty-aci (0) ⊗ sheaf-cohomology (-1) ⊗ gay-mcp (+1) = 0 ✓
libghostty-aci (0) ⊗ captp (-1) ⊗ goblins (+1) = 0 ✓
emacs-vterm (-1) ⊗ libghostty-aci (0) ⊗ daphne-ws (+1) = 0 ✓
```

---

## Commands

```bash
# Build libghostty-vt
just ghostty-build

# Test Emacs integration
emacs --eval '(vterm-ghostty-test)'

# Start MCP terminal server
just mcp-terminal-server

# Run Daphne with terminal support
daphne -b 0.0.0.0 -p 8000 project.asgi:application
```

---

## Related Skills

| Skill | Trit | Relation |
|-------|------|----------|
| captp | 0 | Capability transport for terminal sessions |
| goblins | +1 | Actor model for terminal instances |
| autopoiesis | 0 | Self-modifying terminal config |
| tree-sitter | -1 | AST parsing of terminal output |

---

**Skill Name**: libghostty-aci
**Type**: Terminal Integration
**Trit**: 0 (ERGODIC)
**Seed**: 1069
**Dependencies**: libghostty-vt (Zig), channels (Python), tokio (Rust)


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
