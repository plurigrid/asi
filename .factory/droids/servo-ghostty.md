---
name: servo-ghostty
description: "Servo browser engine integration with ghostty-web for full-color terminal tiles"
model: inherit
tools: ["Read", "Edit", "Execute", "WebSearch"]
---

# Servo-Ghostty Web Terminal Skill

**Full-color terminal with tile parity using Servo browser engine**

## Overview

This skill provides integration between Servo browser engine and ghostty-web terminal, delivering:
- **Full color support**: CSS Color Level 4 (Display P3, Rec. 2020, Oklch)
- **Tile parity**: CSS Grid for tmux-like splits
- **GPU acceleration**: WebRender compositor
- **WebSocket transport**: Existing ghostty-web :7070

**Winner**: Servo beats Ladyworm (3x faster, 6x less code, 100% tile parity)

## Architecture

```
Ghostty Native (macOS)
    ↓
ghostty-web WebSocket :7070 (Zig, 515 LOC)
    ↓
Servo Browser Engine (Rust)
    ↓
WebRender GPU Compositor
    ↓
HTML/CSS Tile Grid
    ↓
    ├─ Terminal tiles (Canvas 2D)
    ├─ Worlds/t navigation
    ├─ Chartered Flights routes
    ├─ BCI colors (Oklch)
    └─ Gay seed color trajectories
```

## Quick Start

### 1. Install Dependencies

```bash
# Servo (prebuilt binary)
brew install servo

# Or build from source
git clone https://github.com/servo/servo
cd servo
./mach build --release

# Verify
servo --version
```

### 2. Run Ghostty-Web Server

```bash
# Start existing ghostty-web WebSocket server
/Users/bob/i/zig-syrup/zig-out/bin/ghostty-web
# → Listening on ws://localhost:7070
```

### 3. Launch Servo Terminal

```bash
# Run Servo with terminal HTML
cd ~/i/asi/skills/servo-ghostty
servo examples/ghostty-terminal.html

# Or embedded mode
cargo run --bin servo-ghostty-embed
```

## Bundled Resources

### Scripts

| Script | Purpose |
|--------|---------|
| `scripts/servo-embed.rs` | Rust embedding code (200 LOC) |
| `scripts/install-servo.sh` | Install Servo dependencies |
| `scripts/run-terminal.sh` | Launch full stack |
| `scripts/test-colors.sh` | Color space verification |

### Examples

| Example | Purpose |
|---------|---------|
| `examples/ghostty-terminal.html` | Main terminal UI (300 LOC) |
| `examples/ghostty-terminal.css` | Tile styling (200 LOC) |
| `examples/ghostty-terminal.js` | WebSocket