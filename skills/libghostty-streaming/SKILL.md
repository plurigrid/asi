# libghostty-vt Streaming Skill ⬜

**Trit**: 0 (ERGODIC - Coordinator)
**GF(3) Triad**: `asciinema-play (-1) ⊗ libghostty-streaming (0) ⊗ vhs-server (+1) = 0`

## Overview

The **white hole** dual to libghostty-recording. Streams, plays back, and broadcasts terminal sessions. Where recording absorbs (black hole), streaming emits (white hole).

```
Recording (●)  ←→  Streaming (○)
   absorb           emit
   capture          broadcast
   input            output
```

## Playback Methods

### 1. Asciinema Play (Local Replay)
```bash
# Play recording at original speed
asciinema play session.cast

# Speed up 2x
asciinema play -s 2 session.cast

# Idle time limit (skip long pauses)
asciinema play -i 2 session.cast

# Play from URL
asciinema play https://asciinema.org/a/123456
```

### 2. asciinema-server (Self-Hosted Streaming)
```bash
# Run local asciinema server
docker run -d -p 3000:3000 asciinema/asciinema-server

# Stream to self-hosted
asciinema rec -t "live session" http://localhost:3000

# Embed in docs
<script src="https://asciinema.org/a/123456.js"></script>
```

### 3. Charmbracelet VHS Server
```bash
# Serve GIFs via HTTP
vhs serve --port 8080

# Watch for .tape changes and regenerate
vhs watch demo.tape

# Continuous output to stdout
vhs demo.tape --output -
```

### 4. libghostty-vt Stream Hooks
```zig
// Stream terminal output via libghostty
const streamer = ghostty_vt.Streamer.init(.{
    .source = .stdin,
    .format = .cast,
    .broadcast = "ws://localhost:9000/stream",
});

// Emit frames
while (streamer.next()) |frame| {
    try websocket.send(frame.render());
}
```

### 5. ttyd (Web Terminal)
```bash
# Stream terminal to web browser
ttyd -p 7681 bash

# Read-only broadcast mode
ttyd -R -p 7681 asciinema play session.cast

# With authentication
ttyd -c user:pass -p 7681 bash
```

## Streaming Transforms

### Cast → WebSocket
```bash
# Stream .cast to WebSocket clients
cat session.cast | websocat ws-listen:127.0.0.1:9000
```

### Cast → NATS
```bash
# Broadcast to NATS subject
asciinema play session.cast | nats pub terminal.stream
```

### Cast → SSH (Remote Pair)
```bash
# Share session via SSH
asciinema play session.cast | ssh user@remote 'cat'

# Bidirectional with tmux
tmux new-session -d -s shared
tmux send-keys -t shared "asciinema play session.cast" Enter
# Others join: tmux attach -t shared
```

## White Hole Architecture

```
┌─────────────────────────────────────────────────────────┐
│  WHITE HOLE: Terminal Emission                          │
│                                                         │
│  Sources (●→○)           Sinks (○→)                     │
│  ├── .cast files         ├── Web browsers (ttyd)        │
│  ├── Live terminals      ├── WebSocket clients          │
│  ├── tmux sessions       ├── NATS subscribers           │
│  └── libghostty-vt       ├── SSH remote                 │
│                          └── GIF/MP4 renders            │
│                                                         │
│  GF(3): input(-1) ⊗ transform(0) ⊗ output(+1) = 0      │
└─────────────────────────────────────────────────────────┘
```

## LLM Training Pipeline

```bash
# 1. Record sessions (black hole - absorb)
asciinema rec session.cast

# 2. Transform (ergodic - process)
cat session.cast | jq -r '.[] | select(.[0] == "o") | .[2]'

# 3. Stream to training (white hole - emit)
asciinema play session.cast | tee training-corpus.txt
```

## Justfile Recipes

```just
# Play latest recording
play-latest:
    asciinema play $(ls -t ~/recordings/*.cast | head -1)

# Stream to web
stream-web port="7681":
    ttyd -R -p {{port}} asciinema play $(ls -t ~/recordings/*.cast | head -1)

# Broadcast to NATS
stream-nats subject="terminal.live":
    asciinema play ~/recordings/latest.cast | nats pub {{subject}}

# Convert to GIF
cast-to-gif file:
    agg {{file}} {{file}}.gif
```

## Duality Table

| Recording (●) | Streaming (○) |
|--------------|---------------|
| `asciinema rec` | `asciinema play` |
| `vhs demo.tape` | `vhs serve` |
| `script session.log` | `scriptreplay session.log` |
| Input capture | Output broadcast |
| Black hole | White hole |
| Trit -1 (absorb) | Trit +1 (emit) |

## Integration with Gay.jl

```julia
# Color-coded streaming sessions
using Gay
seed!(1069)

session_color = color_at(session_id)
stream_trit = trit_at(session_id)  # -1, 0, or +1

# Route by trit
if stream_trit == -1
    record_session()      # Black hole
elseif stream_trit == 0
    transform_session()   # Ergodic
else
    broadcast_session()   # White hole
end
```

## See Also

- `libghostty-recording` - The black hole dual (recording/capture)
- `asciinema` - Terminal session recorder
- `vhs` - Charmbracelet tape automation
- `ttyd` - Web terminal streaming
- `tmux` - Terminal multiplexing for sharing


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
