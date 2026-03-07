---
name: live-recording
description: Always-on audio capture via whisper-cpp to org file with Emacs live display
---

# Live Recording

**Trit**: 0 (ERGODIC - coordinates hardware capture and knowledge output)

Always-on environmental audio capture. Records continuously, transcribes with whisper-cpp (Metal-accelerated), appends timestamped entries to an org file viewable live in Emacs.

## Prerequisites

```bash
# Packages (provided by flox)
flox install whisper-cpp ffmpeg sox

# Whisper model (147MB, one-time download)
curl -L -o ~/v/ggml-base.en.bin \
  https://huggingface.co/ggerganov/whisper.cpp/resolve/main/ggml-base.en.bin

# Script
~/v/scripts/always-on-capture.sh
```

## Activation (3 steps)

### 1. Start tmux capture session

```bash
tmux new-session -d -s capture \
  'while true; do bash ~/v/scripts/always-on-capture.sh; echo "[restart] $(date)"; sleep 2; done'
```

The auto-restart loop ensures crash resilience. The script records 6s WAV chunks via ffmpeg avfoundation device `:1`, silence-detects via sox RMS (`< 0.005`), transcribes non-silent chunks with `whisper-cli --model ~/v/ggml-base.en.bin`, and appends `** [timestamp]\ntext\n` entries to `~/v/audio-capture.org`.

### 2. Open in Emacs with live updates

```
M-x server-start                          ;; required for emacsclient
C-x C-f ~/v/audio-capture.org             ;; open the file
M-x auto-revert-tail-mode                 ;; live tail as entries append
```

`auto-revert-tail-mode` (not `auto-revert-mode`) tails the end of the buffer as new entries arrive, keeping your cursor at the latest transcription.

### 3. Monitor (optional)

```bash
tmux attach -t capture          # watch capture output
tail -f ~/v/audio-capture.org   # terminal tail
```

## Propagator Network

```
Audio Cell (-1)  -->  Whisper Cell (0)  -->  Org File Cell (+1)
  ffmpeg chunk         whisper-cli           append to .org
  sox silence          ggml-base.en          auto-revert in Emacs
```

GF(3): (-1) + (0) + (+1) = 0

The silence detector implements **corollary discharge** (von Holst): predict silence, only transcribe when prediction is wrong. This suppresses ~80% of chunks, saving compute.

## Stopping

```bash
tmux kill-session -t capture
```

Or `Ctrl+C` if attached to the tmux session.

## Troubleshooting

| Symptom | Cause | Fix |
|---------|-------|-----|
| All chunks "no audio" | Wrong device index | `ffmpeg -f avfoundation -list_devices true -i ""` to find mic |
| All chunks "silence" | Threshold too high | Lower `SILENCE_THRESHOLD` in script (default 0.005) |
| Emacs not updating | No server-start | `M-x server-start` then reopen file |
| Emacs not tailing | Wrong mode | Use `auto-revert-tail-mode` not `auto-revert-mode` |
| Script exits immediately | `set -e` + non-fatal error | Script uses `set -uo pipefail` (no `-e`) |

## Configuration (in always-on-capture.sh)

| Variable | Default | Purpose |
|----------|---------|---------|
| `AUDIO_DEVICE` | `:1` | avfoundation device (`:0` = screen, `:1` = mic) |
| `CHUNK_SECONDS` | `6` | Recording window per chunk |
| `SILENCE_THRESHOLD` | `0.005` | RMS below this = silence (suppressed) |
| `MIN_TEXT_LEN` | `6` | Discard transcriptions shorter than this |
| `MODEL` | `~/v/ggml-base.en.bin` | Whisper GGML model path |
| `ORG_FILE` | `~/v/audio-capture.org` | Output org file |

## GF(3) Triads

```
live-recording (0) + ffmpeg-media (+1) + reafference-corollary-discharge (-1) = 0
live-recording (0) + propagators (+1) + sense (-1) = 0
live-recording (0) + whitehole-audio (+1) + voice-channel-uwd (-1) = 0
```

## Causal Capture Integration (plurigrid/causal)

The init.el loads three capture modules from the plurigrid fork of causal:

### causal-catcolab (C-c C)
- Browse/create CatColab documents (ologs, Petri nets, causal-loop diagrams)
- `causal-catcolab-save-proof-as-olog` — scan current buffer for hypotheses/goals, export as CatColab olog
- Works against `backend.catcolab.org` (no auth for public docs)

### causal-self-walker (M-x causal-self-walker-tmenu)
- Walks proof states step-by-step, records a chain of `causal-self-walker-state` structs
- Exports chain as CatColab olog: each state → object, each tactic → morphism
- Optional Monte Carlo tactic proposals (`causal-self-walker-use-mc`)

### sophia-mnemosyne (RDF knowledge graph)
- `sophia-mnemosyne-save-buffer` — capture any buffer as Mnemosyne document
- SPARQL query interface for searching captured content
- Requires `neem serve` running on `localhost:8001`

### Capture flow

```
audio-capture.org (live tail)
  ↓ C-c C → causal-catcolab-save-proof-as-olog (buffer → olog)
  ↓ causal-self-walker-export-chain-as-olog (chain → olog)
  ↓ sophia-mnemosyne-save-buffer (buffer → RDF document)
```

## Related

- `~/v/audio-olog.org` - Category-theoretic ontology of captured audio
- `~/v/audio_acset.duckdb` - Structured audio database (ACSets schema)
- `~/v/scripts/audio-capture-org.py` - Python/mlx-whisper alternative
- `/tmp/causal/` - plurigrid/causal Emacs package (catcolab + self-walker + mnemosyne)
