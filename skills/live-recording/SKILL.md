---
name: live-recording
description: "Always-on audio capture via whisper-cpp to org file with Emacs live display"
---

# Live Recording

Always-on environmental audio capture. Records continuously, transcribes with whisper-cpp (Metal-accelerated), appends timestamped entries to an org file viewable live in Emacs.

## Activation

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

## Stopping

```bash
tmux kill-session -t capture
```

## Configuration (in always-on-capture.sh)

| Variable | Default | Purpose |
|----------|---------|---------|
| `AUDIO_DEVICE` | `:1` | avfoundation device (`:0` = screen, `:1` = mic) |
| `CHUNK_SECONDS` | `6` | Recording window per chunk |
| `SILENCE_THRESHOLD` | `0.005` | RMS below this = silence (suppressed) |
| `MIN_TEXT_LEN` | `6` | Discard transcriptions shorter than this |
| `MODEL` | `~/v/ggml-base.en.bin` | Whisper GGML model path |
| `ORG_FILE` | `~/v/audio-capture.org` | Output org file |

## Troubleshooting

| Symptom | Cause | Fix |
|---------|-------|-----|
| All chunks "no audio" | Wrong device index | `ffmpeg -f avfoundation -list_devices true -i ""` to find mic |
| All chunks "silence" | Threshold too high | Lower `SILENCE_THRESHOLD` in script (default 0.005) |
| Emacs not updating | No server-start | `M-x server-start` then reopen file |
| Emacs not tailing | Wrong mode | Use `auto-revert-tail-mode` not `auto-revert-mode` |
| Script exits immediately | `set -e` + non-fatal error | Script uses `set -uo pipefail` (no `-e`) |

## Related Files

- `~/v/audio-capture.org` -- live output file
- `~/v/scripts/always-on-capture.sh` -- capture script
- `~/v/audio_acset.duckdb` -- structured audio database (ACSets schema)
- `~/v/scripts/audio-capture-org.py` -- Python/mlx-whisper alternative
