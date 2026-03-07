# Livestream Skill: Warehouse Audio Pipeline

Live audio capture, transcription, and narration from the meeting room via Tailscale network.

## Architecture

```
conversation-logger (10.1.10.107)          Local Mac
  3x EMEET OfficeCore M0 Plus USB mics     (fallback: audio-capture-org.py)
  Whisper large-v3-turbo, 6-speaker         mlx-whisper-small, no diarization
  PostgreSQL → Flask :5000                  audio-capture.org → DuckDB
        │                                          │
        ▼                                          ▼
  /api/transcripts?limit=N                  live_history_pipeline.sql
        │
        └──── sshpass via gx10-acee ──────────────┐
                                                   ▼
                                          Say MCP (Samantha Enhanced)
```

## Access Path

### Step 1: SSH to gx10-acee (jump host)
```bash
sshpass -p 'aaaaaa' ssh -o ConnectTimeout=10 -o StrictHostKeyChecking=no a@100.67.53.87
```
- Host: gx10-acee, Tailscale IP: 100.67.53.87
- User: `a`, Password: `aaaaaa`
- NVIDIA HDA audio card, WiFi on `wlP9s9`

### Step 2: SSH to conversation-logger
```bash
sshpass -p 'aaaaaa' ssh -o ConnectTimeout=5 -o StrictHostKeyChecking=no alu@10.1.10.107
```
- Host: conversation-logger, LAN IP: 10.1.10.107
- User: `alu`, Password: `aaaaaa`
- 3x EMEET mics on ALSA cards 1, 2, 3

### Step 3: Query the API
```bash
curl -s 'http://10.1.10.107:5000/api/transcripts?limit=10'
```

### One-liner (from local Mac)
```bash
sshpass -p 'aaaaaa' ssh -o ConnectTimeout=10 -o StrictHostKeyChecking=no a@100.67.53.87 \
  "curl -s 'http://10.1.10.107:5000/api/transcripts?limit=10'"
```

### One-liner (execute command on logger)
```bash
sshpass -p 'aaaaaa' ssh -o ConnectTimeout=10 -o StrictHostKeyChecking=no a@100.67.53.87 \
  'sshpass -p "aaaaaa" ssh -o ConnectTimeout=5 -o StrictHostKeyChecking=no alu@10.1.10.107 "COMMAND"'
```

## API Endpoints

| Endpoint | Method | Description |
|----------|--------|-------------|
| `/api/transcripts?limit=N` | GET | Recent transcripts (JSON: id, speaker_id, transcript, started_at, ended_at, zone_id, confidence, duration_sec) |
| `/transcripts` | GET | Web UI transcript browser |
| `/conversations` | GET | Conversation groupings |
| `/digests` | GET | Digest summaries |
| `/speakers` | GET | Speaker profiles |

## Infrastructure on conversation-logger

### Systemd Services
- `warehouse-capture-mic1.service` — Mic 1 capture (device 4, Whisper large-v3-turbo)
- `warehouse-capture-mic2.service` — Mic 2 capture (device 5)
- `warehouse-capture-mic3.service` — Mic 3 capture (device 6)
- `warehouse-autogain.service` — Auto-gain controller
- `warehouse-gui.service` — Flask web dashboard (:5000)
- `postgresql@16-main.service` — PostgreSQL 16

### Key Paths
- `/opt/warehouse-logging/scripts/capture_node.py` — Main capture script
- `/opt/warehouse-logging/scripts/auto_gain.py` — Gain controller
- `/opt/warehouse-logging/app.py` — Flask dashboard
- `/opt/warehouse-logging/venv/` — Python virtualenv

### Hardware
- 3x EMEET OfficeCore M0 Plus (USB, Bus 001 Devices 3/5/9)
- ALSA cards: 1 (Plus), 2 (Plus_1), 3 (Plus_2)
- NVIDIA HDA on card 0 (not used for capture)

### Network
- WiFi only (`wlP9s9`): SSID `TP-Link_A7B3`, 2.4GHz Ch2, -47dBm, 94%
- All ethernet ports DOWN (NO-CARRIER) — single point of failure
- Consider connecting ethernet for reliability

## Live Narration Script

Save to `/tmp/live-warehouse-stream.sh`:

```bash
#!/bin/bash
# Speaks ALL new transcripts, batched by speaker, no cutoffs
export PATH="/Users/alice/v/.flox/run/aarch64-darwin.v.dev/bin:$PATH"
ACEE="100.67.53.87"
LOGGER="10.1.10.107"
LAST_ID=""
POLL_INTERVAL=5
LIMIT=50

voice_for_speaker() {
    case "$1" in
        SPEAKER_00|alu)    echo "Ava (Premium)" ;;
        SPEAKER_01)        echo "Evan (Enhanced)" ;;
        SPEAKER_02)        echo "Allison (Enhanced)" ;;
        SPEAKER_03)        echo "Nathan (Enhanced)" ;;
        SPEAKER_04)        echo "Noelle (Enhanced)" ;;
        SPEAKER_05)        echo "Nicky (Enhanced)" ;;
        silly-alu)         echo "Samantha (Enhanced)" ;;
        *)                 echo "Ava (Premium)" ;;
    esac
}

while true; do
    RESULT=$(sshpass -p 'aaaaaa' ssh -o ConnectTimeout=8 \
        -o StrictHostKeyChecking=no -o BatchMode=no a@$ACEE \
        "curl -s 'http://$LOGGER:5000/api/transcripts?limit=$LIMIT'" 2>/dev/null)
    [ $? -ne 0 ] || [ -z "$RESULT" ] && { sleep $POLL_INTERVAL; continue; }

    # Parse & reverse to chronological order
    PARSED=$(echo "$RESULT" | python3 -c "
import json,sys
try:
    d=json.load(sys.stdin)
    lines = []
    for t in d['transcripts']:
        lines.append(f\"{t['id']}|{t['speaker_id']}|{t['transcript']}\")
    for line in reversed(lines):
        print(line)
except: pass
" 2>/dev/null)
    [ -z "$PARSED" ] && { sleep $POLL_INTERVAL; continue; }

    # First run: initialize without speaking history
    if [ -z "$LAST_ID" ]; then
        LAST_ID=$(echo "$PARSED" | tail -1 | cut -d'|' -f1)
        sleep $POLL_INTERVAL; continue
    fi

    # Collect all new transcripts, batch consecutive same-speaker
    FOUND_LAST=0; CURRENT_SPEAKER=""; CURRENT_TEXT=""; NEW_COUNT=0
    while IFS= read -r line; do
        ID=$(echo "$line" | cut -d'|' -f1)
        SPEAKER=$(echo "$line" | cut -d'|' -f2)
        TEXT=$(echo "$line" | cut -d'|' -f3)
        if [ "$FOUND_LAST" -eq 0 ]; then
            [ "$ID" = "$LAST_ID" ] && FOUND_LAST=1; continue
        fi
        NEW_COUNT=$((NEW_COUNT + 1)); LAST_ID="$ID"
        TRIMMED=$(echo "$TEXT" | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')
        [ -z "$TRIMMED" ] && continue
        if [ "$SPEAKER" = "$CURRENT_SPEAKER" ]; then
            CURRENT_TEXT="$CURRENT_TEXT $TRIMMED"
        else
            if [ -n "$CURRENT_TEXT" ] && [ -n "$CURRENT_SPEAKER" ]; then
                VOICE=$(voice_for_speaker "$CURRENT_SPEAKER")
                echo "[$(date +%H:%M:%S)] $CURRENT_SPEAKER: $CURRENT_TEXT"
                say -v "$VOICE" -r 210 "$CURRENT_TEXT" 2>/dev/null
            fi
            CURRENT_SPEAKER="$SPEAKER"; CURRENT_TEXT="$TRIMMED"
        fi
    done <<< "$PARSED"
    # Speak last batch
    if [ -n "$CURRENT_TEXT" ] && [ "$NEW_COUNT" -gt 0 ]; then
        VOICE=$(voice_for_speaker "$CURRENT_SPEAKER")
        echo "[$(date +%H:%M:%S)] $CURRENT_SPEAKER: $CURRENT_TEXT"
        say -v "$VOICE" -r 210 "$CURRENT_TEXT" 2>/dev/null
    fi
    sleep $POLL_INTERVAL
done
```

### Key design choices
- **`limit=50`**: Catches all transcripts between polls (Whisper produces ~1 fragment/second)
- **Chronological reversal**: API returns newest-first; we reverse for natural speech order
- **Speaker batching**: Consecutive same-speaker fragments concatenated into one `say` call
- **No "SPEAKER says:" prefix**: Voice identity conveys the speaker; text spoken naturally
- **First-poll skip**: Initializes at current position without blasting history

## Say MCP Voice Selection

Two MCP servers available for TTS:

| Server | Tool | Voice Param | Rate Param |
|--------|------|-------------|------------|
| `say` | `mcp__say__speak` | Name string (e.g. `"Ava (Premium)"`) | WPM (1-500, default 175) |
| `macos-speech-sdk` | `mcp__macos-speech-sdk__speak` | Name or identifier (e.g. `"com.apple.voice.premium.en-US.Ava"`) | 0.0-1.0 mapped to 80-300 WPM, or direct WPM if >1 |

### High-Quality en-US Voices

| Voice | Quality | Identifier | Gender | Trit |
|-------|---------|------------|--------|------|
| Ava (Premium) | premium | `com.apple.voice.premium.en-US.Ava` | F | +1 |
| Ava (Enhanced) | enhanced | `com.apple.voice.enhanced.en-US.Ava` | F | +1 |
| Samantha (Enhanced) | enhanced | `com.apple.voice.enhanced.en-US.Samantha` | F | 0 |
| Allison (Enhanced) | enhanced | `com.apple.voice.enhanced.en-US.Allison` | F | -1 |
| Evan (Enhanced) | enhanced | `com.apple.voice.enhanced.en-US.Evan` | M | +1 |
| Nathan (Enhanced) | enhanced | `com.apple.voice.enhanced.en-US.Nathan` | M | 0 |
| Nicky (Enhanced) | enhanced | `com.apple.ttsbundle.siri_Nicky_en-US_premium` | F | -1 |
| Noelle (Enhanced) | enhanced | `com.apple.voice.enhanced.en-US.Noelle` | F | 0 |

### Per-Speaker Voice Mapping
- SPEAKER_00/alu → Ava (Premium) — primary speaker, highest quality
- SPEAKER_01 → Evan (Enhanced) — male voice for contrast
- SPEAKER_02 → Allison (Enhanced)
- SPEAKER_03 → Nathan (Enhanced)
- SPEAKER_04 → Noelle (Enhanced)
- SPEAKER_05 → Nicky (Enhanced)

### MCP vs CLI Usage
- **Background script** (`/tmp/live-warehouse-stream.sh`): Uses CLI `say -v "Voice Name"` — works headless
- **In-session narration**: Use `mcp__macos-speech-sdk__speak` with voice identifier for full control
- `mcp__say__speak` has `background: true` param for non-blocking speech

## Local Fallback (SDF Ch8 Degeneracy)

When remote pipeline is unreachable, use local mic capture:
```bash
/Users/alice/v/.venv-mlx-lm/bin/python /Users/alice/v/scripts/audio-capture-org.py
```
- Captures MacBook Pro Microphone via FFmpeg avfoundation `:1`
- Transcribes with mlx-whisper-small (16kHz, 8s chunks)
- Appends to `/Users/alice/v/audio-capture.org`

## DuckDB Integration

### Ingest history for audio digest
```bash
duckdb -c ".read /Users/alice/v/live_history_pipeline.sql"
```
- Merges claude/preclaude/codex history
- Generates TTS-ready `narration_line` fields
- `audio_digest` view: top 10 sessions formatted for voice

### Audio ACSet database
- `/Users/alice/v/audio_acset.duckdb` — Structured audio metadata
- Tables: AudioFile, Transcript, Segment, Speaker, Topic, ACSetSchema

## SDF Analysis

Per Software Design for Flexibility (Hanson & Sussman):

- **Ch1 Combinators**: Pipeline = compose(ssh_tunnel, api_poll, tts_narrate)
- **Ch7 Propagators**: Transcripts flow: mic → whisper → postgres → API → say (bidirectional: can query history backwards)
- **Ch8 Degeneracy**: Remote warehouse (primary) vs local mic (fallback) — same generic interface, different implementations
- **Ch9 Generic Dispatch**: `narrate(source)` dispatches on source type: warehouse API vs local org file

## Dependency Structure

```
[USB Mics] ──USB──→ [conversation-logger]
                         │
                    [ALSA/PulseAudio]
                         │
                    [capture_node.py × 3]
                         │
                    [Whisper large-v3-turbo]
                         │
                    [PostgreSQL 16]
                         │
                    [Flask :5000]
                         │
                    [WiFi: TP-Link_A7B3] ← SINGLE POINT OF FAILURE
                         │
                    [LAN: 10.1.10.107]
                         │
            [gx10-acee: 100.67.53.87 via Tailscale]
                         │
                    [Local Mac: sshpass + curl]
                         │
                    [Say MCP / say command]
```

**Risk**: WiFi is the only network path. All ethernet ports show NO-CARRIER.
**Mitigation**: USB mics and local capture/transcription continue even if WiFi drops — data accumulates locally and can be retrieved when connectivity returns.
