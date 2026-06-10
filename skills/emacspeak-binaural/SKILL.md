---
name: emacspeak-binaural <<<<<<< HEAD
description: Replace emacspeak auditory icons with binaural beats using the sound theme system. Load when customizing emacspeak sounds, creating new sound themes, or working with binaural audio on macOS with SwiftMac TTS. >>>>>>> origin/main
metadata:
  trit: '1'
---

# Emacspeak Binaural Beat Theme

<<<<<<< HEAD
Replace emacspeak's auditory icons with binaural beats via the intended sound theme system.

## When to Use

- User wants to change emacspeak sounds to binaural beats
- User asks about customizing emacspeak auditory icons
- User wants to create custom emacspeak sound themes

=======
>>>>>>> origin/main
## Architecture

Emacspeak has three separate sound systems:

<<<<<<< HEAD
| System | Mechanism | Sound |
|--------|-----------|-------|
| **Auditory icons** | OGG files from theme dir, served via `p <filename>` | Chimes on navigation |
| **Pure tones** | `dtk-tone` sends `t <pitch> <dur>` to TTS server | Beeps on empty lines |
| **Soundscapes** | Boodler ambient audio per major mode | Background audio |

On macOS/SwiftMac, `swiftmac-configure-tts` forces `emacspeak-play-program` to `nil`, routing all icons through SwiftMac's OGG player.

## Installation

### 1. Generate binaural beat OGG files

```bash
mkdir -p ~/emacspeak/sounds/binaural
cd ~/emacspeak/sounds/binaural
SOX=$(which sox)
=======
| System | Mechanism | What you hear |
|--------|-----------|---------------|
| **Auditory icons** | OGG files from theme dir, served to TTS server via `p <filename>` | Chimes on navigation, actions |
| **Pure tones** | `dtk-tone` -> `t <pitch> <dur>` to TTS server | Beeps on empty lines, case changes |
| **Soundscapes** | Boodler ambient audio mapped to major modes via UNIX socket | Continuous background audio |

On macOS with SwiftMac, `swiftmac-configure-tts` forces `emacspeak-play-program` to `nil`, routing ALL auditory icons through SwiftMac's OGG player.

## Creating a Theme

1. Create a directory under `~/emacspeak/sounds/<theme-name>/`
2. Populate with `.ogg` files named after the 56 standard icons
3. Call `(emacspeak-sounds-select-theme (expand-file-name "<theme-name>" emacspeak-sounds-dir))`

The cache rebuilds automatically. All playback paths use the same cache.

## Current Installation

Theme directory: `~/emacspeak/sounds/binaural/`

init.el config (after emacspeak loads):
```elisp
(emacspeak-sounds-select-theme
 (expand-file-name "binaural" emacspeak-sounds-dir))
```

## Generating the Theme

Each icon gets a unique carrier frequency (100-320 Hz) and beat frequency (2-10 Hz):

```bash
cd ~/emacspeak/sounds/binaural
SOX=/Users/alice/.local/bin/sox
>>>>>>> origin/main
i=0
for icon in alarm alert-user ask-question ask-short-question button center \
  char close-object complete delete-object deselect-object doc ellipses \
  fill-object help item key large-movement left mark-object modified-object \
  more n-answer network-down network-up new-mail news no-answer off on \
  open-object paragraph process-active progress repeat-active repeat-end \
  repeat-start right save-object scroll search-hit search-miss section \
  select-object shutdown task-done tick-tick time tock-tock unmodified-object \
  voice-mail warn-user window-resize y-answer yank-object yes-answer; do
  carrier=$((100 + i * 4))
  beat_tenth=$((20 + (i * 7 % 80)))
  beat=$(echo "scale=1; $beat_tenth / 10" | bc)
  freq_r=$(echo "scale=1; $carrier + $beat" | bc)
  "$SOX" -n "${icon}.ogg" synth 0.15 sine "$carrier" sine "$freq_r" \
    gain -18 channels 2 fade q 0.01 0.15 0.02
  i=$((i + 1))
done
```

<<<<<<< HEAD
### 2. Add to init.el (after emacspeak loads)

```elisp
(emacspeak-sounds-select-theme
 (expand-file-name "binaural" emacspeak-sounds-dir))
```

## Pitfalls

- **Do NOT override `dtk-tone` or `emacspeak-icon`** — the sound is auditory icons (OGGs), not tones. Function overrides fail silently because `sox-gen-p`/`sox-play` may be nil in Emacs's exec-path.
- **Do NOT set `SWIFTMAC_TONE_VOLUME=0.0`** — silences more than just tones.
- **Do NOT set `emacspeak-play-program` on macOS** — `swiftmac-configure-tts` resets it to nil.

## Icon Dispatch Path (macOS)

```
emacspeak-icon(icon)
  -> emacspeak-serve-icon(icon)
     -> sends "p <filename>\n" to dtk-speaker-process
        -> SwiftMac doPlaySound -> OGGDecoder -> SoundManager -> audio
```

## Customization

Each icon gets a unique carrier (100-320 Hz) and beat frequency (2-10 Hz). Adjust:
- **Duration**: Change `synth 0.15` (currently 150ms)
- **Volume**: Change `gain -18` (lower = quieter)
- **Brainwave band**: Vary beat frequencies per icon category

## Dependencies

- SoX (`sox` binary for OGG generation)
- Emacspeak with SwiftMac (macOS)

## Related

- `sox-gen.el` — Raman's built-in binaural module (`M-x sox-binaural`)
- `soundscape.el` — Ambient audio per mode (`M-x soundscape-toggle`)
- Sound themes: `chimes/` (default), `3d/` — switch with `M-x emacspeak-sounds-select-theme`
=======
## 56 Standard Icon Names

```
alarm alert-user ask-question ask-short-question button center
char close-object complete delete-object deselect-object doc ellipses
fill-object help item key large-movement left mark-object modified-object
more n-answer network-down network-up new-mail news no-answer off on
open-object paragraph process-active progress repeat-active repeat-end
repeat-start right save-object scroll search-hit search-miss section
select-object shutdown task-done tick-tick time tock-tock unmodified-object
voice-mail warn-user window-resize y-answer yank-object yes-answer
```

Missing icons fall back to `button.ogg` (via `emacspeak-sounds-cache-get` default).

## Pitfalls on macOS

### DO NOT override `dtk-tone` or `emacspeak-icon`
- `sox-gen-p` / `sox-play` are nil if `/Users/alice/.local/bin/` is not in `exec-path` at `emacspeak-preamble.el` load time
- The sound you hear is auditory icons (OGGs), NOT tones -- overriding `dtk-tone` changes nothing audible

### DO NOT set `SWIFTMAC_TONE_VOLUME=0.0`
This env var silences more than just pure tones. Remove it.

### DO NOT set `emacspeak-play-program` manually on macOS
`swiftmac-configure-tts` sets it to `nil` during startup. Fighting this breaks icon playback.

### Icon playback dispatch
```
emacspeak-icon(icon)
  -> emacspeak-play-program is nil? (macOS: always yes)
       -> emacspeak-serve-icon(icon)
            -> sends "p <filename>\n" to dtk-speaker-process (SwiftMac)
                 -> SwiftMac plays the OGG file via AVAudioEngine
```

## Brainwave Bands per Icon Category

```
Action icons (delete, yank, fill)      -> beta beats 13-40 Hz (alertness)
Navigation icons (left, right, scroll) -> alpha beats 8-12 Hz (relaxed focus)
Status icons (complete, task-done)     -> theta beats 4-8 Hz (satisfaction)
Warning icons (alarm, warn-user)       -> gamma beats 40+ Hz (attention)
```

## Dependencies

- SoX (`sox` and `play` at `/Users/alice/.local/bin/`)
- Emacspeak with SwiftMac TTS server
- macOS (SwiftMac is macOS-only via AVSpeechSynthesizer)
>>>>>>> origin/main
