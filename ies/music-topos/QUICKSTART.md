# Music Topos - Quick Start

## Installation

### 1. SuperCollider (Manual)
1. Download from: https://supercollider.github.io/downloads.html
2. Install the macOS version
3. Open `SuperCollider.app`
4. Click "Boot Server" button (you should see green text indicating success)

### 2. Clojure/Leiningen
Already configured via Flox:
```bash
flox activate
```

## Run

**Start SuperCollider first** (see above), then:

```bash
# Terminal 1: Boot SuperCollider server
# (open SuperCollider.app and click "Boot Server")

# Terminal 2: Play the worlds
cd /Users/bob/ies/music-topos
flox activate
lein run initial              # Play initial object world (emergence)
lein run terminal             # Play terminal object world (sonata)
```

## Or Use REPL

```bash
flox activate
lein repl

# Inside REPL:
(use 'music-topos.core)
(play-initial-world)          ; Play initial world
(Thread/sleep 20000)          ; Wait 20 seconds
(play-terminal-world)         ; Play terminal world
(stop)                        ; Stop everything
```

## What Plays

### Initial Object World (~10 seconds)
1. **Initial Pitch** - C4 (262Hz) - the atomic unit
2. **Pitch Classes** - All 12 semitones (chromatic scale)
3. **Harmonic Functions** - Tonic → Subdominant → Dominant → Tonic
4. **Modulation** - Circle of fifths (C → G → D → F → C)

### Terminal Object World (~12 seconds)
1. **Exposition** - Two themes presented
2. **Development** - Key exploration
3. **Recapitulation** - Return home
4. **Coda** - Authentic cadence closure (V → I)

## Code Structure

```
music-topos/
├── project.clj                      # Build config
├── src/music_topos/core.clj        # Everything (170 lines)
│   ├── defsynth sine-synth         # Pure sine tone
│   ├── defsynth chord-synth        # Harmonic chords
│   ├── (def initial-world ...)     # World definition
│   ├── (def terminal-world ...)    # World definition
│   ├── (defn play-initial-world)   # Render function
│   ├── (defn play-terminal-world)  # Render function
│   └── (defn -main)                # Entry point
└── README.md                        # System overview
```

## Troubleshooting

### "Connection refused" error
- SuperCollider server is not running
- Open SuperCollider.app
- Click "Boot Server" button
- Wait for green text

### No sound
1. Check system volume (not muted)
2. Check Sonic Preferences → Output device selected
3. Try clicking "Boot Server" button again
4. Check SuperCollider console for error messages

### Clojure errors
```bash
# Update dependencies
lein clean
lein deps

# Try again
lein run initial
```

### Can't find lein
```bash
# Make sure you're in Flox environment
flox activate

# Then run
lein run initial
```

---

**That's it. Pure Clojure + Overtone + SuperCollider. No Ruby, no Sonic Pi, no OSC protocol complexity.**
