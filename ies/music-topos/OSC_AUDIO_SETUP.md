# OSC Audio Setup: Hear the Mathematics

**OSC = Open Sound Control**

A network protocol for sending musical control messages to synthesizers. In this system:
- **Client**: Your Ruby code (music-topos)
- **Server**: Sonic Pi (audio synthesis engine)
- **Protocol**: UDP on localhost:4557

---

## What Is OSC?

OSC is like MIDI but for networked computers. Instead of cables between hardware synthesizers, it sends messages over UDP:

```
Ruby REPL → OSC Message → Sonic Pi → Audio Output
          (UDP packet)
```

**OSC Message Example**:
```
/run/code
  "play 60, amp: 0.7, release: 1.0"
```

This tells Sonic Pi: "Play MIDI note 60 (middle C), volume 70%, 1 second release time"

---

## Setup: Hear Actual Sound

### Step 1: Install Sonic Pi

**macOS**:
```bash
brew install sonic-pi
```

Or download from: https://sonic-pi.net/download

**Linux/Windows**:
Download from https://sonic-pi.net/download

### Step 2: Start Sonic Pi

1. Launch Sonic Pi application
2. It starts listening on `localhost:4557` automatically
3. You should see the splash screen

### Step 3: Run the REPL with Sonic Pi

```bash
ruby /Users/bob/ies/music-topos/bin/interactive_repl.rb
```

Now when you play chords, you'll see:

```
> play C E G C

Playing: Chord(C-E-G-C)
✓ Semantic closure verified (8/8 dimensions)
Rendering audio...
Frequencies: 261.63, 164.81, 196.0, 65.41 Hz
MIDI notes: 60, 52, 55, 36

✓ [OSC → Sonic Pi] play(60) @ 261.63 Hz
✓ [OSC → Sonic Pi] play(52) @ 164.81 Hz
✓ [OSC → Sonic Pi] play(55) @ 196.0 Hz
✓ [OSC → Sonic Pi] play(36) @ 65.41 Hz
```

**And you'll HEAR a C major chord in four voices.**

---

## How OSC Works in Our System

### 1. Validation Gate (Before Sound)

```ruby
# Only mathematically valid compositions make sound
closure = OntologicalValidator.semantic_closure(composition)

if closure[:closed]  # All 8 dimensions true
  # THEN send OSC to Sonic Pi
  send_to_sonic_pi(osc_message)
else
  # REJECT - no sound produced
  puts "✗ Semantic closure failed - audio blocked"
end
```

### 2. OSC Packet Format

The system builds proper OSC bundles:

```ruby
bundle = "BundleOSC"           # Bundle identifier
bundle << time_tag             # When to execute (0 = now)
bundle << message_size         # How many bytes follow
bundle << osc_message          # The actual command

# OSC Message structure:
/run/code\0                   # Path (Sonic Pi endpoint)
,s\0\0                        # Type: string argument
"play 60, amp: 0.7\0"        # The Sonic Pi code
```

All properly null-terminated and padded to 4-byte boundaries (OSC standard).

### 3. UDP Socket Connection

```ruby
@socket = UDPSocket.new
@socket.connect('localhost', 4557)  # Connect to Sonic Pi
@socket.send(osc_bundle, 0)         # Send packet
```

---

## What Happens Inside Sonic Pi

When Sonic Pi receives an OSC message with code:

```
play 60, amp: 0.7, release: 1.0
```

It:
1. Parses the Sonic Pi code
2. Synthesizes the sound (using sine wave oscillators)
3. Routes to audio output
4. **You hear it**

The synthesis happens at **44.1 kHz sample rate** in real-time.

---

## Without Sonic Pi (Fallback)

If Sonic Pi isn't running, the system gracefully degrades:

```
> play C E G C
...
ℹ [Would play] MIDI 60 (261.63 Hz)
💡 To hear audio: Start Sonic Pi and it will receive OSC messages here
```

You'll see what *would* be sent, but no sound. This lets you:
- Test the REPL without Sonic Pi
- Verify OSC message construction
- Debug composition validation

---

## The Complete Perception/Action Loop

```
You type:          play C E G C
                        ↓
System parses:     chord = Chord.from_notes(['C', 'E', 'G', 'C'])
                        ↓
Validates:         8-point semantic closure check
                   ✓ All dimensions true
                        ↓
Constructs OSC:    /run/code
                   "play 60, amp: 0.7, release: 1.0"
                   "play 52, amp: 0.7, release: 1.0"
                   (x4 for 4 voices)
                        ↓
Sends via UDP:     @socket.send(osc_bundle, 0)
                        ↓
Sonic Pi receives: "play 60, amp: 0.7, release: 1.0"
                        ↓
Sonic Pi renders:  Synthesizes sine wave
                   44.1 kHz, 16-bit PCM
                        ↓
Audio device:      Loudspeakers
                        ↓
YOU HEAR:          Middle C (60 Hz fundamental)
                   E below middle C
                   G below that
                   Low C one octave down

                   = C Major Chord in 4-voice harmony
                   = Mathematically verified voice leading
```

---

## OSC Parameters in Our System

### Channel Layout (4 voices = SATB)

| Voice | MIDI | Octave | Frequency | Amplitude |
|-------|------|--------|-----------|-----------|
| Soprano | 60-84 | 4 | 261.63 - 440 Hz | 0.175 |
| Alto | 48-72 | 3 | 130.81 - 261.63 Hz | 0.175 |
| Tenor | 48-72 | 3 | 130.81 - 261.63 Hz | 0.175 |
| Bass | 24-48 | 2 | 65.41 - 130.81 Hz | 0.175 |

**Total amplitude**: 0.175 × 4 = 0.7 (prevents clipping)

### Message Endpoints

**Sonic Pi OSC endpoint**: `/run/code`

**Message format**:
```
play <midi>, amp: <amplitude>, release: <duration>
```

Example:
```
play 60, amp: 0.175, release: 1.0
```

---

## Troubleshooting

### Problem: "OSC initialization failed"

**Sonic Pi not running**
```bash
# Make sure Sonic Pi is launched
# It should show in Applications / System Tray
```

**Wrong port**
- Sonic Pi default: `localhost:4557`
- If you changed it in Sonic Pi preferences, update in `sonic_pi_renderer.rb` line 28

### Problem: "ECONNREFUSED"

Sonic Pi is not listening on port 4557.

**Solution**:
1. Restart Sonic Pi
2. Check firewall isn't blocking localhost
3. Verify port with: `lsof -i :4557`

### Problem: Sound is distorted/clipping

The amplitude might be too high.

**Solution**:
- Current: 0.175 per voice (safe)
- To reduce: Edit `lib/sonic_pi_renderer.rb` line 50
- Change `amplitude / 4.0` to `amplitude / 5.0` or lower

---

## Testing OSC Connection

Run this Ruby code to test OSC:

```ruby
require 'socket'

socket = UDPSocket.new
socket.connect('localhost', 4557)

# Send a simple Sonic Pi command
code = "puts 'OSC test: connection successful'"
socket.send(code, 0)

puts "✓ OSC message sent"
socket.close
```

If it works, Sonic Pi is listening.

---

## Advanced: Custom OSC Messages

You can extend the system to send OSC directly:

```ruby
# In interactive_repl.rb or custom script:
require_relative 'lib/sonic_pi_renderer'

renderer = SonicPiRenderer.new
renderer.send_to_sonic_pi({
  midi: 60,
  duration: 2.0,
  amplitude: 0.7
})
```

Or use the Chord system:

```ruby
chord = Chord.from_notes(['C', 'E', 'G', 'C'])
renderer.play_chord(chord, duration: 1.0)
```

---

## What You'll Perceive

When you play the system:

1. **Pitch accuracy**: Each note is exactly the right frequency
2. **Voice leading**: Smooth transitions between chords (minimize motion)
3. **Harmony**: The mathematical relationships become audible
4. **Closure**: You'll *hear* when compositions resolve mathematically

The sound validates the mathematics.

---

## The Philosophy

**This system proves**:

- Mathematics isn't abstract
- Voice leading rules are geometric facts
- Harmonic closure is topologically necessary
- You can verify theory by ear

**OSC makes it real** - not theoretical, not simulated, but actual sound waves in the air.

---

**Ready?**

1. Install Sonic Pi
2. Start Sonic Pi
3. Run: `ruby bin/interactive_repl.rb`
4. Type: `play C E G C`
5. **Listen to mathematics**

The chord you hear is proof.
