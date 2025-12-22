# Collaboration Architecture: Music Topos Real-Time Platform

Analysis of technical options for extending Music Topos into a real-time collaborative platform.

## Use Cases Summary

| Use Case | Latency Req | State Complexity | Scale | Key Tech |
|----------|-------------|------------------|-------|----------|
| 1. Real-time music collaboration | <50ms | High (patterns) | 2-10 users | WebRTC + CRDT |
| 2. Visualization sharing | <200ms | Medium (UI state) | 10-100 users | WebSocket + CRDT |
| 3. Research streaming | ~1-5s OK | Low (one-way) | 1-1000 viewers | HLS/WebRTC |
| 4. Custom multi-modal platform | Mixed | Very high | Variable | Hybrid |

---

## 1. Real-Time Music/Audio Collaboration

**Goal:** Multiple users generating/editing music patterns with low-latency audio

### Technical Requirements

- **Audio latency:** <50ms round-trip (ideally <20ms for jam sessions)
- **State sync:** Pattern edits visible to all within 100ms
- **Audio streaming:** High quality, low latency, possibly uncompressed
- **Conflict resolution:** Simultaneous edits to same pattern

### Recommended Stack

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         COLLABORATIVE MUSIC STACK                           │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────┐     ┌─────────────┐     ┌─────────────┐                   │
│  │   Client    │     │   Client    │     │   Client    │                   │
│  │ ┌─────────┐ │     │ ┌─────────┐ │     │ ┌─────────┐ │                   │
│  │ │WebAudio │ │     │ │WebAudio │ │     │ │WebAudio │ │                   │
│  │ │  API    │ │     │ │  API    │ │     │ │  API    │ │                   │
│  │ └─────────┘ │     │ └─────────┘ │     │ └─────────┘ │                   │
│  │ ┌─────────┐ │     │ ┌─────────┐ │     │ ┌─────────┐ │                   │
│  │ │  Yjs    │◄├─────┼─┤  Yjs    │◄├─────┼─┤  Yjs    │ │                   │
│  │ │ (CRDT)  │ │     │ │ (CRDT)  │ │     │ │ (CRDT)  │ │                   │
│  │ └─────────┘ │     │ └─────────┘ │     │ └─────────┘ │                   │
│  └──────┬──────┘     └──────┬──────┘     └──────┬──────┘                   │
│         │                   │                   │                          │
│         └───────────────────┼───────────────────┘                          │
│                             │                                              │
│                    ┌────────▼────────┐                                     │
│                    │    LiveKit      │                                     │
│                    │  (WebRTC SFU)   │                                     │
│                    │                 │                                     │
│                    │ • Audio routing │                                     │
│                    │ • Low latency   │                                     │
│                    │ • Room mgmt     │                                     │
│                    └─────────────────┘                                     │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Technology Choices

| Component | Technology | Why |
|-----------|------------|-----|
| **Audio Transport** | [LiveKit](https://livekit.io) | Open-source WebRTC SFU, <100ms latency, scales well |
| **Audio Processing** | Web Audio API | In-browser synthesis, effects chain |
| **Pattern State** | [Yjs](https://yjs.dev) | CRDT for conflict-free merging |
| **Signaling** | WebSocket (via LiveKit) | Built-in with LiveKit |
| **Persistence** | IndexedDB + Server | Offline-first with sync |

### Alternative: JackTrip WebRTC

For **uncompressed, ultra-low-latency** audio:
- [JackTrip-webrtc](https://github.com/JackTrip-webrtc/JackTrip-webrtc)
- Higher bandwidth, lower latency (~10-20ms)
- Best for serious music production

### Data Model (Yjs)

```javascript
// Shared pattern state using Yjs
const ydoc = new Y.Doc()

// Patterns as shared map
const patterns = ydoc.getMap('patterns')

// Each pattern is a shared array of events
patterns.set('aphex-drill', new Y.Array())

// Add event collaboratively
patterns.get('aphex-drill').push([{
  type: 'note',
  pitch: 60,
  duration: 0.25,
  user: 'alice'  // Track who added it
}])

// Conflicts auto-resolve via CRDT
```

### Integration with Music Topos

```ruby
# lib/collaborative/pattern_sync.rb

class PatternSync
  def initialize(yjs_doc)
    @doc = yjs_doc
    @patterns = @doc.get_map('patterns')
  end
  
  # Convert Yjs state to Free Monad pattern
  def to_pattern(pattern_id)
    events = @patterns.get(pattern_id).to_a
    
    FreeMonad::Suspend.new(
      FreeMonad::Sequence.new(
        events.map { |e| event_to_instruction(e) }
      )
    )
  end
  
  # Add local change
  def add_event(pattern_id, event)
    @patterns.get(pattern_id).push([event])
    # Yjs handles sync automatically
  end
end
```

---

## 2. Multi-Participant Visualization Sharing

**Goal:** Users viewing and interacting with dashboards with shared state

### Technical Requirements

- **Latency:** <200ms acceptable
- **State:** Complex nested objects (color palettes, pattern params)
- **Presence:** See who's viewing/editing what
- **Cursors:** Optional shared cursor positions

### Recommended Stack

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      VISUALIZATION SHARING STACK                            │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌──────────────────────────────────────────────────────────────────────┐  │
│  │                           Frontend (Svelte/React)                     │  │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  │  │
│  │  │   Canvas    │  │   Pattern   │  │   Color     │  │  Presence   │  │  │
│  │  │  Renderer   │  │   Editor    │  │   Picker    │  │  Avatars    │  │  │
│  │  └─────────────┘  └─────────────┘  └─────────────┘  └─────────────┘  │  │
│  └──────────────────────────────────────────────────────────────────────┘  │
│                                    │                                        │
│                           ┌────────▼────────┐                              │
│                           │       Yjs       │                              │
│                           │  ┌───────────┐  │                              │
│                           │  │ Awareness │  │  ← Cursor/presence          │
│                           │  └───────────┘  │                              │
│                           │  ┌───────────┐  │                              │
│                           │  │ Y.Map     │  │  ← Shared state              │
│                           │  └───────────┘  │                              │
│                           └────────┬────────┘                              │
│                                    │                                        │
│                           ┌────────▼────────┐                              │
│                           │  y-websocket    │                              │
│                           │    Provider     │                              │
│                           └────────┬────────┘                              │
│                                    │                                        │
│                           ┌────────▼────────┐                              │
│                           │   Hocuspocus    │  ← Or y-websocket server     │
│                           │    (Server)     │                              │
│                           └─────────────────┘                              │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### State Structure

```javascript
// Yjs document for visualization
const ydoc = new Y.Doc()

// Current view state
const viewState = ydoc.getMap('view')
viewState.set('currentPattern', 'aphex-drill')
viewState.set('tempo', 140)
viewState.set('colorSeed', 42)

// Gay.jl color palette (shared)
const palette = ydoc.getArray('colorPalette')

// Awareness (cursors, selections)
const awareness = new awarenessProtocol.Awareness(ydoc)
awareness.setLocalStateField('user', {
  name: 'alice',
  color: '#A855F7',
  cursor: { x: 100, y: 200 }
})
```

### Server Options

| Server | Pros | Cons |
|--------|------|------|
| **y-websocket** | Simple, included with Yjs | Basic features |
| **Hocuspocus** | Auth, webhooks, persistence | Heavier |
| **PartyKit** | Edge-deployed, scalable | Vendor lock-in |
| **Liveblocks** | Full-featured, presence | Commercial |

---

## 3. Research Streaming/Demos

**Goal:** Broadcasting speaker + screenshare to viewers

### Technical Requirements

- **Latency:** 1-5 seconds acceptable
- **Scale:** 1 broadcaster → 1000+ viewers
- **Quality:** High (720p/1080p screen, clear audio)
- **Interaction:** Chat, Q&A

### Recommended Stack

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         STREAMING ARCHITECTURE                              │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────┐                                                           │
│  │ Broadcaster │                                                           │
│  │ ┌─────────┐ │     WebRTC          ┌─────────────────┐                   │
│  │ │ Camera  │─┼────────────────────►│                 │                   │
│  │ └─────────┘ │                     │    LiveKit      │     HLS/DASH      │
│  │ ┌─────────┐ │     WebRTC          │    (Egress)     │───────────────┐   │
│  │ │ Screen  │─┼────────────────────►│                 │               │   │
│  │ └─────────┘ │                     │                 │               │   │
│  │ ┌─────────┐ │     WebRTC          │  • Transcode    │               │   │
│  │ │  Mic    │─┼────────────────────►│  • Package      │               │   │
│  │ └─────────┘ │                     │  • Distribute   │               │   │
│  └─────────────┘                     └─────────────────┘               │   │
│                                              │                         │   │
│                                              │ WebRTC                  │   │
│                                              │ (low latency)           │   │
│                                              ▼                         ▼   │
│                                      ┌─────────────┐           ┌──────────┐│
│                                      │  Viewers    │           │ Viewers  ││
│                                      │  (VIP/Q&A)  │           │ (Scale)  ││
│                                      │  <500ms     │           │  ~5s     ││
│                                      └─────────────┘           └──────────┘│
│                                                                             │
│  ┌──────────────────────────────────────────────────────────────────────┐  │
│  │                              Chat Layer                               │  │
│  │                  (WebSocket / Yjs for real-time)                      │  │
│  └──────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Technology Choices

| Scenario | Technology | Latency | Scale |
|----------|------------|---------|-------|
| **Interactive demo** | LiveKit WebRTC | <500ms | ~100 |
| **Large broadcast** | LiveKit → HLS | 2-5s | 10,000+ |
| **Hybrid** | WebRTC for Q&A, HLS for viewers | Mixed | Mixed |

### Simple Setup (Jitsi)

For quick demos without infrastructure:

```bash
# Just use Jitsi Meet
open https://meet.jit.si/music-topos-demo
```

Pros: Zero setup, end-to-end encrypted, screen sharing built-in
Cons: Less customizable, limited to ~75 participants

---

## 4. Custom Multi-Modal Research Platform

**Goal:** Integration with category theory/color/music systems

### Architecture Vision

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    MULTI-MODAL RESEARCH PLATFORM                            │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌──────────────────────────────────────────────────────────────────────┐  │
│  │                         Web Frontend                                  │  │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  │  │
│  │  │   Pattern   │  │   Audio     │  │   Color     │  │  Diagram    │  │  │
│  │  │   Editor    │  │   Stream    │  │   Palette   │  │  Renderer   │  │  │
│  │  │  (Monaco)   │  │  (WebAudio) │  │  (Gay.jl)   │  │  (Mermaid)  │  │  │
│  │  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘  │  │
│  │         │                │                │                │         │  │
│  │         └────────────────┴────────────────┴────────────────┘         │  │
│  │                                  │                                    │  │
│  │                         ┌────────▼────────┐                          │  │
│  │                         │   Shared State  │                          │  │
│  │                         │      (Yjs)      │                          │  │
│  │                         └────────┬────────┘                          │  │
│  └──────────────────────────────────┼───────────────────────────────────┘  │
│                                     │                                       │
│                            ┌────────▼────────┐                             │
│                            │    WebSocket    │                             │
│                            │    + LiveKit    │                             │
│                            └────────┬────────┘                             │
│                                     │                                       │
│  ┌──────────────────────────────────┼───────────────────────────────────┐  │
│  │                         Backend Services                              │  │
│  │  ┌─────────────┐  ┌─────────────┼─────────────┐  ┌─────────────┐     │  │
│  │  │   Pattern   │  │    State    │   Audio     │  │    Color    │     │  │
│  │  │   Engine    │  │    Sync     │   Render    │  │    Engine   │     │  │
│  │  │   (Ruby)    │  │  (y-server) │   (SC/FFI)  │  │   (Ruby)    │     │  │
│  │  │             │  │             │             │  │             │     │  │
│  │  │ Free Monad  │  │  Hocuspocus │ SuperCollider│  │  Gay.jl    │     │  │
│  │  │ → Events    │  │             │ AudioSynth   │  │  Client     │     │  │
│  │  └──────┬──────┘  └─────────────┴─────────────┘  └──────┬──────┘     │  │
│  │         │                                               │            │  │
│  │         └───────────────────────┬───────────────────────┘            │  │
│  │                                 │                                     │  │
│  │                        ┌────────▼────────┐                           │  │
│  │                        │    PostgreSQL   │                           │  │
│  │                        │   (Sessions,    │                           │  │
│  │                        │    Patterns)    │                           │  │
│  │                        └─────────────────┘                           │  │
│  └──────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Modality Integration

```javascript
// Unified state for all modalities
const ydoc = new Y.Doc()

// Pattern (Free Monad serialized)
const pattern = ydoc.getMap('pattern')
pattern.set('type', 'aphex-drill')
pattern.set('duration', 8.0)
pattern.set('intensity', 0.7)

// Color (Gay.jl state)
const color = ydoc.getMap('color')
color.set('seed', 42)
color.set('index', 0)
color.observe(() => {
  // When color changes, update music
  const params = colorToMusicParams(color.toJSON())
  updatePatternFromColor(pattern, params)
})

// Diagram (category theory visualization)
const diagram = ydoc.getMap('diagram')
diagram.set('mermaid', `
  graph LR
    A[Pattern] -->|runs on| B[Matter]
    B --> C[Events]
`)

// Audio state (playback position, etc.)
const audio = ydoc.getMap('audio')
audio.set('playing', false)
audio.set('position', 0)
```

### Cross-Modal Reactions

```ruby
# When pattern changes → update color
pattern.on_change do |new_pattern|
  # Extract hue from pattern's dominant pitch
  dominant_pitch = new_pattern.dominant_pitch_class
  hue = dominant_pitch * 30  # 30° per semitone
  
  color.set('hue_override', hue)
end

# When color changes → suggest pattern modification
color.on_change do |new_color|
  params = GayNeverending::ColorMusicMapper.color_to_params(new_color)
  
  # Update pattern parameters (non-destructive)
  pattern.set('suggested_tempo', params[:tempo_mod] * pattern.get('tempo'))
  pattern.set('suggested_density', params[:density])
end
```

---

## Comparison Matrix

| Criteria | LiveKit | Jitsi | y-websocket | Custom WS |
|----------|---------|-------|-------------|-----------|
| **Audio latency** | ~50-100ms | ~100-200ms | N/A | N/A |
| **State sync** | Limited | Limited | Excellent | Manual |
| **Scale** | 1000s | ~75 | 100s | Variable |
| **Self-host** | Yes | Yes | Yes | Yes |
| **Complexity** | Medium | Low | Low | High |
| **Cost** | Free/Cloud | Free | Free | Dev time |

---

## Recommended Implementation Path

### Phase 1: Visualization Sharing (Easiest)

1. Add Yjs to existing frontend
2. Use y-websocket server
3. Share pattern parameters + color state
4. Add presence indicators

**Effort:** 1-2 weeks

### Phase 2: Research Streaming

1. Self-host Jitsi or use LiveKit Cloud
2. Add screen sharing for demos
3. Integrate chat with Yjs

**Effort:** 1 week (Jitsi) / 2-3 weeks (LiveKit)

### Phase 3: Real-time Music Collaboration

1. Add LiveKit for audio
2. Sync pattern state via Yjs
3. Handle conflict resolution
4. Low-latency audio routing

**Effort:** 4-6 weeks

### Phase 4: Full Multi-Modal Platform

1. Unify all state in Yjs
2. Cross-modal reactions
3. Custom audio rendering
4. Diagram/visualization sync

**Effort:** 2-3 months

---

## Resources

- [LiveKit Docs](https://docs.livekit.io/)
- [Yjs Docs](https://docs.yjs.dev/)
- [Jitsi Self-Hosting](https://jitsi.github.io/handbook/)
- [Hocuspocus Server](https://tiptap.dev/hocuspocus/)
- [JackTrip WebRTC](https://github.com/JackTrip-webrtc/JackTrip-webrtc)
- [Web Audio API](https://developer.mozilla.org/en-US/docs/Web/API/Web_Audio_API)
