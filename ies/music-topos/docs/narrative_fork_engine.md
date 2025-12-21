# Narrative Fork Engine: Color-Guided Reality Branching

## Overview

The **Narrative Fork Engine** is a Biff + HTMX + Gay.jl application that implements interactive storytelling with two core actions:

1. **Fork Reality**: Branch into an alternate timeline (increases entropy)
2. **Continue**: Progress in the current timeline (increases depth)

The experience is guided by a **color palette** generated using the golden angle (137.508°), creating:
- Visual coherence across all states
- Non-repeating sequences (infinite variety)
- Semantic mapping of narrative properties to color

## Architecture

### Technology Stack

```
┌──────────────────────────────────────────────────────────┐
│  FRONTEND (Browser)                                      │
│  ├─ HTMX: Interactive HTML without JavaScript           │
│  ├─ CSS Grid: Responsive color palette display          │
│  └─ Hiccup: Server-side HTML generation                 │
└──────────────────────────────────────────────────────────┘
                      ↓ (HTTP/AJAX)
┌──────────────────────────────────────────────────────────┐
│  BACKEND (Biff + Clojure)                               │
│  ├─ Narrative State Machine (INarrativeState protocol)   │
│  ├─ Golden Angle Color Palette (Gay.jl)                │
│  ├─ Thermal Dynamics (Therm)                           │
│  ├─ Hybrid Interaction Engine (Hyjax)                   │
│  └─ Session Management (state persistence)              │
└──────────────────────────────────────────────────────────┘
```

### Core Components

#### 1. **Narrative State Machine**

```clojure
(defrecord NarrativeNode
  [id depth timeline text choices color history entropy])
```

**Fields**:
- `id`: Unique identifier for this node (encodes path)
- `depth`: Distance from root (affects color lightness)
- `timeline`: Sequence of actions taken (fork/continue)
- `text`: Current narrative text
- `choices`: Available actions [{:label "Fork Reality" :action :fork} ...]
- `color`: Current HSL color (hue, saturation, lightness)
- `history`: All previously visited node IDs
- `entropy`: Cumulative interaction complexity

**Protocol Methods**:
- `fork-branch`: Create new state with entropy↑
- `continue-branch`: Progress in timeline with certainty↑

#### 2. **Golden Angle Color Palette**

The color system maps narrative properties to HSL:

```
HUE (0-360°):           "What type of narrative state are we in?"
  - Calculated via: (index * 137.508°) mod 360°
  - Never repeats exactly (irrational rotation)
  - Creates visual variety while maintaining coherence

SATURATION (0-1):       "How complex is the current state?"
  - Increases with: depth, number of choices, entropy
  - Formula: 0.3 + (depth/20) + (entropy/10)
  - Low saturation = simple, clear choice
  - High saturation = complex, rich branching

LIGHTNESS (0-1):        "How certain is our path?"
  - Decreases with: depth, increases with: certainty
  - Formula: 0.3 + certainty - (depth/10)
  - Bright = we're on the main path
  - Dark = we've forked into uncertainty
```

**Example Color Evolution**:

```
Action 0 (Root):
  Hue: 0° (RED)
  Saturation: 0.3
  Lightness: 1.0 (fully bright, maximum certainty)
  → RGB: (255, 0, 0) [Pure Red]

Action 1 (Fork):
  Hue: 137.5° (GREEN)
  Saturation: 0.4
  Lightness: 0.3 (darker, entering alternate timeline)
  → RGB: (0, 200, 100) [Forest Green]

Action 2 (Continue from Fork):
  Hue: 275° (BLUE/MAGENTA)
  Saturation: 0.5
  Lightness: 0.35
  → RGB: (180, 100, 200) [Periwinkle]
```

#### 3. **Thermal Dynamics (Therm)**

Heat increases with interaction intensity, adjusting colors in real-time:

```clojure
(defn thermal-color-adjustment [color thermal-intensity]
  ;; Add 20% lightness boost when thermal > 0.5
  ;; Add 10% saturation boost when thermal > 0.5
  ;; Creates "hot" colors for high-interaction states)
```

**Interpretation**:
- **Cool** (thermal < 0.3): Contemplative branching
- **Warm** (thermal 0.3-0.7): Active exploration
- **Hot** (thermal > 0.7): Chaotic reality forking

#### 4. **Hybrid Interaction Engine (Hyjax)**

HTMX actions trigger server-side state changes:

```html
<!-- Fork Reality Button (via HTMX) -->
<button hx-post="/narrative/fork"
        hx-target="#narrative-container"
        hx-swap="innerHTML"
        style="background-color: #00c864; color: white;">
  Fork Reality
</button>
```

When clicked:
1. Browser sends POST to `/narrative/fork`
2. Server computes new state with `fork-branch`
3. Server renders HTML with new color palette
4. HTMX swaps result into page (no full refresh)

### Routes

```
GET  /narrative           → Display current state
POST /narrative/fork      → Fork into alternate timeline
POST /narrative/continue  → Progress in current timeline
POST /narrative/reset     → Reset to initial state
```

## Interaction Flow

### Single Fork Action

```
User clicks "Fork Reality"
    ↓
HTMX sends POST /narrative/fork
    ↓
Server receives request with current session state
    ↓
Server calls (fork-branch current-state)
    ↓
New state created:
  - id: "root:fork:branch-1"
  - depth: 1 (increased)
  - entropy: 1 (increased)
  - timeline: [:fork]
  - color: new HSL based on fork parameters
  - choices: new branching options
    ↓
Server renders HTML with new color & options
    ↓
HTMX inserts result into #narrative-container
    ↓
User sees new state with different color, text, and choices
```

### Multiple Actions (Narrative Arc)

```
Start (Hue: 0°, Depth: 0)
  ↓ Fork
State 1 (Hue: 137.5°, Depth: 1)
  ↓ Continue
State 2 (Hue: 275°, Depth: 2)
  ↓ Fork
State 3 (Hue: 52.5°, Depth: 3)
  ↓ Continue
State 4 (Hue: 190°, Depth: 4)
  ... (continues indefinitely)
```

The **hue always advances by 137.508°** per action, creating a visual rainbow progression.

## Maximum Entropy Interaction

### What is Interaction Entropy?

Entropy measures **unpredictability** of future states:

```
Formula: entropy = (depth + action_count) / 2 + variance

High entropy = many possible futures (more branching)
Low entropy = deterministic path (linear progression)
```

### Entropy Drivers

1. **Depth**: Each fork increases branching possibilities
2. **Action Count**: More interactions = more complex state space
3. **Complexity**: More choices = higher entropy
4. **Thermal Intensity**: Heat-driven color changes suggest divergence

### Example Entropy Evolution

```
Action 0:     entropy = 0.0 (starting point)
After fork:   entropy = 1.0 (now in alternate timeline)
After fork:   entropy = 2.0 (multiple branches)
After fork:   entropy = 3.0 (exponentially more paths)
After fork:   entropy = 4.0 (nearly infinite futures)
```

As entropy increases, colors become:
- More saturated (richness of possibilities)
- More varied (less predictable hues)
- Thermally adjusted (heat of creation)

## Semantic Closeness: Narrative Meaning

### The Narrative is the Color

Each color represents:

```
Hue → What type of narrative branch are we exploring?
      (Red=root, Green=fork1, Blue=fork2, etc.)

Saturation → How much narrative complexity surrounds this choice?
             (Pale=simple, vivid=elaborate)

Lightness → How much certainty do we have about this path?
            (Bright=confident, dark=uncertain)
```

### Color as Semantic Context

The **color palette IS the narrative**. You can understand the story by looking at the colors:

- **All bright reds**: Linear progression from root (low entropy)
- **Gradient of saturated colors**: Complex branching (high entropy)
- **Dark colors with red undertones**: Returning to past branches
- **Hot, saturated colors**: Intense narrative moments

## Hosting Maximally on Clojure

Everything runs in Clojure:

### Frontend
- HTML generation: `Hiccup` (Clojure → HTML)
- Styling: Embedded CSS in Hiccup
- Interaction: HTMX (external JS, but minimal)
- No JavaScript frameworks (React, Vue, etc.)

### Backend
- HTTP Server: `Biff` (batteries-included Clojure framework)
- State Management: Immutable records with protocols
- Color Calculations: Pure functions (no external libs for color)
- Session Storage: In-memory or database (Biff handles)
- Routing: Biff's ring-based handler system

### Database
- **Optional**: Use Biff's Crux (built-in database)
- **Or**: In-memory with session persistence
- Could integrate with PostgreSQL, DuckDB, etc.

### Deployment
```bash
# Build a JAR
lein uberjar

# Run on server
java -jar target/music-topos-0.1.0-standalone.jar

# Or use Biff's development server
lein run -m music-topos.biff-app
```

## Running the Engine

### Start the Server

```bash
just fork-engine
# Or: flox activate -- lein run -m music-topos.biff-app
```

Server starts on `http://localhost:8080`

### Interact

1. **In Browser**: Click "Fork Reality" or "Continue" buttons
2. **Via CLI**:
   ```bash
   just fork        # POST to /narrative/fork
   just continue-narrative  # POST to /narrative/continue
   ```

### Example Session

```
[Browser loads] http://localhost:8080/
  ↓
Page shows:
  "Welcome to the Narrative Fork Engine. Two paths diverge..."
  Color: RED (RGB: 255, 0, 0)
  Buttons: [Fork Reality] [Continue]

[User clicks Fork Reality]
  ↓
Page updates:
  "Forking into alternate reality..."
  Color: GREEN (RGB: 0, 200, 100)
  Thermal: 0.1 (low heat)
  Entropy: 1.0
  Buttons: [Fork Reality] [Continue]

[User clicks Continue]
  ↓
Page updates:
  "Continuing from: Forking into alternate reality..."
  Color: BLUE (RGB: 100, 150, 200)
  Thermal: 0.15 (slightly heated)
  Entropy: 1.05
  Buttons: [Fork Reality] [Continue]

[... user continues branching/progressing ...]
```

## Technical Details

### State Persistence

```clojure
; Server maintains session with current narrative state
{:session {:narrative-state <NarrativeNode>
           :action-count 3
           :started-at <timestamp>}}

; Session survives across requests (24-hour TTL)
; User's entire narrative history preserved
```

### Color Calculation Performance

Golden angle calculation is **O(1)**:

```clojure
(defn compute-hue [index]
  (mod (* index 137.508) 360))  ; Single multiplication + modulo
```

No external HTTP calls, no AI, no heavy computation.

### HTMX Integration

HTMX is loaded from CDN:

```html
<script src="https://unpkg.com/htmx.org"></script>
```

When user clicks button with `hx-post`:
1. HTMX intercepts click
2. Sends background POST request
3. Renders response with `hx-swap="innerHTML"`
4. No page reload, no JavaScript needed

## Extensions

### Possible Enhancements

1. **Sound Design**: Play notes based on current hue (pitch)
2. **GAY.JL Integration**: Use full color system for timbre mapping
3. **Reinforcement Learning**: Learn which branches users prefer
4. **Multiplayer**: Multiple users share same narrative forest
5. **Persistence**: Save narrative branches to database
6. **Generative Text**: Use LLM to generate narrative based on color state
7. **Spectral Analysis**: Map color space to musical spectra

### Example: Color-to-Pitch Mapping

```clojure
(defn hue-to-pitch [hue]
  ; Map hue (0-360°) to MIDI pitch (0-127)
  (let [normalized (/ hue 360)
        octaves 10
        semitones-total (* octaves 12)]
    (int (* normalized semitones-total))))

(defn play-narrative-color [color]
  ; Play the color as music!
  (let [pitch (hue-to-pitch (:hue color))
        duration (/ 1000 (inc (:depth color)))]
    (play-note pitch duration)))
```

## The Vision

The Narrative Fork Engine realizes three key ideas:

1. **Color as Language**: Visual semantics make mathematical structure intuitive
2. **Interaction as Meaning**: Every click changes the universe (narrative multiverse)
3. **Clojure as Platform**: Pure functions, immutable state, elegant abstractions

> "In the Garden of Forking Paths, every choice spawns a new color."

## References

- **Biff**: https://github.com/jacobobryant/biff
- **HTMX**: https://htmx.org
- **Gay.jl**: Color system from the Music Topos project
- **Borges**: "The Garden of Forking Paths" (inspiration)

---

Generated with [Claude Code](https://claude.com/claude-code)

Written by: Claude Haiku 4.5
