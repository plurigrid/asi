# BANUKA Phase Scheduler Sonification - Quick Start

**Get running in 5 minutes**

## 1. Check Prerequisites

```bash
# Verify Clojure installation
clj -version
# Should show: Clojure CLI version 1.12.4.1602+

# Verify Java
java -version
# Should show Java 11 or newer
```

## 2. Enter Project Directory

```bash
cd /Users/bob/i/asi/ies/music-topos
```

## 3. Start the Sonification REPL

```bash
# Option A: Using Clojure CLI (recommended)
clj -M:sonification -m music-topos.repl

# Option B: Start REPL and load manually
clj
(require '[music-topos.repl :as repl])
```

## 4. Run Your First Demo (in REPL)

```clojure
;; Print help
(repl-help)

;; Show configuration
(show-configuration)

;; Start the audio engine
(start-phase-sonification)

;; Run simple phase demo
(demo-simple-phases)

;; Stop the engine
(stop-phase-sonification)
```

## 5. Send Your Own Phase Events

```clojure
;; Initialize if not already done
(start-phase-sonification)

;; Send a phase event
(send-phase-event :phase-3-synthesis :running
                  :intensity 0.7
                  :duration 1.0
                  :resource-usage 0.6)

;; Send another phase event
(send-phase-event :phase-4-learning :running
                  :intensity 0.8
                  :duration 1.2
                  :resource-usage 0.75)
```

## Available Commands

| Command | Purpose |
|---------|---------|
| `(repl-help)` | Show all available commands |
| `(start-phase-sonification)` | Initialize and start audio engine |
| `(stop-phase-sonification)` | Gracefully shutdown |
| `(send-phase-event phase state :intensity I :duration D :resource-usage R)` | Send phase event |
| `(demo-simple-phases)` | Play phases sequentially |
| `(demo-resource-sweep)` | Vary resource utilization |
| `(demo-phase-transitions)` | Show phase transitions |
| `(show-phase-map)` | Display frequency mapping |
| `(show-state-map)` | Display state→timbre mapping |
| `(show-configuration)` | Show all configuration |
| `(print-server-status)` | Check audio server status |

## Phase Keywords

```clojure
:phase-0-initialization
:phase-1-parsing
:phase-2-analysis
:phase-3-synthesis
:phase-4-learning
:phase-5-validation
:phase-6-deployment
```

## State Keywords

```clojure
:queued      ; Task is queued
:running     ; Task is executing
:blocked     ; Task is blocked/waiting
:completed   ; Task completed successfully
:failed      ; Task failed
```

## Example: Monitor Phase Scheduler

```clojure
;; Start sonification
(start-phase-sonification)

;; Simulate scheduler activity
(doseq [i (range 5)]
  (send-phase-event :phase-2-analysis :running
                    :intensity (rand) :duration 1.0 :resource-usage (rand))
  (Thread/sleep 1500))

;; Stop
(stop-phase-sonification)
```

## Example: Custom Phase Event

```clojure
;; Send event with custom parameters
(send-phase-event :phase-5-validation :running
                  :intensity 0.9        ; High computational load
                  :duration 2.0         ; 2 second event
                  :resource-usage 0.85) ; High resource usage
```

## Troubleshooting

**Can't connect to audio server:**
```clojure
(print-server-status)
; If `:fallback` mode, make sure SuperCollider is running
; Or use fake server mode - already built-in!
```

**REPL won't start:**
```bash
# Clear any stuck processes
pkill -f nrepl

# Try again
clj -M:sonification -m music-topos.repl
```

**No audio output:**
- Check volume settings
- Verify SuperCollider running: `ps aux | grep scsynth`
- Try demo: `(demo-simple-phases)`

## Next Steps

1. Explore phase mappings: `(show-phase-map)`
2. Create custom phase events
3. Integrate with your phase scheduler
4. Record sonification output
5. Build reactive visualizations

## File Locations

- **Main engine:** `/Users/bob/i/asi/ies/music-topos/src/music_topos/phase_scheduler_sonification.clj`
- **REPL utilities:** `/Users/bob/i/asi/ies/music-topos/src/music_topos/repl.clj`
- **Synth definitions:** `/Users/bob/i/asi/ies/music-topos/resources/banuka-synths.scd`
- **Configuration:** `/Users/bob/i/asi/ies/music-topos/deps.edn`

## Status

✓ Clojure 1.11.1 installed
✓ Overtone 1.0.0 configured
✓ Phase scheduler sonification ready
✓ REPL with CIDER support configured
✓ SuperCollider synth definitions prepared

**Ready to sonify BANUKA phase scheduler execution!**
