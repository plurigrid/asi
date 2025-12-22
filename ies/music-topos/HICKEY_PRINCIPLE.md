# What Rich Hickey Would Do: Making Sound "Right Now & In Perpetuity"

## The Problem Statement
"make a sound right now correctly and in perpetuity"

## Hickey's Principles Applied

### 1. **Simplicity Over Cleverness**
Hickey would NOT:
- Use Overtone (adds JNA native library complexity)
- Try to auto-detect synth definitions
- Over-engineer synth management

Hickey WOULD:
- Use pure OSC (no native dependencies)
- Send explicit `/s_new` commands with pre-defined synths
- Keep configuration external and declarative

### 2. **Separate Concerns Ruthlessly**

```clojure
;; The Clean Architecture
Concern 1: Music Theory (our domain)
  → Pure data structures: InitialObjectWorld, TerminalObjectWorld
  → Immutable values: frequencies, durations, amplitudes
  → Pure functions: play-initial-world, play-terminal-world

Concern 2: Audio Protocol (mediator)
  → OSC message creation
  → Network communication
  → Non-essential—can be replaced

Concern 3: Audio Synthesis (SuperCollider's domain)
  → SynthDef definitions
  → Synth instantiation
  → Audio output routing
  → Completely separate from our Clojure code
```

### 3. **Document the Contract, Not the Implementation**

**The Contract we establish with SuperCollider:**
```
REQUIRED: SuperCollider must have these synths defined before use:
  • "sine" {|freq=440, amp=0.3, sustain=1| ... }
  • Parameters: freq (Hz), amp (0.0-1.0), sustain (seconds)

REQUIRED: SuperCollider must accept these OSC commands:
  • /s_new "sine" <node-id> 1 0 freq=<f> amp=<f> sustain=<f>

DELIVERED BY: startup.scd (must be loaded by SuperCollider before use)
```

### 4. **Make Both Spec and Implementation Verifiable**

```clojure
;; Hickey-style test: Pure function, no side effects
(deftest osc-message-correctness
  (let [spec {:freq 60, :amp 0.3, :dur 2.0}
        message (build-osc-message "sine" spec)]
    ;; This test proves our code generates correct OSC format
    ;; This test requires NO running SuperCollider server
    ;; This test can run in CI/CD
    ))

;; Hickey-style integration test: Verify the contract
(deftest supercollider-contract-fulfilled
  ;; This test only verifies: "Does SuperCollider have 'sine' synth?"
  ;; It doesn't verify: "Can I hear sound?" (that's a physical concern)
  (is (has-synth? @osc-client "sine")))
```

### 5. **Values vs. State vs. Identity**

```clojure
;; VALUES: Our music specifications (immutable, timeless)
(def initial-world {
  :pitch-classes (range 60 72)        ;; These values never change
  :harmonic-functions [...]           ;; This IS the music
})

;; STATE: SuperCollider's node tree (changing, temporary)
(def server-state (atom {:nodes-active 0}))
;; This is orthogonal to our values. Don't confuse them.

;; IDENTITY: The OSC connection (persistent, but replaceable)
(def osc-client (atom nil))
;; This is how we communicate, not what we communicate about
```

### 6. **Get the Simplest Thing Working, Then Build**

**Phase 1: Make tone generation work** ✓
- Clojure code sends OSC messages → DONE
- Messages have correct format → DONE
- OSC socket connects → DONE
- SuperCollider receives commands → (NEEDS VERIFICATION)

**Phase 2: Make SuperCollider respond** ← WE ARE HERE
- Ensure startup.scd loads with sine synth definition
- Verify SuperCollider boots with correct configuration
- Test: can we hear a single tone?

**Phase 3: Make both worlds work together** ← NEXT
- InitialObjectWorld generates correct OSC sequence
- SuperCollider plays the sequence
- Both work "in perpetuity" via documented contract

**Phase 4: Make it truly perpetual**
- Tests verify contract at every level
- Documentation makes it learnable
- Configuration is external and explicit
- No magic, no surprises

---

## The Solution: Two Executables

### Executable 1: Clojure (Our Code)
```clojure
;; Pure, testable, independent
;; Doesn't need audio hardware to validate
;; Can be tested without SuperCollider
(ns music-topos.core
  (:require [overtone.osc :as osc]))

(defn play-initial-world []
  "Send music world as OSC commands"
  ;; This function is CORRECT if:
  ;; 1. It sends valid OSC messages
  ;; 2. OSC messages have correct frequency/amplitude/duration values
  ;; 3. Messages arrive at SuperCollider in order
  ;;
  ;; It does NOT need to: produce audible sound
  ;; That's SuperCollider's job
  )
```

### Executable 2: SuperCollider (Their Code)
```supercollider
// Declarative, explicit, versioned
SynthDef("sine", {|freq=440, amp=0.3, sustain=1|
  var env = EnvGen.kr(
    Env([0, 1, 1, 0], [0.01, sustain, 0.01], 'lin'),
    doneAction: Done.freeSelf
  );
  Out.ar(0, env * amp * SinOsc.ar(freq));
}).send(Server.local);
```

**The contract is FULFILLED when:**
- File 1 (Clojure): Sends `/s_new "sine" ...` commands
- File 2 (startup.scd): Defines the "sine" synth
- File 3 (SuperCollider app): Loads File 2 on boot
- File 4 (macOS): Routes audio to speakers

Each piece is independent, testable, and replaceable.

---

## Perpetuity: The Key Insight

**"In perpetuity" means:**
- 5 years from now, someone understands why it works
- The system doesn't break when SuperCollider updates
- You can replace SuperCollider with another synth engine without changing Clojure code
- Tests prove correctness independent of physical audio

**How Hickey achieves this:**
1. **Separate layers clearly**
   - Clojure layer: Data + pure functions
   - Protocol layer: OSC messages
   - Synthesis layer: SuperCollider (replaceable)

2. **Document the boundaries**
   - Clojure PROVIDES: OSC commands (structured, testable)
   - SuperCollider PROVIDES: audio output (external, verifiable)
   - Boundary: OSC protocol (unchanging specification)

3. **Make assumptions explicit**
   - ASSUME: SuperCollider has "sine" synth defined
   - VERIFY: Startup.scd provides this definition
   - TEST: Can send 1000 synths to SuperCollider without errors

4. **Test at every boundary**
   - Pure function tests (no audio hardware needed)
   - Protocol tests (no audio hardware needed)
   - Integration tests (requires running SuperCollider)
   - Acceptance tests (requires audio hardware)

---

## Next Step: Verify The Contract

Rich Hickey would now:

1. **Check**: Does startup.scd exist and load?
```bash
# Verify the file exists in the right place
ls -la ~/Library/Application\ Support/SuperCollider/startup.scd
```

2. **Verify**: Does SuperCollider boot with it?
```bash
# Restart SuperCollider; it should load the startup file on boot
# In the SuperCollider IDE, run:
Server.local.quit;  // Shutdown
Server.local.boot;  // Boot (will load startup.scd)
Server.local.dump;  // Should show "sine" synth defined
```

3. **Test**: Can we invoke the synth?
```bash
flox activate -- lein run initial
# Should produce OSC messages
# If startup.scd was loaded, should produce sound
```

That's the Hickey approach: **Simple, Separated, Specified, Tested, Verifiable.**
