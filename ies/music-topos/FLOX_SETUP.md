# Flox Setup: Reproducible Music Topos Environment

**Flox** = Declarative environment manager
**Purpose**: Set up complete audio testing environment automatically

---

## What Flox Does

Flox creates isolated development environments with all dependencies:
- Ruby 3.2
- Sonic Pi (audio synthesizer)
- Testing tools
- Audio utilities

**Benefits**:
- ✓ Same environment for everyone
- ✓ Automatic Sonic Pi setup
- ✓ No manual installation
- ✓ Automated testing on activation
- ✓ Reproducible results

---

## Installation

### Step 1: Install Flox

```bash
# macOS
brew install flox

# Or download from:
# https://flox.dev/get-started
```

### Step 2: Create Flox Account (Optional)

```bash
flox login
```

Or use offline:

```bash
flox activate -e dev --no-remote
```

---

## Usage

### Development Environment

```bash
cd /Users/bob/ies/music-topos

# Enter the dev environment
flox activate -e dev
```

**On activation:**
- ✓ Ruby 3.2 available
- ✓ Sonic Pi installed
- ✓ All tools ready
- ✓ Instructions displayed

**Then:**
```bash
# Option 1: Interactive composition
ruby bin/interactive_repl.rb

# Option 2: Run automated demo
ruby bin/just_play.rb

# Option 3: Verify mathematics
ruby bin/ontological_verification.rb
```

---

### Testing Environment

```bash
# Enter test environment
flox activate -e test
```

**On activation:**
- ✓ Checks if Sonic Pi is running
- ✓ Runs automated tests automatically
- ✓ Shows pass/fail status
- ✓ Displays next steps

**Manual test commands:**
```bash
ruby test_osc_connection.rb      # Test OSC connection
ruby test_audio_synthesis.rb     # Test audio generation
ruby test_complete_system.rb     # Full system test
```

---

### Audio Testing Environment

```bash
# Full audio testing suite
flox activate -e audio-test
```

**Available:**
- Sonic Pi server
- Audio analysis tools (sox)
- OSC debugging (jq)
- Complete Ruby environment

**Run tests:**
```bash
ruby test_osc_connection.rb
ruby test_audio_synthesis.rb
ruby test_complete_system.rb
```

---

## Automated Test Workflow

When you enter the test environment:

```
flox activate -e test
  ↓
System checks if Sonic Pi running
  ↓
If yes:
  ✓ Run test_osc_connection.rb
  ✓ Verify OSC works
  ✓ Show results
  ↓
If no:
  ⚠ Show instructions
  ↓
Ready for manual testing
```

---

## Complete Testing Procedure

### Step 1: Open Terminal

```bash
cd /Users/bob/ies/music-topos
```

### Step 2: Enter Test Environment

```bash
flox activate -e test
```

**Expected output:**
```
════════════════════════════════════════════════════════════════
🧪 MUSIC TOPOS TEST ENVIRONMENT
════════════════════════════════════════════════════════════════

Running automated tests...

✓ Sonic Pi is running on localhost:4557

Running OSC audio tests...
[test output]
```

### Step 3: Check Results

#### If Sonic Pi is running:
```
✓ All tests passed!
════════════════════════════════════════════════════════════════
```

#### If Sonic Pi not running:
```
⚠ Sonic Pi not running on port 4557

To run audio tests:
  1. Start Sonic Pi application
  2. Return to this terminal
  3. Run: ruby test_osc_connection.rb
```

---

## Test Suite Details

### Test 1: OSC Connection (`test_osc_connection.rb`)

**What it tests:**
- Can we connect to Sonic Pi on localhost:4557?
- Can we send OSC packets?
- Does Sonic Pi receive them?

**Output:**
```
Test 1: Checking Sonic Pi on localhost:4557...
  ✓ Socket created successfully

Test 2: Sending OSC test message...
  ✓ OSC bundle sent (X bytes)

Test 3: Verifying Sonic Pi is listening...
  ✓ Second message sent

✓ OSC CONNECTION SUCCESSFUL
```

---

### Test 2: Audio Synthesis (`test_audio_synthesis.rb`)

**What it tests:**
- PitchClass → Frequency conversion
- Chord → MIDI/Frequency mapping
- Voice leading distance calculation
- WAV file generation

**Output:**
```
Test 1: PitchClass → Frequency conversion...
  ✓ C (octave 4): 261.63 Hz (expected 261.63)
  ✓ G (octave 4): 392.00 Hz (expected 392.00)

Test 2: Chord → MIDI → Frequencies...
  Chord: Chord(C-E-G-C)
  MIDI notes: 60, 52, 55, 36
  ✓ All frequencies in human hearing range

Test 5: WAV File Synthesis...
  ✓ WAV file created: /tmp/test_audio.wav
    Size: 441000 bytes
  ✓ File size reasonable

✓ ALL TESTS PASSED (6/6)
```

---

### Test 3: Complete System (`test_complete_system.rb`)

**What it tests:**
1. Mathematical validation
2. Semantic closure verification
3. Triangle inequality enforcement
4. Audio synthesis
5. OSC connection status
6. PLR transformations

**Output:**
```
TEST 1: Mathematical Validation
  ✓ Metric space valid (3 objects)

TEST 2: Semantic Closure Validation
  ✓ Semantic closure verified (8/8 dimensions)

TEST 3: Voice Leading Validation
  ✓ Triangle inequality satisfied

TEST 4: Audio Synthesis
  ✓ WAV file generated

TEST 5: OSC Connection Status
  ✓ OSC connection established

TEST 6: Neo-Riemannian Transformations
  ✓ P transformation correct

✓ ALL 6 TESTS PASSED!
```

---

## Troubleshooting

### Problem: "flox: command not found"

**Solution:**
```bash
# Install Flox
brew install flox

# Or verify installation
which flox
```

### Problem: "Sonic Pi not running"

**Solution:**
```bash
# Install Sonic Pi
flox activate -e dev
# Then start Sonic Pi app
# Then run tests again
```

### Problem: "socket error: Address already in use"

**Solution:**
```bash
# Port 4557 is in use by another app
# Kill the process:
lsof -i :4557
kill -9 <PID>

# Or restart Sonic Pi
```

### Problem: Tests fail with "require error"

**Solution:**
```bash
# Make sure you're in flox environment:
flox activate -e test

# Then run test
ruby test_osc_connection.rb
```

---

## Environment Variables

When you activate Flox environment:

```bash
# Available commands:
ruby --version         # Ruby 3.2.x
sonic-pi --version   # Sonic Pi version
sox --version        # Audio utilities
jq --version         # JSON tools

# Environment variables:
echo $FLOX_ENV       # Current environment name
echo $PATH           # Updated with Flox tools
```

---

## Development Workflow

### 1. Daily Development

```bash
# Start
flox activate -e dev

# Do your work
ruby bin/interactive_repl.rb

# Exit
exit
```

### 2. Testing Before Commit

```bash
# Run tests
flox activate -e test

# Results shown automatically
```

### 3. Full Validation

```bash
# Run all tests
flox activate -e audio-test

ruby test_osc_connection.rb
ruby test_audio_synthesis.rb
ruby test_complete_system.rb
```

---

## Flox Configuration

**Location:** `flox.toml`

**Sections:**
- `[project]` - Project metadata
- `[environments.dev]` - Development environment
- `[environments.test]` - Testing with auto-run
- `[environments.audio-test]` - Full audio testing
- `[environments.production]` - Production (audio only)

**Features:**
- `packages` - List of tools to install
- `features` - Optional feature groups
- `hook.on-activate` - Scripts to run on entry

---

## CI/CD Integration

You can automate testing in CI/CD:

```bash
#!/bin/bash
# Example CI script

cd /Users/bob/ies/music-topos

# Activate test environment and run tests
flox activate -e test -- \
  bash -c "ruby test_complete_system.rb"

# Check exit code
if [ $? -eq 0 ]; then
  echo "✓ All tests passed"
  exit 0
else
  echo "✗ Tests failed"
  exit 1
fi
```

---

## Commands Reference

| Command | Purpose |
|---------|---------|
| `flox list` | List available Flox environments |
| `flox activate -e dev` | Enter dev environment |
| `flox activate -e test` | Enter test environment |
| `flox show` | Show environment details |
| `flox search <package>` | Search for packages |
| `flox search sonic-pi` | Find Sonic Pi package |

---

## Complete Setup (Start to Finish)

```bash
# 1. Install Flox
brew install flox

# 2. Navigate to project
cd /Users/bob/ies/music-topos

# 3. Activate environment (sets up everything)
flox activate -e test

# 4. Watch automated tests run
# (Should show results automatically)

# 5. If all pass, you're ready to develop
ruby bin/interactive_repl.rb

# 6. Compose music
# > play C E G C
# [hear actual audio via OSC]

# 7. Exit when done
exit
```

---

## Philosophy

**Before Flox:**
- Manual Ruby installation
- Manual Sonic Pi installation
- Manual port setup
- Hope everything works

**With Flox:**
- ✓ Automated setup
- ✓ Verified dependencies
- ✓ Automated testing
- ✓ Reproducible results
- ✓ Same environment for everyone

**Result:** Confidence that the system actually works, not just theoretically.

---

**Status**: Flox environment fully configured and ready for testing.

Run:
```bash
flox activate -e test
```

And the entire system will validate itself automatically.
