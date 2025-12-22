# Music Topos Justfile - Quick Start

## One Command to Rule Them All

```bash
just world
```

This single command will:

1. ✓ Check all dependencies (flox, leiningen, SuperCollider)
2. ✓ Install SuperCollider startup configuration
3. ✓ Boot SuperCollider server if not running
4. ✓ Build the Clojure project
5. ✓ Verify audio output configuration
6. ✓ Play InitialObjectWorld (4 sections, ~15 seconds)
7. ✓ Play TerminalObjectWorld (4 sections, ~15 seconds)

**Expected result:** You hear music coming through your speakers 🎵

---

## What It Does (Step by Step)

### Step 1: Dependency Check
```
✓ flox available
✓ leiningen available
✓ scsynth available
```

### Step 2: SuperCollider Setup
- Copies `startup.scd` to `~/Library/Application Support/SuperCollider/`
- Sets correct permissions
- Defines the "sine" synth needed for audio output

### Step 3: Server Boot
- Checks if SuperCollider is running on port 57110
- If not running, boots it automatically
- Waits for server to be ready

### Step 4: Build
- Compiles the Clojure code
- Downloads dependencies via Leiningen
- Creates standalone JAR

### Step 5: Audio Check
- Verifies system audio output is configured
- Shows current volume settings

### Step 6-7: Sound!
- Runs InitialObjectWorld
- Runs TerminalObjectWorld
- Logs output to `.music-topos-run.log`

---

## Individual Commands

If you want to run steps separately:

```bash
# Setup phase (one time)
just check-deps              # Verify dependencies installed
just setup-supercollider     # Install SuperCollider config
just boot-sc-server          # Start audio server

# Build phase (after code changes)
just build                   # Compile Clojure project

# Execution phase (whenever you want)
just run-initial             # Play InitialObjectWorld
just run-terminal            # Play TerminalObjectWorld

# Diagnostics
just check-sc-server         # Is SuperCollider running?
just check-audio             # Audio system configuration
just logs                    # View run logs

# Cleanup
just stop-sc                 # Stop SuperCollider server
```

---

## Troubleshooting

### No Sound Heard?

1. **Check audio is configured:**
   ```bash
   just check-audio
   ```

2. **Verify SuperCollider is running:**
   ```bash
   just check-sc-server
   ```

3. **Verify startup.scd was installed:**
   ```bash
   ls ~/Library/Application\ Support/SuperCollider/startup.scd
   ```

4. **Check system audio output:**
   - Open System Preferences → Sound
   - Verify output device is selected
   - Check volume is not muted

5. **Try running again:**
   ```bash
   just stop-sc
   just world
   ```

### Build Fails?

```bash
just build    # Try rebuilding
```

If that doesn't work:
```bash
flox activate -- lein clean
flox activate -- lein uberjar
```

### SuperCollider Won't Boot?

1. Check if already running:
   ```bash
   lsof -i :57110
   ```

2. Kill any stuck processes:
   ```bash
   just stop-sc
   ```

3. Verify SuperCollider is installed:
   ```bash
   which scsynth
   ```

4. If not installed, download from: https://supercollider.github.io/downloads.html

---

## How It Works (Under The Hood)

### The Justfile as Documentation

Each recipe in the justfile is both executable AND readable:

```justfile
setup-supercollider:
    #!/bin/bash
    # Creates config directory
    mkdir -p "$HOME/Library/Application Support/SuperCollider"

    # Installs startup configuration
    cp startup.scd "$SC_STARTUP"

    # Sets permissions
    chmod 644 "$SC_STARTUP"
```

You can read exactly what each step does.

### No Sudo Required

The `world` recipe handles everything without requiring sudo because:

- Configuration files go to your home directory (no system permissions needed)
- SuperCollider boots as a regular user process
- All Clojure compilation happens locally

### Atomic Operations

Each step is self-contained:
- If step 3 fails, steps 4-7 don't run
- You can fix the issue and re-run from that point
- Partial failures are clearly reported

---

## Output Examples

### Successful Run

```
🌍 Music Topos - Complete World Setup
════════════════════════════════════════════════════════════════

Step 1/7: Checking dependencies...
─────────────────────────────────────────────────────────────────
✓ flox available
✓ leiningen available
✓ scsynth available

✓ All dependencies present

Step 2/7: Setting up SuperCollider...
...
[continues with all 7 steps]

════════════════════════════════════════════════════════════════
✓ Music Topos World Complete!
```

### With Issues

```
Step 3/7: Checking SuperCollider server...
✗ SuperCollider server is NOT running on port 57110
SuperCollider server not running. Booting...
🎵 Booting SuperCollider server...
Starting scsynth on port 57110...
Waiting for server to boot (PID: 12345)...
✓ SuperCollider server booted successfully

[continues normally]
```

---

## Performance Notes

- **First run:** ~30-60 seconds (builds Clojure project, boots SuperCollider)
- **Subsequent runs:** ~5-10 seconds (if SuperCollider already running)
- **Music duration:** ~30 seconds total (InitialObjectWorld + TerminalObjectWorld)

---

## What Gets Installed/Modified

### New Files
- `~/.music-topos-run.log` - Execution logs

### Modified Files
- `~/Library/Application Support/SuperCollider/startup.scd` - SuperCollider configuration (copied from project)

### No System-Level Changes
- No sudoto required
- No changes to /usr, /opt, etc.
- No changes to system libraries
- All changes are user-specific and reversible

---

## Advanced Usage

### Run Just InitialObjectWorld (Loop)

```bash
# Run once
just run-initial

# Run and repeat
while true; do just run-initial; done
```

### Debug SuperCollider Issues

```bash
# See SuperCollider server logs
just check-sc-server
just check-audio

# In another terminal, monitor SuperCollider
Server.local.dump  # Shows active synths
Server.local.scope # Shows waveforms
```

### Verify Morphism Chain

```bash
# Check that each layer works:

1. Clojure code generates correct OSC messages
   just build

2. OSC reaches SuperCollider
   just run-initial    # Should connect without errors

3. SuperCollider creates synths
   just check-sc-server  # Should show active synths

4. Audio is generated
   just check-audio    # Should show output device active
```

---

## Next Steps

1. **Run it:**
   ```bash
   just world
   ```

2. **Listen for music** 🎵

3. **If audio works:**
   - Explore individual commands
   - Read SOLUTION_SUMMARY.md for architecture
   - Check OVERTONE_TO_OSC_MAPPING.md for extending

4. **If audio doesn't work:**
   - Follow troubleshooting above
   - Check CAUSAL_CHAIN_ANALYSIS.md for verification steps
   - Post issues to repository

---

## One-Liner Reference

```bash
# Everything in one command
just world

# Check everything works
just check-deps && just check-sc-server && just check-audio

# Quick rebuild and test
just build && just run-initial
```

---

*Music Topos - Ready for Sound*
