# Music Topos Setup Guide

## Quick Setup (5 minutes)

### 1. SuperCollider
```bash
# Using Homebrew (simplest for macOS)
brew install supercollider

# Or download: https://supercollider.github.io/download
```

### 2. Clojure & Leiningen
```bash
# Via Flox (already configured)
flox activate

# Or manually:
brew install clojure leiningen
```

### 3. Run
```bash
# In Flox environment (recommended)
flox activate -- lein run initial

# Or directly
lein run initial    # Initial object world
lein run terminal   # Terminal object world (sonata)
```

## What Gets Installed

- **SuperCollider** (audio synthesis engine)
  - `scsynth` - audio server
  - Real-time synthesis, no Sonic Pi needed

- **Clojure** (programming language)
  - JVM-based functional language
  - Powers Overtone

- **Leiningen** (build tool)
  - Manages dependencies
  - Runs Clojure projects

- **Overtone** (Clojure audio library)
  - Downloaded automatically by Leiningen
  - Wraps SuperCollider

## Using Flox

```bash
# Enter Flox environment
flox activate

# Inside environment, all tools available:
lein --version
clojure --version
scsynth --version

# Run project
lein run initial
```

## Without Flox

```bash
# Just use Homebrew
brew install supercollider clojure leiningen

# Run
lein run initial
```

## Troubleshooting

### SuperCollider not found
```bash
# Check installation
which scsynth
which sclang

# If not found, install via Homebrew
brew install supercollider
```

### Leiningen issues
```bash
# Update Leiningen
brew upgrade leiningen

# Or reinstall
brew uninstall leiningen
brew install leiningen
```

### Audio not working
- Open SuperCollider.app directly (has GUI)
- Click "Boot Server" to start audio
- Then run: `lein run initial`

## Environment Variables (Optional)

```bash
export SUPERCOLLIDER_PATH="/usr/local/bin"
export JAVA_TOOL_OPTIONS="-Xmx2g"  # More memory for Clojure
```

---

**You now have everything you need. Just run:**

```bash
flox activate
lein run initial
```

**Or without Flox:**

```bash
lein run initial
```
