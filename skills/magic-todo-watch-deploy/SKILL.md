---
name: magic-todo-watch-deploy
description: Build, deploy, and manage the MagicTodoWatch iOS/watchOS voice-to-task pipeline app. Use when building for device or simulator, fixing Xcode project issues, or running the 7-world backend pipeline.
---

# MagicTodoWatch Deploy

## Project Location

- **Source**: `/Users/alice/worlds/w/MagicTodoWatch/`
- **jj repo**: `/Users/alice/worlds/magic-todo-watch/`
- **GitHub**: `monaduck1069/magic-todo-watch` (private)
- **Bundle ID**: `com.monaduck1069.MagicTodoWatch`
- **Watch Bundle**: `com.monaduck1069.MagicTodoWatch.watchkitapp`
- **Team**: `FLLV2L2D4K`
- **Device (#ee2b49)**: `00008150-00123D3E0C46401C`

## Xcode Setup

Xcode is at `/Users/alice/Downloads/Xcode.app`. xcode-select points at CommandLineTools, so ALL xcodebuild/xcrun commands need:

```bash
DEVELOPER_DIR=/Users/alice/Downloads/Xcode.app/Contents/Developer
```

For xcrun (simctl, devicectl):
```bash
DEVELOPER_DIR=/Users/alice/Downloads/Xcode.app/Contents/Developer /usr/bin/xcrun simctl ...
```

For xcodebuild:
```bash
DEVELOPER_DIR=/Users/alice/Downloads/Xcode.app/Contents/Developer /Users/alice/Downloads/Xcode.app/Contents/Developer/usr/bin/xcodebuild ...
```

## Build & Deploy to Physical Device

```bash
XC="DEVELOPER_DIR=/Users/alice/Downloads/Xcode.app/Contents/Developer /Users/alice/Downloads/Xcode.app/Contents/Developer/usr/bin/xcodebuild"
DC="DEVELOPER_DIR=/Users/alice/Downloads/Xcode.app/Contents/Developer /Users/alice/Downloads/Xcode.app/Contents/Developer/usr/bin/devicectl"
PROJ="-project /Users/alice/worlds/w/MagicTodoWatch/MagicTodoWatch.xcodeproj"
DEVICE="id=00008150-00123D3E0C46401C"

# Build (includes embedded watch app)
$XC $PROJ -scheme MagicTodoWatch -configuration Debug -destination "$DEVICE" -allowProvisioningUpdates clean build

# Install
APP_PATH=$(ls -d ~/Library/Developer/Xcode/DerivedData/MagicTodoWatch-*/Build/Products/Debug-iphoneos/MagicTodoWatch.app | head -1)
$DC device install app --device 00008150-00123D3E0C46401C "$APP_PATH"

# Launch (phone must be unlocked)
$DC device process launch --device 00008150-00123D3E0C46401C com.monaduck1069.MagicTodoWatch
```

## Build & Deploy to Simulators

```bash
SIMCTL="DEVELOPER_DIR=/Users/alice/Downloads/Xcode.app/Contents/Developer /usr/bin/xcrun simctl"
IPHONE_SIM=E7F1ADC6-21F1-4BA4-944A-B99D693571B3   # iPhone 17
WATCH_SIM=FE8B667A-A976-4F71-9CE6-F1C7414F5C25     # Apple Watch Series 10 46mm

# Boot
$SIMCTL boot $IPHONE_SIM
$SIMCTL boot $WATCH_SIM

# Build for sim
$XC $PROJ -scheme MagicTodoWatch -destination "id=$IPHONE_SIM" -allowProvisioningUpdates build

# Install
$SIMCTL install $IPHONE_SIM ~/Library/Developer/Xcode/DerivedData/MagicTodoWatch-*/Build/Products/Debug-iphonesimulator/MagicTodoWatch.app
$SIMCTL install $WATCH_SIM ~/Library/Developer/Xcode/DerivedData/MagicTodoWatch-*/Build/Products/Debug-watchsimulator/MagicTodoWatchWatch.app

# Launch
$SIMCTL launch $IPHONE_SIM com.monaduck1069.MagicTodoWatch
$SIMCTL launch $WATCH_SIM com.monaduck1069.MagicTodoWatch.watchkitapp

# Open Simulator.app
open /Users/alice/Downloads/Xcode.app/Contents/Developer/Applications/Simulator.app
```

## Architecture

```
Watch (watchOS 10+)                    Phone (iOS 17+)
┌──────────────────┐                   ┌──────────────────────────┐
│ AudioCaptureMgr  │─── PCM chunks ──→│ PhoneSessionManager      │
│ LiveTranscriber   │   (WCSession)    │   ├─ SFSpeechRecognizer  │
│ WatchSessionMgr  │←── transcripts ──│   ├─ TodoProcessor        │
│ WatchContentView │    + todos        │   │   ├─ LocalModelService│
└──────────────────┘                   │   │   └─ regex fallback   │
                                       │   └─ CaptureBufferBridge  │
                                       │       └─ JSON → Files app │
                                       └──────────────────────────┘
                                                    │
                                           ~/Documents/capture-buffer/
                                                    │
                                       ┌────────────▼─────────────┐
                                       │   Desktop Pipeline       │
                                       │   p/orchestrate.py       │
                                       │   W→T→A→M→P→E↔C         │
                                       └──────────────────────────┘
```

## Key Files (iOS Target)

| File | Role |
|------|------|
| `App/Services/PhoneSessionManager.swift` | WCSessionDelegate, SFSpeech, main coordinator |
| `App/Services/TodoProcessor.swift` | 3-stage extraction chain (NLP → regex → MLX) |
| `App/Services/LocalModelService.swift` | NLTagger POS/NER on-device extraction |
| `App/Services/CaptureBufferBridge.swift` | JSON export to App Group + Files app |
| `App/Services/VoiceMemoBridge.swift` | Voice memo audio bridge |

## Key Files (watchOS Target)

| File | Role |
|------|------|
| `Watch/Services/AudioCaptureManager.swift` | AVAudioEngine mic capture |
| `Watch/Services/LiveTranscriber.swift` | Float32→Int16 conversion, chunked send |
| `Watch/Services/WatchSessionManager.swift` | WCSession send/receive |

## Common Issues & Fixes

### "cannot find 'X' in scope"
File exists but isn't in `project.pbxproj`. Add three entries:
1. PBXBuildFile (Sources reference)
2. PBXFileReference (file declaration)
3. PBXGroup children (directory listing)
4. PBXSourcesBuildPhase files (compile list)

### Python 3.9 compat
Pipeline scripts must work on system Python 3.9.6. Use `from __future__ import annotations` instead of `X | None` union syntax.

### Empty entitlements
Both `App.entitlements` and `Watch.entitlements` MUST contain `group.com.magictodo.capture` App Group for CaptureBufferBridge to work.

### Phone locked during launch
`devicectl device process launch` fails with "Locked" — phone must be unlocked first. Install still works while locked.

## 7-World Pipeline

```bash
# Dry-run the orchestrator
python3 /Users/alice/worlds/p/orchestrate.py --dry-run --verbose

# Run arena forge conversion
python3 /Users/alice/worlds/p/task_to_arena.py /Users/alice/worlds/p/capture-buffer-canonical.org --dry-run

# Regenerate olog from arena
python3 /Users/alice/worlds/p/task-olog-export.py --input /Users/alice/worlds/p/arena_forge.json --output /Users/alice/worlds/p/task-olog.json --pretty
```

## jj Workflow

```bash
JJ=/nix/store/jjyhca8bymk8zvgc65q5cy19wm9pqkmd-jujutsu-0.38.0/bin/jj
cd /Users/alice/worlds/magic-todo-watch

$JJ status
$JJ log
$JJ describe -m "description"
$JJ new
$JJ bookmark set main -r @-
$JJ git push --bookmark main
```

## App Icon

Generate with Swift (renders emoji to 1024x1024 PNG):
```bash
# See /tmp/gen_icon.swift — renders emoji onto rounded-rect background
# Output: App/Assets.xcassets/AppIcon.appiconset/icon_1024.png
/usr/bin/swift /tmp/gen_icon.swift
```
