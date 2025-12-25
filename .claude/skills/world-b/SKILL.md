---
name: world-b
description: bmorphism projects - trittty terminal emulator (Ghostty fork with balanced ternary extensions), oxcaml-sci scientific computing, fusion OS kernel, and babashka static builds
version: 1.0.0
author: bmorphism
tags:
  - terminal
  - zig
  - swift
  - nim
  - os-kernel
  - balanced-ternary
  - ghostty
color: "#B05425"
hue: 20.3
trit: 1
role: PLUS
wallet: "0x3f892ebe6e45164e63416ad10e7c87ce81e1acf2264c32dcfe21105a4577cb13"
neighbors: ["A", "C"]
mcp_alias: "bob_aptos"
---

# World b - bmorphism Projects

**Color**: `#B05425` | **Trit**: +1 PLUS | **Hue**: 20.3°

## Wallet

```
0x3f892ebe6e45164e63416ad10e7c87ce81e1acf2264c32dcfe21105a4577cb13
```

## GF(3) Role

As a **PLUS (+1)** world, World B serves as a **generator** in triadic operations:
- Generates new solutions
- Executes transformations
- Produces outputs

Navigation skill for ~/worlds/B containing bmorphism's infrastructure projects.

## Directory Tree

```
B/
└── bmorphism/
    ├── trittty/                     # Ghostty fork with ternary extensions
    │   ├── macos/                   # macOS native app
    │   │   ├── Assets.xcassets/     # App icons & assets
    │   │   │   ├── Custom Icon/     # Customizable icon components
    │   │   │   └── Alternate Icons/ # Theme variants (Xray, Retro, Glass, etc.)
    │   │   ├── Sources/
    │   │   │   ├── App/             # iOS/macOS app entry
    │   │   │   ├── Features/        # Terminal, Settings, QuickTerminal, etc.
    │   │   │   ├── Helpers/         # SplitView, Private utilities
    │   │   │   └── Ghostty/         # Core bridge to Zig
    │   │   └── Ghostty.xcodeproj/   # Xcode project
    │   ├── nix/                     # Nix build support & VM configs
    │   ├── src/                     # Core Zig implementation
    │   │   ├── renderer/            # Metal & OpenGL backends
    │   │   │   ├── metal/
    │   │   │   ├── opengl/
    │   │   │   └── shaders/
    │   │   ├── apprt/gtk/           # GTK runtime (Linux)
    │   │   ├── terminal/            # Terminal emulation core
    │   │   │   ├── kitty/           # Kitty protocol support
    │   │   │   └── res/
    │   │   ├── font/                # Font rendering
    │   │   │   ├── face/
    │   │   │   ├── shaper/
    │   │   │   ├── sprite/
    │   │   │   └── opentype/
    │   │   ├── shell-integration/   # bash, zsh, fish, elvish
    │   │   ├── unicode/
    │   │   ├── config/
    │   │   ├── input/
    │   │   ├── simd/
    │   │   ├── cli/
    │   │   ├── crash/               # Crash reporting & minidump
    │   │   ├── terminfo/
    │   │   ├── termio/
    │   │   ├── datastruct/
    │   │   ├── inspector/
    │   │   ├── os/wasm/
    │   │   ├── stb/
    │   │   ├── bench/
    │   │   └── build/               # Build tooling (webgen, mdgen, docker)
    │   ├── pkg/                     # Vendored dependencies
    │   │   ├── macos/               # macOS bindings (dispatch, foundation, etc.)
    │   │   ├── freetype/
    │   │   ├── harfbuzz/
    │   │   ├── fontconfig/
    │   │   ├── glfw/
    │   │   ├── cimgui/
    │   │   ├── libpng/
    │   │   ├── zlib/
    │   │   ├── glslang/
    │   │   ├── spirv-cross/
    │   │   ├── sentry/
    │   │   ├── breakpad/
    │   │   └── ... (simdutf, highway, oniguruma, etc.)
    │   ├── dist/                    # Distribution configs (macos, linux, windows)
    │   ├── flatpak/
    │   ├── snap/
    │   ├── test/cases/vttest/
    │   ├── images/icons/
    │   ├── vendor/glad/
    │   ├── include/
    │   ├── example/
    │   └── po/                      # Translations
    │
    ├── oxcaml-sci/                  # OCaml scientific computing
    │
    ├── fusion/                      # Nim OS kernel
    │   ├── src/
    │   │   ├── kernel/drivers/
    │   │   ├── boot/
    │   │   ├── common/
    │   │   ├── user/
    │   │   ├── syslib/
    │   │   ├── nimpatches/
    │   │   └── include/
    │   ├── ovmf/                    # UEFI firmware
    │   └── screenshots/
    │
    └── babashka-static-build/       # Static Babashka builds
```

## Key Projects

### trittty (Ghostty Fork)
A terminal emulator based on Ghostty with balanced ternary extensions:
- **Language**: Zig core + Swift macOS UI
- **Renderers**: Metal (macOS), OpenGL (Linux/Windows)
- **Features**: GPU-accelerated, kitty graphics protocol, shell integration
- **Build**: Nix flake or Xcode

### fusion
Nim-based OS kernel:
- **Boot**: UEFI via OVMF
- **Drivers**: Custom kernel drivers
- **Build**: Nim compiler with custom patches

### oxcaml-sci
OCaml scientific computing toolkit.

### babashka-static-build
Static compilation infrastructure for Babashka (Clojure scripting runtime).

## Navigation Patterns

```bash
# Build trittty on macOS
cd ~/worlds/B/bmorphism/trittty
nix build .#ghostty

# Open Xcode project
open macos/Ghostty.xcodeproj

# Run fusion in QEMU
cd ~/worlds/B/bmorphism/fusion
# See fusion README for QEMU invocation
```

## Integration Points

- **Gay.jl colors**: Terminal theming via deterministic 3-color palettes
- **GF(3) trits**: Balanced ternary support in terminal rendering
- **Nix**: Reproducible builds across all projects
- **MCP**: Terminal can serve as MCP transport layer
