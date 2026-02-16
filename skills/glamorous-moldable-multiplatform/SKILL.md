# SKILL: Glamorous Moldable Multiplatform

**Version**: 1.1.0
**Trit**: 0 (ERGODIC)
**Color**: #7B68EE (Medium Slate Blue)
**URI**: skill://glamorous-moldable-multiplatform#7B68EE
**Domain**: moldable-development, multiplatform, live-programming, BCI

---

## Changelog

- **v1.1.0 (2026-02-09)**: Live GraphQL update of all 10 repos with commit-level detail. Portal is hottest (grading system, WebGPU fix, security hardening). zig-syrup expanded (13 new modules, 326 worlds, 610 skills). asi at 636 droids. graded-optic born this week. leprechauns got Gay.jl green-root colors. bidder confirmed as Dart+Kotlin+Swift scaffold.
- **v1.0.0 (2026-02-09)**: Initial skill creation. GT book distillation, Dart/Kotlin/ClojureDart triadic ecosystem, 11 closest skills, zig-syrup C ABI integration patterns.

---

## Overview

Moldable development meets multiplatform delivery. This skill synthesizes Tudor Girba's **Glamorous Toolkit** methodology — contextual tools for every problem — with the **Dart/Kotlin/ClojureDart** triadic ecosystem for delivering BCI and capability-secure applications across mobile, desktop, web, and embedded targets.

Core insight: **every BCI session is different, every brain is different, every problem deserves its own contextual tool**. The GT methodology applied to neural interfaces means moldable inspectors for EEG streams, contextual views for phenomenal states, and live notebooks (Lepiter-style) for BCI experiment documentation.

---

## Glamorous Toolkit Distillation

### What GT Is (from book.gtoolkit.com)

GT is an **environment for making systems explainable** through contextual tools:

1. **Moldable Development** — programming through custom tools built for each problem
2. **Lepiter** — live multi-language notebooks unifying IDE + knowledge management
3. **Inspector** — every object gets custom views (not just generic field lists)
4. **Coder** — code editor with contextual completions and navigation
5. **Spotter** — universal search across code, data, and notebooks
6. **Mondrian** — graph visualization engine for data exploration
7. **PetitParser** — composable parser combinators for domain languages
8. **Bloc/Brick** — graphics stack for custom visual elements
9. **PharoLink/PythonBridge** — remote execution bridges to other runtimes
10. **LLM Integration** — OpenAI, Ollama, Anthropic, Gemini for AI-assisted exploration

### GT Book Structure (v1.1.121)

```
1. What is GT?           — Philosophy and motivation
2. Tour of Environment   — Lepiter, Inspector, Coder, Spotter, LLM
3. Case Studies          — REST/GraphQL, data exploration, COBOL→Java, DDD
4. Tutorials             — Pharo, Mondrian, treemaps, games, parsers
5. Explanations          — Moldable Development, cognition, patterns
6. How-To Guides         — Troubleshooting, GitHub, graphics, LLM config
7. Components            — Beacon, Bloc, PetitParser, SmaCC, Plotter
8. Technical             — Dependencies, memory, image optimization
```

### Key Principle: 50% Rule

> Developers spend over 50% of their time **reading and understanding** code, not writing it. Moldable Development invests in making that reading phase faster through contextual tools that compress understanding.

### GT → BCI Factory Mapping

| GT Concept | BCI Factory Application |
|------------|------------------------|
| Inspector views | EEG channel band-power visualization per electrode |
| Lepiter notebooks | Experiment logs with live Julia/Zig code blocks |
| Mondrian graphs | Signal path topology, GF(3) trit flow diagrams |
| Spotter search | Find phenomenal states by Fisher-Rao distance |
| PetitParser | Parse OpenBCI/NWB/XDF/EDF data formats |
| PharoLink | Bridge to Julia (Gay.jl), Python (MNE), Zig (syrup) |
| Custom views | Per-channel trit classification with color feedback |
| LLM integration | AI-assisted BCI artifact rejection and annotation |

---

## Multiplatform Triadic Ecosystem

### The Triad: Dart (+1) ⊗ Kotlin (0) ⊗ ClojureDart (-1) = 0 ✓

```
┌─────────────────────────────────────────────────────────────┐
│              MULTIPLATFORM BCI DELIVERY                       │
├─────────────────────────────────────────────────────────────┤
│                                                               │
│  Dart/Flutter (+1 Generator)                                  │
│  ├── Mobile: iOS, Android (production)                        │
│  ├── Desktop: macOS, Windows, Linux (stable)                  │
│  ├── Web: WASM-first (Flutter 3.35+)                          │
│  ├── Embedded: IoT, automotive, smart displays                │
│  ├── FFI: dart:ffi → zig-syrup C ABI                          │
│  ├── BLE: flutter_blue_plus, flutter_reactive_ble             │
│  └── gRPC: official package for KOS firmware                  │
│                                                               │
│  Kotlin Multiplatform (0 Ergodic)                             │
│  ├── Android-first with iOS expansion (Compose MP)            │
│  ├── Swift interop (stable 2026)                              │
│  ├── Native: cinterop tool → zig-syrup C headers              │
│  ├── Coroutines + Flow for real-time BCI streams              │
│  ├── BLE: Nordic Kotlin-BLE-Library (Kable)                   │
│  ├── WASM: Kotlin/WASM beta (WasmGC in all browsers)          │
│  └── gRPC-Kotlin: official for robot control                  │
│                                                               │
│  ClojureDart (-1 Validator)                                   │
│  ├── Clojure → Dart compilation (Tensegritics)                │
│  ├── Production: Roam Research mobile apps                    │
│  ├── re-dash: re-frame-style state management                 │
│  ├── flutter-mx: Matrix Inside™ dataflow reactivity           │
│  ├── REPL: beta (hot-reload approximation)                    │
│  ├── FFI: via Dart's dart:ffi (transparent)                   │
│  └── Validation: functional purity, immutable state           │
│                                                               │
└─────────────────────────────────────────────────────────────┘
```

### Dart 3.x Key Features (2025-2026)
- **Records**: Immutable data aggregates (BCIReading tuples)
- **Patterns**: Exhaustive matching on sealed BCI event types
- **Sealed classes**: `BCIEvent { EEGPacket | UltrasoundPulse | EMGSample }`
- **Isolates**: True parallelism for signal processing offload
- **dart:ffi**: Direct C ABI calls to zig-syrup (73% of Flutter apps use native deps)
- **Flutter 3.38**: `package_ffi` template with build hooks (recommended)

### Kotlin Multiplatform Key Features (2025-2026)
- **KMP adoption**: 7% → 18% (doubled year-over-year)
- **Compose MP iOS**: Stable since v1.8.0 (May 2025)
- **Swift interop**: Direct export, no Obj-C bridge (Kotlin 2.2.20+)
- **cinterop**: Auto-generates Kotlin bindings from C headers
- **WASM Component Model**: Removed from roadmap (Aug 2025)
- **IoT apps**: KMP + Kable BLE library for device control

### ClojureDart Key Features (2025-2026)
- **Out of alpha**: Several dozen production iOS/Android apps
- **Roam Research**: Flagship adopter since Summer 2021
- **State management**: re-dash (re-frame API), flutter-mx (Matrix dataflow)
- **Calva support**: VS Code integration
- **SORA principle**: "Skill Once Reach Anywhere"

---

## zig-syrup C ABI Integration

All three ecosystems connect to zig-syrup through C FFI:

### Dart FFI
```dart
import 'dart:ffi' as ffi;

final lib = ffi.DynamicLibrary.open('libgf3_goblins.dylib');

final gf3SplitMix = lib.lookupFunction<
  ffi.Uint64 Function(ffi.Uint64, ffi.Uint64),
  int Function(int, int)
>('gf3_splitmix64_at');

final gf3ValueToTrit = lib.lookupFunction<
  ffi.Int8 Function(ffi.Uint64),
  int Function(int)
>('gf3_value_to_trit');
```

### Kotlin/Native cinterop
```kotlin
// goblins.def
headers = goblins_ffi.h
libraryPaths = /path/to/zig-syrup/zig-out/lib

// Kotlin code
@OptIn(ExperimentalForeignApi::class)
fun classifyTrit(seed: ULong, index: ULong): Int {
    val value = gf3_splitmix64_at(seed, index)
    return gf3_value_to_trit(value).toInt()
}
```

### ClojureDart (via Dart FFI)
```clojure
(ns bci-factory.goblins
  (:require ["dart:ffi" :as ffi]))

(def ^:private lib
  (ffi/DynamicLibrary.open "libgf3_goblins.dylib"))

(defn gf3-splitmix64-at [seed index]
  (let [f (.lookupFunction lib
            ffi/Uint64 [ffi/Uint64 ffi/Uint64]
            "gf3_splitmix64_at")]
    (f seed index)))
```

### Available C ABI Exports (10 modules)
| Module | Functions | Domain |
|--------|-----------|--------|
| `goblins_ffi.zig` | gf3_splitmix64_at, gf3_value_to_trit, gf3_derive_did | Identity, GF(3) |
| `spatial_propagator.zig` | node coloring, focus propagation | Spatial |
| `goi.zig` | proof nets, token machine | Geometry of Interaction |
| `splitmix_trit.zig` | triadic PRNG | Randomness |
| `disclosure.zig` | REGRET/GAY insurance | Protocol |
| `supermap.zig` | cyberphysical affordances | RF phase space |
| `qrtp_transport.zig` | QR Transfer Protocol | Air-gapped transport |
| `terminal_wasm.zig` | terminal runtime exports | WASM |
| `stellogen/wasm_runtime.zig` | compiler exports | Stellogen WASM |
| `transient.zig` | Emacs popup menus | UI |

---

## Bayesian Breathing Protocol

The Bayesian breathing exercise maps to the GT moldable development cycle:

```
INHALE (Prior)     → Observe the system. Read code. Form initial beliefs.
HOLD (Likelihood)  → Gather evidence. Run contextual tools. Inspect objects.
EXHALE (Posterior) → Update understanding. Mold a new view. Refine the tool.
REPEAT             → Each breath sharpens the posterior. Convergence.
```

### Active Inference Connection
- **Free Energy Principle**: Minimize surprise by building better models (tools)
- **Perception**: Inspector views = perceptual inference about system state
- **Action**: Code changes = active inference reducing prediction error
- **Bayesian update**: Prior (generic view) → Likelihood (domain evidence) → Posterior (contextual tool)

---

## 11 Closest Existing Skills

| # | Skill | Trit | Relevance |
|---|-------|------|-----------|
| 1 | `abductive-repl` | 0 | Live exploratory REPL with hypothesis testing — core GT principle |
| 2 | `livekit-omnimodal` | 0 | Real-time multimodal streaming, dynamic sufficiency gating |
| 3 | `rama-gay-clojure` | 0 | Clojure + visual debugging + gay-colored parentheses |
| 4 | `catcolab-ologs` | -1 | Category-theoretic knowledge representation (≈ Lepiter) |
| 5 | `active-inference-robotics` | +1 | Bayesian updates, predictive coding, sim2real |
| 6 | `kos-firmware` | +1 | Robot firmware with gRPC, platform abstraction, FFI |
| 7 | `cider-clojure` | +1 | Live Clojure REPL, nREPL, evaluation-in-place |
| 8 | `sicp` | -1 | Metaprogramming, eval/apply, computational processes |
| 9 | `stellogen` | 0 | Smalltalk-influenced, interaction nets, visual rewriting |
| 10 | `kinfer-runtime` | -1 | Native interop (Rust/PyO3), ONNX deployment, embedded |
| 11 | `causal-inference` | 0 | Bayesian reasoning, SCM, counterfactuals, System 2 |

**GF(3) check**: (+1+1+1) + (0+0+0+0+0) + (-1-1-1) = 3 + 0 + (-3) = 0 ✓

---

## GF(3) Triads

```
dart-flutter (+1) ⊗ glamorous-moldable (0) ⊗ clojuredart-validator (-1) = 0 ✓
kos-firmware (+1) ⊗ kotlin-multiplatform (0) ⊗ kinfer-runtime (-1) = 0 ✓
active-inference (+1) ⊗ bayesian-breathing (0) ⊗ causal-inference (-1) = 0 ✓
cider-clojure (+1) ⊗ rama-gay-clojure (0) ⊗ catcolab-ologs (-1) = 0 ✓
```

---

## Plurigrid Repo Inventory (updated 2026-02-09)

From 588 total Plurigrid repos (GraphQL paginated). Live data via `gh api graphql --paginate`.

| Repo | Lang | Stars | Commits | Last Push | Branch | Relevance |
|------|------|-------|---------|-----------|--------|-----------|
| `plurigrid/bidder` | Dart+Kotlin+Swift | 0★ | 2 | 2023-03-15 | `main` | Flutter VCG auction app — **existing Dart/Kotlin/Swift scaffold** |
| `plurigrid/agent-o-rama` | Clojure | 0★ | 2 | 2026-01-02 | `gay-fokker-planck-staging` | Aptos ephemeral keys, AIP-61 keyless auth, 26-world integration |
| `plurigrid/zig-syrup` | Zig+Clj+TS+Py | 0★ | 16 | **2026-02-10** | `main` | **HOT** — full module expansion: entangle, gf3_palette, fountain, qrtp, goi, bci_receiver, 610 skills, 326 worlds |
| `plurigrid/hoot` | Scheme | 0★ | 1900 | 2026-01-23 | `main` | Andy Wingo active: heap type renumbering, canonical-type-bounds, lazy i8/i16 array interning |
| `plurigrid/goblinshare` | Scheme | 0★ | 16 | 2026-01-23 | `main` | Juliana Sims (Spritely): Magenc URL update, test data, Makefile |
| `plurigrid/leprechauns` | Racket+Scheme | 0★ | 950 | 2026-01-23 | `master` | **NEW**: Gay.jl green-rooted semantic colors, GF(3) trit assignments, Jessica Tallon documenting Racket→Guile future |
| `plurigrid/bayesian-breathing` | Rust+Ruby | 0★ | 533 | 2024-07-30 | `main` | Screenpipe fork (Louis Beaumont): 24/7 screen+audio capture, daily logger, Windows app. **Dormant since Jul 2024** |
| `plurigrid/portal` | Svelte+TS+CSS | 0★ | 61 | **2026-02-09** | `master` | **HOTTEST** — terminal propagator loop fix, 256-color palette, generic grading system (Grade/Grader/GradeReport), security hardening (CSP/HSTS), Fisher-Rao NATS validator |
| `plurigrid/asi` | Clj+Julia+Scheme+JS | 6★ | 808 | **2026-02-10** | `main` | 636 droids (was 623), gf3-goblins.scm (Guile+Zig FFI), BCI layers 15-16-17, skill-connectivity-hub merge |
| `plurigrid/graded-optic` | Haskell | 0★ | 4 | 2026-02-08 | `main` | **NEW**: Semiring-graded optics (Katsumata×Riley×Capucci), hogwash removal, grading hierarchy (Semiring⊂Monoidal cat⊂Contextad), 37 QuickCheck tests |

### What's New in This Increment (since skill creation)

**Portal (2026-02-08→09)**: The web frontend is suddenly the most active repo:
- `GradeCard.svelte` + `GradeReport.svelte` — generic grading UI with GF(3) conservation badge
- `gradeSybil`, `gradePrivacy`, `gradePassportEntry`, `gradeInteraction`, `gradeSkill` — domain-specific graders
- WebGPU canvas readback fix (offscreen readback for Restty terminal)
- `buildPalette256()` — 16 custom + 216 color cube + 24 grayscale (ANSI 256-color spec)
- Security: CSP headers, HSTS, Fisher-Rao NATS validator bounds, .well-known/security.txt
- PtyTransport wiring for VT output path

**zig-syrup (2026-02-08→10)**: Massive module expansion:
- New modules: `entangle` (CNOT3 qutrit gates), `gf3_palette` (243-color), `splitmix_trit`, `fountain` (LT codes), `qrtp` (QR transport), `retty` (terminal), `supermap`, `disclosure`, `goi` (Geometry of Interaction), `lux_color`, `tapo_energy`, `transient`, `bci_receiver`
- 326 worlds in `world_enum`
- 610 skills embedded
- `goblins_ffi.zig` — 13 C ABI functions, cross-verified Scheme↔Zig↔Python

**asi (2026-02-08→10)**: 636 marketplace droids, `gf3-goblins.scm` (unified Guile implementation with Zig FFI backend)

**graded-optic (2026-02-08)**: Born this week — 4 commits, all Haskell, rigorous (self-corrected hogwash in commit 2)

**Key findings**:
- `plurigrid/bidder` contains **both Dart AND Kotlin AND Swift** (Flutter scaffold with native platform code) — perfect multiplatform seed
- `plurigrid/portal` is the live web frontend with Svelte + WebGPU + grading system — natural GT-style moldable inspector target
- `plurigrid/bayesian-breathing` is dormant (Screenpipe fork, last push Jul 2024) — candidate for resurrection via ClojureDart mobile wrapper
- `plurigrid/leprechauns` now has Gay.jl color assignments — green (H=120°) as root hue for capability objects

---

## Data Flow Architecture

```
┌──────────────────────────────────────────────────────────────┐
│ LAYER 1: BCI HARDWARE                                         │
│   nRF5340 Universal Receiver (bci_receiver.zig)               │
│   OpenBCI Cyton | Nudge Ultrasound | Intan RHS2116            │
└────────────────┬─────────────────────────────────────────────┘
                 │ BLE GATT / USB HID / OCapN-Syrup
                 ▼
┌──────────────────────────────────────────────────────────────┐
│ LAYER 2: MOBILE APP (Dart/Kotlin/ClojureDart)                │
│   BLE: flutter_blue_plus | Kable | Nordic BLE Library         │
│   FFI: dart:ffi | cinterop → zig-syrup C ABI                 │
│   UI:  Flutter widgets | Compose MP | re-dash widgets         │
│   Stream: Isolates | Coroutines+Flow | core.async             │
└────────────────┬─────────────────────────────────────────────┘
                 │ C ABI calls
                 ▼
┌──────────────────────────────────────────────────────────────┐
│ LAYER 3: ZIG-SYRUP NATIVE                                     │
│   bci_receiver.zig  → parse, classify, Fisher-Rao             │
│   goblins_ffi.zig   → GF(3) identity, did:gay, Passport      │
│   spatial_propagator → golden spiral coloring                 │
│   passport.zig       → BandPowers, PhenomenalState            │
└────────────────┬─────────────────────────────────────────────┘
                 │ gRPC / OCapN
                 ├───────────────────────────┐
                 ▼                           ▼
┌────────────────────────┐   ┌──────────────────────────────┐
│ KOS Robot Control      │   │ GT-Style Moldable Notebooks   │
│ (gRPC to UR5/Z-Bot)   │   │ (Lepiter-inspired, DuckDB)   │
└────────────────────────┘   └──────────────────────────────┘
```

---

## Commands

```bash
# Multiplatform
just flutter-bci-app        # Create Flutter BCI app scaffold
just kotlin-kmp-bci          # Create KMP BCI app scaffold
just cljd-bci-app            # Create ClojureDart BCI app

# FFI generation
just dart-ffi-gen             # Generate Dart FFI bindings from zig-syrup
just kotlin-cinterop-gen      # Generate Kotlin cinterop defs
just cljd-ffi-bridge          # Create ClojureDart FFI bridge

# GT-style moldable tools
just moldable-inspector OBJECT  # Create contextual view for object
just moldable-notebook FILE     # Create Lepiter-style live notebook
just moldable-search QUERY      # Universal spotter-style search

# Bayesian breathing
just breathe                   # Guided bayesian breathing session (say TTS)
just breathe-cycle N           # N breathing cycles with progressive depth

# Testing
just test-ffi-dart            # Test Dart→zig-syrup FFI
just test-ffi-kotlin          # Test Kotlin→zig-syrup cinterop
just test-ffi-cljd            # Test ClojureDart→zig-syrup FFI
```

---

## References

### Glamorous Toolkit
- [GT Book](https://book.gtoolkit.com/) — Complete documentation
- [feenk](https://feenk.com/) — Tudor Girba's company
- [Lepiter](https://lepiter.io/) — Knowledge management + live notebooks
- [Moldable Development](https://moldabledevelopment.com/) — Methodology
- [GitHub](https://github.com/feenkcom/gtoolkit) — Open source (MIT)

### Dart / Flutter
- [Dart 3 Records & Patterns](https://dart.dev/language/records)
- [dart:ffi](https://dart.dev/interop/c-interop) — C interop
- [flutter_zig](https://github.com/maks/flutter_zig) — Zig↔Dart FFI demo
- [Flutter BLE](https://pub.dev/packages/flutter_blue_plus)
- [Flutter gRPC](https://grpc.io/docs/languages/dart/)

### Kotlin Multiplatform
- [KMP](https://kotlinlang.org/docs/multiplatform.html)
- [cinterop](https://kotlinlang.org/docs/native-c-interop.html)
- [Kable](https://github.com/JuulLabs/kable) — KMP BLE library
- [Compose MP](https://kotlinlang.org/compose-multiplatform/)
- [Nordic BLE Library](https://github.com/NordicSemiconductor/Kotlin-BLE-Library)

### ClojureDart
- [ClojureDart](https://github.com/Tensegritics/ClojureDart)
- [re-dash](https://github.com/htihospitality/re-dash) — re-frame for Flutter
- [flutter-mx](https://github.com/kennytilton/flutter-mx) — Matrix Inside™
- [Calva ClojureDart](https://calva.io/clojuredart/)

### BCI
- [IronBCI](https://sciety.org/articles/activity/10.20944/preprints202507.1198.v1) — Open-source BCI with mobile SDK
- [SYNAPTICON](https://github.com/AlbertBarqueDuran/SYNAPTICON-Brain-Waves-to-Natural-Language-to-Aesthetics) — EEG→LLM→Aesthetics
- [brain-go-brrr](https://github.com/Clarity-Digital-Twin/brain-go-brrr) — EEG signal processing

---

## Related Skills

- `abductive-repl` (0) — Live exploratory programming
- `rama-gay-clojure` (0) — Clojure + visual debugging
- `kos-firmware` (+1) — Robot firmware platform
- `active-inference-robotics` (+1) — Bayesian robot control
- `cider-clojure` (+1) — Live Clojure REPL
- `catcolab-ologs` (-1) — Knowledge representation
- `stellogen` (0) — Smalltalk-influenced interaction nets
- `causal-inference` (0) — Bayesian reasoning

---

**Skill Name**: glamorous-moldable-multiplatform
**Type**: Moldable Development + Multiplatform Delivery
**Trit**: 0 (ERGODIC)
**GF(3)**: Conserved via Dart(+1) ⊗ Kotlin(0) ⊗ ClojureDart(-1) = 0
