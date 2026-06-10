---
name: cheerpx-self-hosting
description: Run x86 Linux binaries in the browser via WebAssembly. Self-host development environments, interpreters, and even this skill itself.
---
# CheerpX Self-Hosting Skill

Run x86 Linux binaries in the browser via WebAssembly. Self-host development environments, interpreters, and even this skill itself.

## Overview

[CheerpX](https://cheerpx.io/) is Leaning Technologies' x86-to-WebAssembly virtualization engine. Combined with [WebVM](https://github.com/leaningtech/webvm), it enables running full Linux systems in the browser with no server-side execution.

### Key Capabilities

| Feature | Description |
|---------|-------------|
| **x86 → WASM JIT** | Dynamic binary translation, handles self-modifying code |
| **Linux Syscalls** | Full syscall emulation layer (CheerpOS) |
| **Block Filesystem** | Virtual block-based file system with persistence |
| **Networking** | Tailscale/Headscale integration for inbound networking |
| **Performance** | 2x-10x slowdown vs native (varies by workload) |

### Self-Hosting Use Cases

1. **Run Nickel in browser** - Evaluate `.ncl` configs without local install
2. **Run Guile/Goblins** - Distributed capability actors in browser
3. **Run Julia** - Gay.jl SPI verification in browser
4. **Run the skill itself** - Meta-circular self-hosting

## Integration Points

### With Goblins/CapTP

The Goblins distributed actor system (from Spritely Institute) compiles to WASM via Hoot:

```scheme
;; From goblins.scm - Hoot FFI for browser interop
(use-modules (fibers promises)
             (goblins)
             (hoot ffi))

(define (spawn-vat/js name)
  (spawn-vat #:name name))

;; Capabilities can flow between WASM modules
(define (spawn/js constructor . args)
  (spawn
   (lambda (bcom)
     (wrap-external-function
      (apply call-external constructor args)))))
```

CheerpX enables running the *non-Hoot* parts of the ecosystem (x86 Guile, native libraries).

### With Nickel SPI

Configure CheerpX with deterministic, type-safe Nickel:

```nickel
let CheerpXConfig = {
  # Memory configuration
  memory | {
    initial_mb | Num | default = 512,
    max_mb | Num | default = 4096,
  },

  # Filesystem
  filesystem | {
    type | [| 'block, 'overlay, 'memory |] | default = 'overlay,
    persist | Bool | default = true,
    cache_size_mb | Num | default = 256,
  },

  # Networking
  network | {
    tailscale | Bool | default = false,
    headscale_server | optional | Str,
  },

  # SPI seed for deterministic state
  spi_seed | Num,
} in

let DevEnvironment = CheerpXConfig & {
  memory.initial_mb = 1024,
  filesystem.persist = true,
  spi_seed = 20251226,
} in

DevEnvironment
```

### With GF(3) Triadic Routing

Three execution tiers for capability-secure computing:

| Tier | Trit | Execution | Use Case |
|------|------|-----------|----------|
| **Browser** | -1 | CheerpX/WASM | Untrusted, sandboxed |
| **Edge** | 0 | BrowserPod | Semi-trusted, fast |
| **Server** | +1 | Native x86 | Trusted, full speed |

GF(3) conservation: Every capability request routes to exactly one tier, sum = 0.

## Usage

### Quick Start (HTML)

```html
<!DOCTYPE html>
<html>
<head>
  <script src="https://cxrtnc.leaningtech.com/1.0.6/cx.js"></script>
</head>
<body>
  <script type="module">
    const cx = await CheerpX.Linux.create({
      mounts: [
        { type: "ext2", path: "/", url: "https://example.com/rootfs.ext2" },
        { type: "devs", path: "/dev" },
      ],
    });

    // Run Nickel in the browser
    await cx.run("/usr/bin/nickel", ["eval", "/config.ncl"]);

    // Run Guile for Goblins
    await cx.run("/usr/bin/guile", ["-l", "/goblins.scm"]);
  </script>
</body>
</html>
```

### Self-Hosting This Skill

```bash
# Build a rootfs with skill dependencies
docker run -it debian:bookworm bash
apt-get update && apt-get install -y nickel guile-3.0 julia
# Export as ext2 image

# Serve via CheerpX
npx serve --cors -l 8080
```

### BrowserPod Integration

For full-stack environments with Node.js:

```javascript
import { BrowserPod } from '@aspect/browserpod';

const pod = await BrowserPod.create({
  runtime: 'node22',
  env: {
    GAY_SEED: '20251226',
    SPI_ENABLED: 'true',
  },
});

// Run skill in isolated browser pod
await pod.exec('npx', ['nickel', 'eval', 'spi_fast.ncl']);
```

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                      Browser Tab                             │
├─────────────────────────────────────────────────────────────┤
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐         │
│  │   Nickel    │  │   Goblins   │  │   Julia     │         │
│  │   Config    │  │   Actors    │  │   Gay.jl    │         │
│  └──────┬──────┘  └──────┬──────┘  └──────┬──────┘         │
│         │                │                │                 │
│  ┌──────▼────────────────▼────────────────▼──────┐         │
│  │              CheerpX x86→WASM JIT              │         │
│  │         (handles self-modifying code)          │         │
│  └──────────────────────┬────────────────────────┘         │
│                         │                                   │
│  ┌──────────────────────▼────────────────────────┐         │
│  │           CheerpOS (Linux Syscalls)            │         │
│  │    - Process management                        │         │
│  │    - Virtual filesystem (ext2/overlay)         │         │
│  │    - Networking (Tailscale tunnels)            │         │
│  └──────────────────────┬────────────────────────┘         │
│                         │                                   │
│  ┌──────────────────────▼────────────────────────┐         │
│  │              WebAssembly Runtime               │         │
│  │         (V8/SpiderMonkey/JavaScriptCore)       │         │
│  └───────────────────────────────────────────────┘         │
└─────────────────────────────────────────────────────────────┘
```

## SPI Guarantees

CheerpX + SPI ensures:

1. **Deterministic JIT**: Same x86 input → Same WASM output
2. **Reproducible Filesystem**: Content-addressed blocks
3. **Consistent State**: SPI seed propagates through all computations

```javascript
// Verify SPI in browser
const color1 = await cx.run("/usr/bin/julia", [
  "-e", "using Gay; println(gay_color(20251226, 1))"
]);
const color2 = await cx.run("/usr/bin/julia", [
  "-e", "using Gay; println(gay_color(20251226, 1))"
]);
console.assert(color1 === color2, "SPI violation!");
```

## Limitations

- **Performance**: 2-10x slower than native (acceptable for dev/testing)
- **Memory**: Browser memory limits apply
- **Networking**: Requires CORS proxy for some operations
- **GPU**: No GPU acceleration (WebGPU integration planned)

## References

- [CheerpX 1.0 Announcement](https://cheerpx.io/blog/cx-10)
- [WebVM GitHub](https://github.com/leaningtech/webvm)
- [BrowserPod Announcement](https://labs.leaningtech.com/blog/browserpod-annoucement)
- [Spritely Goblins](https://spritely.institute/goblins/)
- [Hoot Scheme→WASM Compiler](https://spritely.institute/hoot/)

## License

This skill follows the repository license. CheerpX requires commercial licensing for business use.
