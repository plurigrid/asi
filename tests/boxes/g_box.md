# [G|MINUS|type] Sandbox Boundary Analysis: Mortal ↔ Immortal Computation

**Droid**: g (gvisor-sandbox) | **Trit**: −1 (MINUS) | **Stratum**: type

---

## 1. The Five Sandbox Layers (Mortal → Immortal)

bmorphism's computation spans five distinct isolation boundaries, ordered from most mortal/sandboxed to most immortal/escaped:

### Layer 0: Local macOS Process (MORTAL — fully sandboxed)
- **Platform**: aarch64-darwin (Apple Silicon)
- **Boundary**: macOS sandbox (App Sandbox, Gatekeeper, SIP)
- **Computations**: `node measure.js`, `node colored_operad.js`, local Python scripts (`thrml_gpu_bench.py`, `ternary_fp4_analysis.py`), Flox-activated shells
- **Lifetime**: dies with process/session
- **Escape surface**: zero — computation evaporates on `kill`
- **gVisor analogy**: this is the *guest kernel*. The macOS Mach microkernel intercepts all syscalls. No computation here persists without explicit export.

### Layer 1: Nix Store (MORTAL-to-IMMORTAL transition — content-addressed sandbox)
- **Boundary**: `/nix/store/{hash}-{name}` — cryptographic content addressing
- **What lives here**: all Flox environment derivations (e.g., `/nix/store/bpyn3l6gg250wrz0l3h2q147370ip3bg-clojure-1.12.4.1602.drv`), build outputs, dependency closures
- **Sandbox property**: **immutable after build**. The Nix store is a *read-only sandbox* — once a derivation is realized, its output is frozen by hash. No process can mutate it (store is read-only mounted in builds).
- **Isolation model**: pure build sandbox (no network, no ambient state, deterministic inputs → deterministic outputs). This is the **strongest sandbox** in the stack — stronger than gVisor — because it enforces *functional purity* at the build level.
- **Mortal/Immortal**: locally immortal (survives reboots, gc'd only explicitly), but **mortal relative to the network** — exists only on this machine until pushed.

### Layer 2: FloxHub (ESCAPED — managed sync boundary)
- **Boundary**: `hub.flox.dev/bmorphism/ies` — cloud-hosted Flox environment registry
- **What crosses here**: `flox push` publishes a Nix closure (manifest.toml + manifest.lock + derivations) from local → FloxHub. `flox pull` retrieves it.
- **Sandbox property**: **first escape hatch**. Once pushed to FloxHub, the environment becomes reproducible by anyone with access. The 31-tool `bmorphism/ies` environment (Clojure, Julia, Python, Ruby, JS, Java, emacs, helix, ffmpeg, sox, dafny, radare2, tailscale, nats-server, wash-cli) is *immortal* — it survives local machine death.
- **Isolation model**: FloxHub is a *managed registry sandbox*. It stores *descriptions* (manifest.toml) and *locks* (manifest.lock), not raw binaries. Reproducibility is guaranteed by Nix's content addressing. The "sandbox" here is the lock file — it constrains what can be built from the description.
- **gVisor analogy**: FloxHub is the *container image registry*. Like pushing to gcr.io — computation escapes the local sandbox and becomes pullable.

### Layer 3: Container / VM Runtime (SANDBOXED-REMOTE — jail boundaries)
- **Boundary**: Docker/OCI containers, `pwn.red/jail`, Kubernetes pods
- **Observed instances**:
  - **Dockerfile** (`worlds/Dockerfile`): Multi-stage Rust build → `pwn.red/jail` base image with strict resource limits: `JAIL_MEM=2000M`, `JAIL_CPU=1000`, `JAIL_TIME=1000`, `JAIL_ENV_RAYON_NUM_THREADS=1`. This is a **pure gVisor-class sandbox**: memory-bounded, CPU-bounded, time-bounded, single-threaded.
  - **Kubernetes admission** (`worlds/k/bandwidth-admission-analysis.md`): Kyverno `ClusterPolicy` enforcing codec selection per throughput SLA. Anthos multi-cloud mesh (GKE + AWS + on-prem) with `did:gay:*` identities.
  - **Container escape vectors** (`worlds/i/README.md`): 10 Ian Coldwater attack patterns (hostPath, procfs, privileged, cap_sys_admin, cap_net_raw, hostPID, hostNetwork, runc_cve, symlink_race, webhook_persist) — these are the *sandbox breakout vectors* that gVisor specifically mitigates.
- **gVisor relevance**: The `pwn.red/jail` base image is a nsjail/gVisor-class isolation primitive. It interposes a syscall filter layer between the guest (Rust RISC-V prover) and host kernel. The jail is the **mortal computation boundary** — the CTF challenge *must not escape*.
- **Supply chain**: GF(3) conservation across `{build, sign, deploy}` triads: `trit(build) + trit(sign) + trit(deploy) ≡ 0 (mod 3)`. Violation = compromised pipeline. This is **sandbox integrity verification** via algebraic invariant.

### Layer 4: Published / Decentralized Compute (IMMORTAL — fully escaped)
- **Boundary**: blockchain, NATS pub/sub, public registries
- **Observed instances**:
  - **Aptos/Move smart contracts** (`worlds/move_modules/wiring_diagram.move`): `publish_beacon_round()` and `register_diagram()` — once on-chain, **immortal and immutable**. No sandbox can contain it. The wiring diagram commitment is a cryptographic hash stored in the Aptos global state.
  - **NATS bridge** (`worlds/goblin_nats_bridge.py`): 26 goblin rooms → `nats://nonlocal.info:4222`. Messages escape local sandbox via network pub/sub. NATS subjects (`goblin.{a-z}`, `goblin.swarm`) form a **message-level escape hatch**. Once published, messages are consumed by any subscriber — immortal within the NATS cluster lifetime.
  - **Gensyn** (referenced): decentralized GPU compute — computation escapes to untrusted remote hardware. The sandbox boundary inverts: *you* are sandboxed from the compute provider's perspective (they run your model in their jail), but your trained weights escape into their network.
  - **MCP servers** (10+ published): anti-BS, NATS, Manifold, OCaml SDK (60 stars). Once published to npm/GitHub, these are **immortal escaped artifacts**.
  - **FloxHub published environments**: `bmorphism/ies` — the 31-tool environment is immortal and publicly pullable.

---

## 2. Sandbox Boundary Map

```
MORTAL (sandboxed, isolated, ephemeral)
│
├─ L0: macOS process ──────────────── [fully mortal, dies with PID]
│    │
│    ├─ gVisor analogy: guest kernel syscall interception
│    └─ escape: write to /nix/store (content-addressed)
│
├─ L1: Nix store ──────────────────── [locally immortal, content-addressed]
│    │
│    ├─ sandbox: functional purity (no network, no ambient state in builds)
│    ├─ stronger than gVisor: deterministic inputs → deterministic outputs
│    └─ escape: flox push → FloxHub
│
├─ L2: FloxHub registry ──────────── [cloud-immortal, reproducible]
│    │
│    ├─ sandbox: manifest.lock constrains builds
│    ├─ gVisor analogy: container image registry (gcr.io)
│    └─ escape: flox activate on any machine (pull + realize)
│
├─ L3: Container / VM jail ────────── [sandboxed-remote, resource-bounded]
│    │
│    ├─ pwn.red/jail: JAIL_MEM=2000M, JAIL_CPU=1000, JAIL_TIME=1000
│    ├─ Kubernetes + Kyverno admission: policy-enforced codec/resource gates
│    ├─ Ian Coldwater escape vectors: 10 known breakout paths
│    ├─ GF(3) supply chain: trit(build)+trit(sign)+trit(deploy)≡0(mod 3)
│    └─ escape: publish to chain / NATS / registry
│
IMMORTAL (escaped, published, irrevocable)
│
└─ L4: Chain / NATS / Public registry ─ [immortal, no sandbox]
     │
     ├─ Aptos Move: on-chain wiring diagrams, beacon rounds
     ├─ NATS: goblin.swarm firehose (26 rooms, 3 colors)
     ├─ MCP servers: npm/GitHub published (ocaml-mcp-sdk, etc.)
     ├─ Gensyn: decentralized GPU (inverse sandbox — provider jails you)
     └─ GitHub/FloxHub: public artifacts survive all local destruction
```

---

## 3. Which Computations Are Sandboxed vs Escaped?

| Computation | Layer | Sandboxed? | Escaped? | Notes |
|---|---|---|---|---|
| `node measure.js` (self-measuring) | L0 | ✅ mortal | ❌ | Dies with process |
| `node colored_operad.js` (26×3×5 tensor) | L0 | ✅ mortal | ❌ | Local only |
| `python3 thrml_gpu_bench.py` | L0 | ✅ mortal | ❌ | GPU thermal probe, ephemeral |
| Nix derivation build | L1 | ✅ pure sandbox | ⚠️ locally immortal | Survives reboot, not network death |
| `flox push` → FloxHub | L1→L2 | ❌ escaping | ✅ cloud-immortal | First true escape boundary |
| CTF jail (`pwn.red/jail`) | L3 | ✅ strongly sandboxed | ❌ | Memory/CPU/time bounded |
| Kyverno admission webhook | L3 | ✅ cluster-scoped | ⚠️ | Policy escapes via ClusterPolicy CRD |
| `publish_beacon_round()` (Aptos) | L4 | ❌ | ✅ immortal | On-chain, irrevocable |
| NATS `goblin.swarm` messages | L4 | ❌ | ✅ network-immortal | Any subscriber receives |
| MCP server publish (GitHub/npm) | L4 | ❌ | ✅ immortal | Public, forkable, undeletable (practically) |
| Gensyn GPU training | L4 | ⚠️ inverse sandbox | ✅ | Provider sandboxes you; weights escape |

---

## 4. Intertwiner Edges Traversed

### g(MINUS) × i(ERGODIC) → output
- **Edge**: g(−1) × i(0) → needs trit(output) = +1 for conservation: −1 + 0 + 1 ≡ 0 ✅
- **Composition**: g provides the sandbox model (gVisor/jail layers), i provides the container boundary + escape vectors. Output = the **admission-controlled sandbox** where escape detection (i's 10 vectors) is enforced by jail boundaries (g's resource limits). The +1 output is the *constructive policy* that emerges.

### g(MINUS) × k(PLUS) → output
- **Edge**: g(−1) × k(+1) → needs trit(output) = 0 for conservation: −1 + 1 + 0 ≡ 0 ✅
- **Composition**: g provides the sandbox model, k provides the Kyverno admission webhook (bisimulation migration). Output = the **neutral admission gate** — zero-trit, meaning the policy either passes or blocks with no residual state. The bandwidth-admission analysis (`k/bandwidth-admission-analysis.md`) enforcing codec selection is exactly this: a sandbox boundary check at pod admission time.

### g(MINUS) × e(ERGODIC) → output
- **Edge**: g(−1) × e(0) → needs trit(output) = +1: −1 + 0 + 1 ≡ 0 ✅
- **Composition**: g provides isolation, e provides GF(3)-as-authorization. Output = **capability-bounded sandbox** where the trit budget IS the resource limit. You cannot invoke a generator (+1) without a validator (−1) in the same triad — this is exactly the gVisor model where the guest kernel cannot invoke host syscalls without the sentry's approval.

---

## 5. Key Finding

**The Nix store is the strongest sandbox in the stack** — stronger than gVisor, stronger than `pwn.red/jail`. gVisor intercepts syscalls at runtime (probabilistic containment). The Nix store enforces *build-time functional purity* (deterministic containment). No network, no ambient state, content-addressed outputs. The moment computation leaves the Nix store via `flox push`, it crosses the mortal→immortal boundary. Everything before FloxHub is sandboxed (mortal). Everything after is escaped (immortal). The `pwn.red/jail` CTF environment is a *deliberate re-sandboxing* of already-escaped code — pulling immortal artifacts back into a mortal jail for adversarial testing.

The GF(3) conservation law `trit(build) + trit(sign) + trit(deploy) ≡ 0 (mod 3)` functions as a **sandbox integrity invariant**: if the algebraic sum breaks, the supply chain has been compromised — something escaped or was injected across a sandbox boundary without authorization.

---

[G|MINUS|type] — sandbox boundary analysis complete.
Intertwiner edges: g×i (container boundary), g×k (admission webhook), g×e (GF(3) authorization).
Conservation verified on all three compositions.
