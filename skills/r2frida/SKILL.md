---
name: r2frida
description: Dynamic instrumentation bridge — radare2 static analysis meets Frida runtime hooking via r2frida:// URI
version: 1.0.0
trit: 0
color: "#E50DA1"
seed: 4431712562122273656
invocation: 7
---

# r2frida

Static-to-dynamic bridge: use radare2 commands to drive Frida instrumentation on live processes.

## Installation

```bash
# r2frida IO plugin (requires radare2 6.0.x)
r2pm -ci r2frida

# Verify
r2 -L | grep frida
# io  frida  Frida io [r2frida://action/link/device/target]

# Companion packages
r2pm -ci r2frida-codeshare   # Frida codeshare browser
r2pm -ci r2frida-objection   # Objection integration
r2pm -ci r2flutch            # iOS app decryption
```

## URI Format

```
r2 frida://[action]/[link]/[device]/[target]
```

| Component | Options |
|-----------|---------|
| action | `attach`, `spawn`, `launch`, `list`, `apps` |
| link | `local`, `usb`, `remote host:port` |
| device | device-id (optional) |
| target | PID, process name, or bundle ID |

### Examples

```bash
# Attach to local process
r2 frida://attach/local//1234
r2 frida://attach/local//Safari

# Spawn on USB-connected iOS device
r2 frida://spawn/usb//com.example.app

# List apps on USB device
r2 frida://apps/usb//

# Remote frida-server
r2 frida://attach/remote/192.168.1.10:27042/target
```

## Core Commands (`:` prefix)

### Information & Enumeration

| Command | Description |
|---------|-------------|
| `:?` | r2frida help |
| `:i` | Target info |
| `:il` | List loaded libraries |
| `:ii` | List imports |
| `:iE` | List exports |
| `:is <lib>` | Symbols of a library |
| `:ic` | List classes (ObjC/Java) |
| `:ic <class>` | List methods of class |
| `:ip` | List protocols (ObjC) |

### Memory

| Command | Description |
|---------|-------------|
| `:dm` | List memory regions |
| `:dm.` | Current region info |
| `:dmm` | List modules with base addresses |
| `:/v <value>` | Search memory for value |
| `:/w <string>` | Search wide string |
| `:/x <hex>` | Search hex pattern |

### Tracing

| Command | Description |
|---------|-------------|
| `:dt <addr\|sym>` | Trace function |
| `:dt-*` | Remove all traces |
| `:dtf <addr> <fmt>` | Trace with format string |
| `:dtSf <addr\|sym>` | Stalker deep trace (follows subcalls) |
| `:dtm` | Monitor library loads |
| `:dtt` | Monitor thread lifecycle |
| `:e stalker.in=app` | Restrict stalking to app code |

**Format specifiers for `:dtf`:**
- `^` onEnter (default onExit)
- `+` backtrace
- `x` hex arg, `i` int arg
- `z` string pointer
- `O` ObjC object pointer

### Hooking & Interception

| Command | Description |
|---------|-------------|
| `:di0 <addr>` | Intercept, return 0 (skip original) |
| `:di1 <addr>` | Intercept, return 1 (skip original) |
| `:di-1 <addr>` | Intercept, return -1 (skip original) |
| `:dif0 <addr>` | Call original, then return 0 |
| `:dif1 <addr>` | Call original, then return 1 |
| `:db <addr>` | Set breakpoint |
| `:db- <addr>` | Remove breakpoint |
| `:dc` | Continue execution |

### Function Calls

| Command | Description |
|---------|-------------|
| `:dx <addr> [args]` | Call function |
| `:dxc <addr> [args]` | Call C function |
| `:dxo <class> <method> [args]` | Call ObjC method |
| `:dxs <num> [args]` | Invoke syscall |

### Process Control

| Command | Description |
|---------|-------------|
| `:dp` | PID |
| `:dpt` | List threads with entrypoints |
| `:dl <path>` | Load library into target |
| `:env` | Show environment variables |
| `:fd` | List file descriptors |

### JavaScript Evaluation

| Command | Description |
|---------|-------------|
| `:. <file.js>` | Load and run Frida script |
| `:eval <js>` | Evaluate inline JavaScript |
| `r2frida-compile <ts>` | Compile TypeScript to agent |

## Workflows

### Static-to-Dynamic: Identify Then Hook

```bash
# 1. Static analysis — find interesting functions
r2 /path/to/binary
> aaa
> afl~decrypt           # find decrypt functions
> pdf @ sym.decrypt_msg # read disassembly
> q

# 2. Dynamic — hook what we found
r2 frida://attach/local//target_process
> :dt sym.decrypt_msg   # trace it
> :dtf sym.decrypt_msg zx^  # trace with string arg + hex arg + backtrace
> :dc                   # resume
# ... trigger the function, see live args
```

### SSL Pinning Bypass (iOS)

```bash
r2 frida://spawn/usb//com.example.app
> :di0 sym.SSLSetSessionOption  # return 0 = success
> :di0 sym.SSLCreateContext
> :dc
```

### ObjC Method Tracing

```bash
r2 frida://attach/local//Safari
> :ic NSURLSession              # enumerate methods
> :dt "-[NSURLSession dataTaskWithRequest:completionHandler:]"
> :dc
```

### Memory Forensics

```bash
r2 frida://attach/local//target
> :dm                          # list memory regions
> :/w password                 # search for "password" (wide)
> :dmm                         # list modules
> s <addr>; px 256             # seek and hexdump
```

### Android/Dalvik

```bash
r2 frida://spawn/usb//com.example.android
> :ic com.example.android.CryptoHelper
> :dt "com.example.android.CryptoHelper.encrypt"
> :dc
```

## MCP Integration Architecture

```
┌─────────────────────────────────────────────────────────┐
│  Claude / AI Agent                                      │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  radare2 MCP (static)          frida MCP (dynamic)     │
│  ┌─────────────────┐          ┌─────────────────┐      │
│  │ open_file        │          │ spawn            │      │
│  │ analyze          │          │ attach           │      │
│  │ decompile        │◄────────►│ eval_js          │      │
│  │ list_functions   │ r2frida  │ list_apps        │      │
│  │ list_strings     │ bridge   │ get_frontmost    │      │
│  │ xrefs_to         │          │                  │      │
│  │ run_command      │          │                  │      │
│  └─────────────────┘          └─────────────────┘      │
│          │                            │                 │
│          └────────┬───────────────────┘                 │
│                   │                                     │
│          ┌────────▼────────┐                           │
│          │   r2frida://     │                           │
│          │   IO plugin      │                           │
│          │                  │                           │
│          │  : commands      │                           │
│          │  Stalker tracing │                           │
│          │  Interceptor     │                           │
│          └────────┬────────┘                           │
│                   │                                     │
│          ┌────────▼────────┐                           │
│          │  Target Process  │                           │
│          │  (local/usb/tcp) │                           │
│          └─────────────────┘                           │
└─────────────────────────────────────────────────────────┘
```

### Via radare2 MCP run_command

Since `run_command` passes raw r2 commands, r2frida commands work directly when the session is opened with a `frida://` URI:

```
open_file("frida://attach/local//Safari")
run_command(":il")          # list loaded libraries
run_command(":dt malloc")   # trace malloc
run_command(":dc")          # continue
```

## GF(3) RE Skill Ecosystem

```
MINUS (-1)                    ERGODIC (0)               PLUS (+1)
─────────────────────────────────────────────────────────────────
radare2-hatchery              r2frida                   blackhat-go
  static analysis               bridge                    offensive
  decompilation                 : commands                techniques
  trit: -1                      trit: 0                   trit: +1

dwarf-expert                                            cantordust-viz
  debug formats                                           binary viz
  trit: -1                                                trit: +1

narya-proofs
  formal verify
  trit: -1
```

### Triads

```
radare2-hatchery (-1) + r2frida (0) + blackhat-go (+1) = 0 ✓
dwarf-expert (-1)     + r2frida (0) + cantordust-viz (+1) = 0 ✓
narya-proofs (-1)     + r2frida (0) + blackhat-go (+1) = 0 ✓
```

### r2con Speaker Network

| Speaker | Handle | Specialty | Trit |
|---------|--------|-----------|------|
| pancake | @trufae | r2 creator, r2frida | 0 |
| oleavr | @oleavr | Frida creator | +1 |
| iGio90 | @AAndresG90 | Dwarf debugger (r2frida GUI) | 0 |
| enovella | @enovella | r2frida wiki, mobile RE | 0 |
| hexploitable | @hexploitable | iOS r2frida | -1 |
| cryptax | @cryptax | Android droidlysis | -1 |
| bmorphism | @bmorphism | r2 Zignatures (2020) | 0 |
| as0ler | @asoler | iOS instrumentation | +1 |

## Related Skills

- `radare2-hatchery` — Static analysis MCP server
- `reverse-engineering` — Multi-tool RE (Ghidra, IDA, r2)
- `dwarf-expert` — DWARF debug format analysis
- `cantordust-viz` — Binary visualization
- `blackhat-go` — Offensive security techniques
- `aflpp` — AFL++ fuzzing
- `entry-point-analyzer` — Binary entry point analysis
- `harness-writing` — Fuzzing harness creation

## References

- [r2frida GitHub](https://github.com/nowsecure/r2frida)
- [r2frida Wiki](https://github.com/enovella/r2frida-wiki)
- [Frida Handbook - r2frida](https://learnfrida.info/r2frida/)
- [Radare2 Book - r2frida](https://book.rada.re/r2frida/intro.html)
- [OWASP MASTG r2frida](https://mas.owasp.org/MASTG/tools/generic/MASTG-TOOL-0036/)
- [Frida MCP Server](https://github.com/zhizhuodemao/frida-mcp)
- [Ringzer0 r2frida Training](https://ringzer0.training/)

## SDF Interleaving

**Primary Chapter**: 7. Propagators

r2frida propagates constraints bidirectionally between static knowledge (what the binary *is*) and dynamic observation (what the process *does*). The `:` command interface is a propagator network where each trace/hook/intercept is a cell that merges information from both directions.

### GF(3) Balanced Triad

```
r2frida (0) + SDF.Ch7 (0) + [balancer] (0) = 0
```

**Skill Trit**: 0 (ERGODIC - the bridge that makes static and dynamic cohere)
