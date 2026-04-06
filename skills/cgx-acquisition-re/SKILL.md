---
name: cgx-acquisition-re
description: Reverse engineer CGX Cognionics Quick-20 EEG acquisition protocol using MCP RE tooling (Binary Ninja, Ghidra, radare2)
version: 1.0.0
---

# CGX Acquisition Reverse Engineering

Unlock the CGX Quick-20 EEG headset's 500Hz acquisition mode by reverse engineering the proprietary protocol. The device streams impedance noise over USB serial; the real control path is Bluetooth, gated by CGX Acquisition software (Windows).

## Trigger Conditions

- User wants to reverse engineer EEG device firmware or protocol
- CGX/Cognionics Quick-20 acquisition mode unlock
- USB/Bluetooth device protocol sniffing and replay
- BCI hardware bring-up on unsupported platforms (macOS/Linux)

## Problem Statement

The Quick-20 connects via Bluetooth dongle → USB serial (`/dev/cu.usbserial-*`, 115200 default). In impedance mode:
- Streams unidirectionally at baud-rate-dependent throughput (115200→1.4kB/s, 921600→43.7kB/s)
- Entropy locked at 4.322 bits (maximal for 20ch) — pure noise
- Band power flat across δ/θ/α/β/γ — no spectral structure
- Full 24-bit range saturated (±8.4M counts vs ±5000 for real EEG)
- 36.4 Hz autocorrelation = impedance injection frequency
- Serial port ignores all input commands — unidirectional data-out

**Root cause**: Control channel is Bluetooth, not serial. CGX Acquisition software (Windows) sends the mode-switch command over Bluetooth, then EEG data appears on the serial stream at 500Hz.

## Three Paths to 500Hz

### Path A: Windows VM + CGX Acquisition (Pragmatic)
```
1. Install CGX Acquisition in Parallels/UTM
2. Plug in Bluetooth dongle, pair device (code: 0000)
3. Launch software → device appears under "Discovered Devices"
4. Click device name → Connect
5. Click "Start LabStreamingLayer" → LSL outlet on network (float32, µV, 500Hz)
6. Consume LSL stream from macOS via pylsl
```

### Path B: USB/Bluetooth Sniff + Replay (Medium)
```
1. On Windows VM: install Wireshark + USBPcap or Bluetooth HCI logger
2. Start capture before launching CGX Acquisition
3. Record the Bluetooth control sequence when "Connect" is clicked
4. Extract the mode-switch command bytes
5. Replay from macOS using PyBluez or bleak
```

### Path C: RE the CGX Acquisition .exe (Fun)
```
1. Locate CGX Acquisition binary (Windows installer from cgxsystems.com/documents)
2. Load into Binary Ninja or Ghidra via MCP
3. Find Bluetooth serial write calls (CreateFile → WriteFile on COM port, or WinBT API)
4. Trace from UI button handler ("Connect"/"Start") to the write call
5. Extract command bytes
6. Implement in Python with pyserial or bleak
```

## MCP Tooling Stack

All three RE tools are configured at user scope (`~/.claude/mcp/`):

| Tool | MCP Server | Tools | Config |
|------|-----------|-------|--------|
| Binary Ninja | `mrphrazer/binary-ninja-headless-mcp` | 181 | `~/.claude/mcp/binary-ninja.json` |
| Ghidra | `LaurieWired/GhidraMCP` bridge | 110 | `~/.claude/mcp/ghidra.json` |
| radare2 | `radareorg/radare2-mcp` | 30+ | Already in session |

### Additional RE MCP Servers (available)

| Server | Repo | Use Case |
|--------|------|----------|
| Reversecore MCP | `sjkim1127/Reversecore_MCP` | Orchestrates Ghidra + radare2 + YARA |
| BinaryAnalysis MCP | `Ap3x/BinaryAnalysis-MCP` | PE/ELF/Mach-O via LIEF |
| Agentic Malware Analysis | `mrphrazer/agentic-malware-analysis` | Structured RE workflow for Claude Code |

### mrphrazer Structured Workflow (Anthropic-recommended)

From Tim Blazytko's synthesis.to (2026-03-18):

1. **CLAUDE.md defines analysis phases** — triage → strings → imports → decompile → deep dive
2. Agent uses Binary Ninja HLIL in a loop, not just one-shot decompile
3. Structured workflow finds 2-3x more than unguided agent on same binary
4. Key: give explicit phases, not just tools

## Protocol Reference

### Quick-20r Specs (from manual)
- 24-bit simultaneous sampling, ADS1299 ADC
- 500 samples/second
- 0-131 Hz bandwidth, true DC coupling
- Bluetooth wireless (pairing code: 0000)
- Export: EDF, BDF, CSV, LSL
- Compatible: BrainVision Recorder, NeuroPype, LabStreaming Layer

### LSL Connector
- **Built-in**: CGX Acquisition has "Start LabStreamingLayer" button
- **Deprecated standalone**: `labstreaminglayer/App-Cognionics` (C++, 2018)
- **Python**: `idontknoweider/cognionics-lsl-loop` (archived, P300 BCI speller)

### BrainFlow
- No `CGX_QUICK20_BOARD` in current BrainFlow release (confirmed via enumerate)
- The deprecated LSL connector README mentions Bluetooth COM port at 0000

### Serial Protocol (impedance mode, observed)
- 24-bit samples, 3 bytes/channel, big-endian, two's complement
- No sync header (unlike OpenBCI 0xA0)
- Packet size = `n_channels × 3` bytes
- Baud-rate dependent: scales linearly from 9600 to 921600
- At 921600: ~729 Hz effective but still impedance noise

## Binary Ninja RE Workflow

```
# 1. Open CGX Acquisition binary
mcp__binary-ninja__session_open "/path/to/CGXAcquisition.exe"

# 2. Wait for analysis
mcp__binary-ninja__analysis_update_and_wait

# 3. Find Bluetooth/serial functions
mcp__binary-ninja__binary_search_text "CreateFile"
mcp__binary-ninja__binary_search_text "WriteFile"
mcp__binary-ninja__binary_search_text "BluetoothConnect"
mcp__binary-ninja__binary_search_text "WSAConnect"

# 4. Find UI strings
mcp__binary-ninja__binary_strings  # look for "Connect", "Start", "Acquisition"

# 5. Trace from string xrefs to write calls
mcp__binary-ninja__xref_data_refs_to <string_addr>
mcp__binary-ninja__function_callees <handler_addr>

# 6. Decompile the handler
mcp__binary-ninja__il_function <handler_addr> il_type="hlil"

# 7. Extract command bytes from the write buffer
mcp__binary-ninja__memory_read <buffer_addr> length=64
```

## Radare2 Quick RE

```
mcp__radare2__open_file "/path/to/CGXAcquisition.exe"
mcp__radare2__analyze level=2
mcp__radare2__list_strings filter="Connect|Acquisition|Start|COM|Bluetooth"
mcp__radare2__list_imports filter="CreateFile|WriteFile|Bluetooth|WSA"
mcp__radare2__xrefs_to address=<import_addr>
mcp__radare2__decompile_function address=<caller>
```

## Time-Unit Integration

The acquisition unlock determines which temporal scales are resolvable:

| Mode | Hz | Resolves | Cannot Resolve |
|------|-----|----------|----------------|
| Impedance (current) | 5.65-729 | hemodynamic (2s), specious present, helek | trit-tick, alpha, SSVEP |
| Acquisition (target) | 500 | ALL: trit-tick (2ms) through circadian | — |

## GF(3) Conservation

| Component | Trit | Role |
|-----------|------|------|
| CGX Acquisition .exe | -1 | Target (proprietary, to be opened) |
| MCP RE tooling | 0 | Bridge (analysis infrastructure) |
| Protocol replay | +1 | Liberation (cross-platform unlock) |
| **Sum** | **0** | ✓ |

## Related Skills

- `reverse-engineering` — General RE workflow, r2con speaker repos
- `ghidra-mcp` — Ghidra + radare2 MCP setup, port resurrection
- `bci-colored-operad` — BCI device pipeline, K⊣P adjunction
- `cyton-dongle` — OpenBCI Cyton connection (working reference)

## References

- CGX Quick-20r Manual: manualslib.com/manual/2075541
- CGX Documents: cgxsystems.com/documents
- labstreaminglayer/App-Cognionics: github.com (deprecated C++ connector)
- mrphrazer/agentic-malware-analysis: synthesis.to/2026/03/18
- mrphrazer/binary-ninja-headless-mcp: 181 tools, headless
- sjkim1127/Reversecore_MCP: Ghidra + radare2 + YARA orchestration
- Ap3x/BinaryAnalysis-MCP: LIEF-based PE/ELF/Mach-O parsing
