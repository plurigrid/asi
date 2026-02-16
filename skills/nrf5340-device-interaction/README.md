# nRF5340 Device Interaction Skill

**Unified hardware abstraction + low-level security testing for Nordic nRF5340 DK**

This skill combines:
- **Hardware abstraction** (from `nrf5340-hardware` skill)
- **Blackhat patterns** (from `blackhat-go` skill)
- **GF(3) triadic coordination** for device state management
- **Production-ready Python** implementations

---

## Quick Start

### 1. Detect Device

```bash
python3 nrf5340_device_interaction.py
```

Output:
```
[*] nRF5340 Device Detection
======================================================================
  nrfjprog             ✓ FOUND
    → 960009873
  system_profiler      ✓ FOUND
  UART port            ✓ FOUND
    → /dev/ttyUSB0

[✓] nRF5340 DK CONNECTED and READY
Serial: 960009873
```

### 2. Probe Hardware State

```python
from nrf5340_device_interaction import SWDMemoryProbe, DebugPortAnalysis

probe = SWDMemoryProbe(device_serial="960009873")

# Check debug port status
debug_status = DebugPortAnalysis.check_debug_enabled(probe)
print(debug_status)

# Output:
# {
#   'raw_value': '0xffffffff',
#   'cpuniden': 65535,
#   'dbgporten': 65535,
#   'full_debug_enabled': False,
#   'risk_level': '🟢 SAFE'
# }
```

### 3. Integrated with Hardware Bundle

```bash
# Start with NATS color broadcasting enabled
ENABLE_NATS_BROADCASTER=1 python3 /Users/bob/.hardware-bundles/startup-coordinator.py
```

The coordinator will:
1. Auto-detect nRF5340 device
2. Probe hardware state via SWD
3. Broadcast device state with deterministic color index
4. Start telemetry monitoring

---

## Architecture

```
┌─────────────────────────────────────────────────────────┐
│  nRF5340 Device Interaction Skill                       │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  ┌──────────────────────────────────────────────────┐  │
│  │  DETECTION LAYER                                │  │
│  │  • nrfjprog -i (most reliable)                  │  │
│  │  • system_profiler SPUSBDataType (macOS)        │  │
│  │  • /dev/tty enumeration                         │  │
│  └──────────────────────────────────────────────────┘  │
│           ▼                                             │
│  ┌──────────────────────────────────────────────────┐  │
│  │  SWD MEMORY PROBE LAYER                          │  │
│  │  • nrfjprog --memrd / --memwr                   │  │
│  │  • Register access (32-bit)                     │  │
│  │  • UART, GPIO, BLE radio                        │  │
│  └──────────────────────────────────────────────────┘  │
│           ▼                                             │
│  ┌──────────────────────────────────────────────────┐  │
│  │  DEBUG PORT ANALYSIS                            │  │
│  │  • UICR Debug Control register (0xFF84)         │  │
│  │  • Secure bootloader status                     │  │
│  │  • Irreversible lock/unlock                     │  │
│  └──────────────────────────────────────────────────┘  │
│           ▼                                             │
│  ┌──────────────────────────────────────────────────┐  │
│  │  RADIO / BLE ANALYSIS                           │  │
│  │  • Radio state inspection                       │  │
│  │  • Frequency, TX power, CRC                     │  │
│  │  • BLE advertisement capture (via Bleak)        │  │
│  └──────────────────────────────────────────────────┘  │
│           ▼                                             │
│  ┌──────────────────────────────────────────────────┐  │
│  │  RTT CONSOLE                                    │  │
│  │  • Bidirectional debug channel                  │  │
│  │  • No UART/USB required                         │  │
│  │  • Real-time telemetry                          │  │
│  └──────────────────────────────────────────────────┘  │
│           ▼                                             │
│  ┌──────────────────────────────────────────────────┐  │
│  │  GF(3) STATE COORDINATION                       │  │
│  │  • Device trit (VALIDATOR / ERGODIC / GENERATOR)│  │
│  │  • Conservation: sum ≡ 0 (mod 3)                │  │
│  │  • Integration with startup-coordinator        │  │
│  └──────────────────────────────────────────────────┘  │
│                                                         │
└─────────────────────────────────────────────────────────┘
```

---

## Key Classes

### `nRF5340Detector`
Auto-detects device via multiple methods:
- `detect_via_nrfjprog()` — Most reliable
- `detect_via_system_profiler()` — macOS specific
- `detect_uart_port()` — Serial port enumeration
- `auto_detect()` — Tries all methods

### `SWDMemoryProbe`
Low-level memory access via Serial Wire Debug:
- `read_memory(address, size)` — Read bytes
- `write_memory(address, data)` — Write bytes
- `read_register(base, offset)` — Read 32-bit register
- `write_register(base, offset, value)` — Write 32-bit register

### `DebugPortAnalysis`
Debug port security status:
- `check_debug_enabled(probe)` — Current status
- `disable_debug(probe)` — IRREVERSIBLE lock

### `BLERadioAnalyzer`
Radio state inspection:
- `read_radio_state(probe)` — Current radio state

### `nRF5340StateController`
GF(3) state management:
- `probe_state(probe)` — Query actual hardware state
- `transition(new_trit, reason)` — Change state with conservation check

### `FirmwareManager`
Build and flash firmware:
- `build(app_path)` — Build via west
- `flash()` — Flash via J-Link
- `verify()` — Verify flashed firmware

### `RTTClient`
Real-Time Transfer console:
- `start()` — Connect to RTT
- `send_command(cmd)` — Send command to device
- `read_output(timeout)` — Read telemetry

---

## Usage Examples

### Example 1: Detect and Report Device Status

```python
from nrf5340_device_interaction import nRF5340Detector, SWDMemoryProbe

detector = nRF5340Detector()
if detector.auto_detect():
    probe = SWDMemoryProbe(detector.serial_number)

    # Read actual register values
    flash_protection = probe.read_register(0xFF8000, 0xFF80)
    bootloader_crc = probe.read_register(0xFF000, 0)

    print(f"Flash protection: {hex(flash_protection)}")
    print(f"Bootloader CRC: {hex(bootloader_crc)}")
```

### Example 2: Analyze Debug Port Security

```python
from nrf5340_device_interaction import (
    nRF5340Detector,
    SWDMemoryProbe,
    DebugPortAnalysis,
    nRF5340StateController
)

detector = nRF5340Detector()
detector.auto_detect()

probe = SWDMemoryProbe(detector.serial_number)
debug_status = DebugPortAnalysis.check_debug_enabled(probe)

if debug_status["full_debug_enabled"]:
    print("[!] WARNING: Full debug enabled (security risk)")
else:
    print("[✓] Debug port is locked (secure)")

# Check GF(3) state
controller = nRF5340StateController()
state = controller.probe_state(probe)
print(f"Device trit: {state.name}")
```

### Example 3: Build and Flash Firmware

```python
from nrf5340_device_interaction import FirmwareManager

manager = FirmwareManager(sdk_path="/path/to/nrf-connect-sdk")

if manager.build("nrf/applications/blinky"):
    if manager.flash():
        if manager.verify():
            print("[✓] Firmware successfully flashed and verified")
```

### Example 4: Real-Time Telemetry via RTT

```python
from nrf5340_device_interaction import RTTClient
import time

rtt = RTTClient()
if rtt.start():
    rtt.send_command("telemetry_enable")

    for i in range(10):
        output = rtt.read_output(timeout=0.5)
        if output:
            print(f"[{i}] {output.strip()}")
        time.sleep(1)

    rtt.stop()
```

---

## Integration with Startup Coordinator

The skill is automatically integrated with the hardware bundle startup coordinator:

```python
# In startup-coordinator.py

class BundleService:
    async def probe_hardware_state(self) -> dict:
        """Before starting, probe actual hardware state"""
        from nrf5340_device_interaction import (
            SWDMemoryProbe,
            DebugPortAnalysis,
            nRF5340StateController
        )

        probe = SWDMemoryProbe()
        debug_status = DebugPortAnalysis.check_debug_enabled(probe)
        controller = nRF5340StateController()
        state = controller.probe_state(probe)

        return {
            "debug_enabled": debug_status["full_debug_enabled"],
            "trit": state.value,
            "risk_level": debug_status["risk_level"]
        }

# Startup flow:
# 1. Auto-detect device
# 2. Probe hardware state
# 3. Broadcast state with color index
# 4. Start BLE gateway
# 5. Start telemetry monitor
```

---

## GF(3) Device State

The skill maintains GF(3) conservation across device states:

```
VALIDATOR (-1):
  • Secure bootloader locked
  • Debug port disabled (0xFF84 = 0xFFFFFFFF)
  • Flash protection enabled
  • Watchdog active
  ✓ SAFE: Cannot extract firmware or inject code

ERGODIC (0):
  • Normal application running
  • BLE advertising
  • UART telemetry
  • Crypto accelerator available
  ✓ NORMAL: Standard operation

GENERATOR (+1):
  • Debug enabled (0xFF84 = 0x00FFFFFF)
  • JTAG/SWD unlocked
  • Memory writeable
  • Firmware extractable
  🔴 DANGEROUS: Security perimeter is open
```

### Conservation Rule

At any moment:
```
Σ(trits) ≡ 0 (mod 3)

Example:
  Device (0) + Debugger (+1) + Test harness (-1) = 0 ✓
```

---

## Security Considerations

### ✅ Authorized Use Cases
- Penetration testing (with written engagement)
- CTF challenges and educational labs
- Own-device security research
- Firmware vulnerability analysis
- Hardware security assessments

### ❌ Prohibited Use Cases
- Unauthorized device access
- Firmware extraction for reverse engineering without license
- Credential harvesting via debug port
- Supply chain attack preparation

### Safe Practice

Always require signed authorization for security testing:

```python
class AuthorizedDeviceTest:
    def __init__(self, authorization_doc: str):
        # Verify written authorization before proceeding
        assert self._verify_authorization(authorization_doc)
```

---

## Files

| File | Purpose | Lines |
|------|---------|-------|
| `nrf5340_device_interaction.py` | Main Python library | 500+ |
| `nrf5340_device_interaction_skill.md` | Full technical documentation | 900+ |
| `README.md` | This file | — |

---

## Requirements

```bash
# Nordic nRF tools
brew install nrf-tools

# Python dependencies
pip3 install pyserial bleak

# Optional: J-Link RTT tools
# Download from Segger: https://www.segger.com/downloads/jlink/
```

---

## Commands

```bash
# Detect device and probe state
python3 nrf5340_device_interaction.py

# With integrated hardware bundle
ENABLE_NATS_BROADCASTER=1 python3 startup-coordinator.py

# Standalone RTT console
JLinkRTTViewer -device nrf5340_xxaa

# Read memory directly
nrfjprog --memrd 0x20000000 --w 64 -f NRF53

# Flash firmware
nrfjprog --program build/zephyr/zephyr.hex -f NRF53
nrfjprog --reset
```

---

## Skill Metadata

| Attribute | Value |
|-----------|-------|
| **Name** | nrf5340-device-interaction |
| **Type** | Hardware Abstraction + Security Testing |
| **Trit** | 0 (ERGODIC) — Coordinator |
| **GF(3) Role** | Device state management |
| **Status** | ✅ Production Ready |
| **Authorization** | Required for security testing |
| **Base Skills** | nrf5340-hardware, blackhat-go |

---

## Related Documentation

- **Hardware Bundle**: `/Users/bob/.hardware-bundles/`
- **nRF5340 Hardware Skill**: `/Users/bob/.claude/skills/nrf5340-hardware/nrf5340_skill.md`
- **Startup Coordinator**: `/Users/bob/.hardware-bundles/startup-coordinator.py`
- **NATS Color Broadcasting**: `/Users/bob/.hardware-bundles/NATS_COLOR_INDEX.md`

---

*Skill created with combined expertise from nrf5340-hardware and blackhat-go skills. Authorization required for security testing use cases.*
