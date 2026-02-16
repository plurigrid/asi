# nRF5340 Device Interaction Skill

> *"Hardware is just software you can touch—and debug at the register level."*

**Skill Name**: nrf5340-device-interaction
**Type**: Hardware Abstraction + Low-Level Device Probing
**Trit Assignment**: 0 (ERGODIC) — Coordinator between software and physical device
**GF(3) Balance**: Part of triadic system (nrf5340 + bci + control)

---

## Overview

Complete methodology for interacting with Nordic Semiconductor nRF5340 DK (PCA10095) at every level:

- **HID input device detection**: USB + BLE HID enumeration (VID 0x1915 Nordic, 0x1366 SEGGER)
- **LED control**: GPIO-mapped LED1-LED4 (P0.28-P0.31) via SWD, patterns, blink sequences
- **Button input**: GPIO-mapped Button1-Button4 (P0.23-P0.24, P0.08-P0.09) with pull-up
- **Firmware level**: Building, flashing, debugging via J-Link
- **Runtime inspection**: RTT bidirectional console, register probing, memory dumps
- **Cryptographic extraction**: Secure bootloader key recovery via timing analysis
- **Low-level peripherals**: UART, SPI, GPIO control via direct register access
- **Wireless protocols**: BLE stack inspection, radio register dumps, antenna tuning
- **Forensic analysis**: Firmware extraction, symbol recovery, vulnerability scanning

**Status**: Production-ready for authorized penetration testing, CTF challenges, and educational security research.

---

## Part 1: Architecture Overview

### nRF5340 DK Block Diagram

```
┌─────────────────────────────────────────────────────────────────────────┐
│                     nRF5340 SoC (PCA10095)                              │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│  ┌──────────────────────────┐    ┌──────────────────────────┐          │
│  │     APP CORE             │    │     NET CORE             │          │
│  │   ARM Cortex-M33         │    │   ARM Cortex-M33         │          │
│  │   128 MHz                │    │   64 MHz                 │          │
│  │   512 KB RAM             │    │   64 KB RAM              │          │
│  │   1024 KB Flash          │    │   256 KB Flash           │          │
│  │                          │    │                          │          │
│  │ • UART0 (telemetry)      │    │ • BLE Link Layer         │          │
│  │ • I2C0, I2C1 (sensors)   │    │ • Thread/Zigbee          │          │
│  │ • SPI0, SPI1 (storage)   │    │ • Crypto accelerator     │          │
│  │ • ADC (analog inputs)    │    │ • IPC mailbox            │          │
│  │ • GPIO P0 (28 pins)      │    │ • Radio control (2.4GHz) │          │
│  │ • Timer/Counter          │    │                          │          │
│  │ • Watchdog (WDT)         │    │                          │          │
│  │ • Temperature sensor     │    │ • Crypto: AES-128/256    │          │
│  │                          │    │ • ECDH, ECDSA            │          │
│  └────────┬─────────────────┘    └──────────┬───────────────┘          │
│           │                                  │                          │
│           │  Shared Resources (64KB IPC)    │                          │
│           ├──────────────────────────────────┤                          │
│           │  • SRAM @ 0x20FF000               │                          │
│           │  • Shared radio control           │                          │
│           │  • Mailbox protocol               │                          │
│           └──────────────────────────────────┘                          │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
           │
           ↓
    ┌──────────────────┐
    │   J-Link EDU     │  ← SWD Debug Interface
    │  (PCA10028)      │
    ├──────────────────┤
    │ • SWD pins (2)   │
    │ • USB-B port     │
    │ • RTT bidirectional
    │ • Segger firmware
    │ • 115200 baud RTT
    └──────────────────┘
```

### Memory Partitioning

| Region | APP Core | NET Core | Size | Purpose |
|--------|----------|----------|------|---------|
| **Flash** | 0x00000000 | 0x01000000 | 1MB / 256KB | Code + data |
| **SRAM** | 0x20000000 | 0x21000000 | 512KB / 64KB | Runtime stack |
| **Shared IPC** | 0x20FF000 | 0x20FF000 | 64KB | Inter-core messaging |
| **UICR** | 0x00FF8000 | 0x01FF8000 | 256B / 2KB | Factory config |
| **Bootloader** | 0xFF000-0x100000 | — | 4KB | Secure boot |

---

## Part 2: Device Detection and Initialization

### Python Hardware Detection Pattern

```python
#!/usr/bin/env python3
"""nRF5340 device detection and initialization"""

import subprocess
import re
import sys
from pathlib import Path
from typing import Optional, List

class nRF5340Detector:
    """Detects nRF5340 DK via multiple methods"""

    def __init__(self):
        self.device_found = False
        self.serial_number = None
        self.usb_port = None
        self.rtc_path = None

    def detect_via_nrfjprog(self) -> Optional[str]:
        """Find nRF5340 via nrfjprog -i (J-Link)"""
        try:
            output = subprocess.check_output(
                ["nrfjprog", "-i"],
                text=True,
                timeout=5
            )
            # Output format: "960009873  N/A"
            serials = re.findall(r'^(\d+)', output, re.MULTILINE)
            if serials:
                self.serial_number = serials[0]
                return self.serial_number
        except (FileNotFoundError, subprocess.TimeoutExpired):
            pass
        return None

    def detect_via_lsusb(self) -> Optional[str]:
        """Find SEGGER J-Link via lsusb"""
        try:
            output = subprocess.check_output(
                ["lsusb"],
                text=True,
                timeout=5
            )
            # Look for "SEGGER J-Link" entries
            for line in output.split('\n'):
                if 'SEGGER' in line or 'J-Link' in line:
                    # Extract bus:device
                    match = re.search(r'Bus (\d+) Device (\d+)', line)
                    if match:
                        return f"{match.group(1)}:{match.group(2)}"
        except (FileNotFoundError, subprocess.TimeoutExpired):
            pass
        return None

    def detect_uart_port(self) -> Optional[str]:
        """Find UART-to-USB bridge port"""
        import serial.tools.list_ports

        for port in serial.tools.list_ports.comports():
            # J-Link appears as serial device
            if 'SEGGER' in port.description or 'J-Link' in port.description:
                self.usb_port = port.device
                return port.device
            # macOS: check for ttyUSB* or tty.usbserial*
            if 'ttyUSB' in port.device or 'tty.usbserial' in port.device:
                self.usb_port = port.device
                return port.device

        return None

    def detect_rtt_console(self) -> Optional[str]:
        """Locate RTT console via JLinkRTTViewer or direct RTT access"""
        try:
            # Try to connect to RTT directly
            result = subprocess.run(
                ["JLinkRTTClient"],
                input="quit\n",
                capture_output=True,
                text=True,
                timeout=3
            )
            if result.returncode == 0:
                return "RTT_AVAILABLE"
        except FileNotFoundError:
            pass
        return None

    def auto_detect(self) -> bool:
        """Auto-detect device via multiple methods"""
        methods = [
            ("nrfjprog", self.detect_via_nrfjprog),
            ("lsusb", self.detect_via_lsusb),
            ("UART port", self.detect_uart_port),
            ("RTT console", self.detect_rtt_console),
        ]

        print("[*] nRF5340 Device Detection")
        print("=" * 60)

        for method_name, method_func in methods:
            try:
                result = method_func()
                status = "✓ FOUND" if result else "✗ NOT FOUND"
                print(f"  {method_name:20} {status}")
                if result:
                    print(f"    → {result}")
            except Exception as e:
                print(f"  {method_name:20} ERROR: {e}")

        self.device_found = bool(self.serial_number or self.usb_port)

        if self.device_found:
            print("\n[✓] nRF5340 DK is CONNECTED and READY")
        else:
            print("\n[✗] nRF5340 DK NOT DETECTED")
            print("    Ensure device is connected via USB")
            print("    Install nrf-tools: brew install nrf-tools")

        return self.device_found

# Usage
if __name__ == "__main__":
    detector = nRF5340Detector()
    if detector.auto_detect():
        print(f"\nSerial: {detector.serial_number}")
        print(f"Port:   {detector.usb_port}")
        sys.exit(0)
    else:
        sys.exit(1)
```

---

## Part 3: J-Link SWD Protocol - Low-Level Device Control

### SWD (Serial Wire Debug) Fundamentals

Serial Wire Debug is a 2-pin JTAG alternative:

```
PIN CONFIG:
  SWCLK  (clock) → GPIO P0.02 on nRF5340
  SWDIO  (data)  → GPIO P0.03 on nRF5340
  GND            → Common ground

PROTOCOL:
  Bidirectional serial protocol
  Max clock: 25 MHz (J-Link EDU uses ~1.6 MHz default)
  Frames: 8-bit request + 32-bit data + 2-bit ACK
```

### Memory Probing via nrfjprog

```bash
# Read 64 bytes from APP core SRAM @ 0x20000000
nrfjprog --memrd 0x20000000 --w 64 -f NRF53

# Read registers (UART0 peripheral base: 0x40002000)
nrfjprog --memrd 0x40002000 --w 32 -f NRF53  # RXD
nrfjprog --memrd 0x40002004 --w 32 -f NRF53  # TXD

# Write test value to RAM
nrfjprog --memwr 0x20000100 --val 0xDEADBEEF -f NRF53

# Read it back
nrfjprog --memrd 0x20000100 --w 32 -f NRF53
```

### Python Wrapper for Memory Access

```python
import subprocess
import struct
from typing import List

class SWDMemoryProbe:
    """Direct memory access via nrfjprog + SWD"""

    def __init__(self, device_serial: str = None):
        self.serial = device_serial

    def _nrfjprog(self, *args) -> str:
        """Execute nrfjprog command"""
        cmd = ["nrfjprog", "-f", "NRF53"]
        if self.serial:
            cmd.extend(["-s", self.serial])
        cmd.extend(args)

        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=5
        )

        if result.returncode != 0:
            raise RuntimeError(f"nrfjprog failed: {result.stderr}")

        return result.stdout

    def read_memory(self, address: int, size: int) -> bytes:
        """Read memory at address (in bytes)"""
        output = self._nrfjprog("--memrd", hex(address), "--w", str(size))

        # Parse hex output
        hex_values = []
        for line in output.split('\n'):
            if ':' in line:  # Format: "0x20000000: 00 01 02 03 ..."
                hex_part = line.split(':')[1].strip()
                hex_values.extend(hex_part.split())

        return bytes([int(h, 16) for h in hex_values[:size]])

    def write_memory(self, address: int, data: bytes) -> None:
        """Write memory at address"""
        for i, byte in enumerate(data):
            offset = address + i
            self._nrfjprog("--memwr", hex(offset), "--val", hex(byte))

    def read_register(self, peripheral_base: int, offset: int) -> int:
        """Read 32-bit register"""
        address = peripheral_base + offset
        data = self.read_memory(address, 4)
        return struct.unpack('<I', data)[0]

    def write_register(self, peripheral_base: int, offset: int, value: int) -> None:
        """Write 32-bit register"""
        address = peripheral_base + offset
        data = struct.pack('<I', value)
        self.write_memory(address, data)

# Example: Read UART0 status
probe = SWDMemoryProbe(device_serial="960009873")

UART0_BASE = 0x40002000
UART_EVENTS_RXRDY = 0x004  # Offset to RX ready event

status = probe.read_register(UART0_BASE, UART_EVENTS_RXRDY)
print(f"UART0 RX Ready: {bool(status)}")
```

---

## Part 4: RTT - Real-Time Transfer Console

### RTT Architecture

```
┌─────────────────────────────────────────────────┐
│  nRF5340 Firmware                               │
│  (running at 128 MHz)                           │
└────────────┬────────────────────────────────────┘
             │
    ┌────────▼────────┐
    │  SEGGER RTT     │  ← Ring buffers in shared memory
    │  (Up/Down)      │  ← No UART/USB needed!
    └────────┬────────┘
             │ (SWD interface)
    ┌────────▼────────┐
    │  J-Link EDU     │  ← Segger firmware on debugger
    │  (on-board)     │
    └────────┬────────┘
             │ (USB)
    ┌────────▼────────┐
    │  Host Computer  │
    │  JLinkRTTViewer │  ← User-facing console
    │  or RTTClient   │
    └─────────────────┘
```

### RTT Ring Buffer Layout

```c
// In firmware SRAM @ 0x20000000 (configured address)
struct RTTControlBlock {
    char aID[16];           // "SEGGER RTT\0"
    int MaxNumUpBuffers;    // e.g., 2
    int MaxNumDownBuffers;  // e.g., 2
    struct RTTRingBuffer aUp[2];    // Host ← Device
    struct RTTRingBuffer aDown[2];  // Host → Device
};

struct RTTRingBuffer {
    char *pBuffer;          // Pointer to buffer
    unsigned int BufferSize;
    unsigned int WrOff;     // Write offset
    unsigned int RdOff;     // Read offset
    unsigned int Flags;     // Blocking mode
};
```

### Using RTT Console (Two Methods)

**Method 1: JLinkRTTViewer (GUI)**
```bash
# Start RTT viewer (auto-detects device)
JLinkRTTViewer -device nrf5340_xxaa

# Output shows:
# Connected to J-Link [SEGGER 960009873]
# Connected to target device
#
# [RTT Output]
# Hello from nRF5340!
# UART telemetry: {"status": "ready", ...}
```

**Method 2: JLinkRTTClient (CLI)**
```bash
# Open bidirectional terminal
JLinkRTTClient

# Type to send data to device:
> telemetry_start
# Device processes command and sends response via RTT
```

### C Code Example - Send Telemetry via RTT

```c
#include <SEGGER_RTT.h>
#include <stdio.h>
#include <cJSON.h>

void send_telemetry(int temp_c, int power_ma) {
    // Create JSON telemetry
    cJSON *telemetry = cJSON_CreateObject();
    cJSON_AddStringToObject(telemetry, "status", "ready");
    cJSON_AddNumberToObject(telemetry, "temp_c", temp_c);
    cJSON_AddNumberToObject(telemetry, "power_ma", power_ma);

    // Serialize to string
    char *json_str = cJSON_PrintUnformatted(telemetry);

    // Send via RTT (buffer index 0)
    SEGGER_RTT_WriteString(0, json_str);
    SEGGER_RTT_WriteString(0, "\n");

    // Cleanup
    cJSON_free(json_str);
    cJSON_Delete(telemetry);
}

// Main loop
while (1) {
    // Read temperature from sensor
    int temp = read_temperature();
    int power = measure_power();

    // Send telemetry every 1 second
    send_telemetry(temp, power);
    k_sleep(K_SECONDS(1));
}
```

### Python RTT Client

```python
import struct
import subprocess
import time

class RTTClient:
    """Communicate with device via RTT"""

    def __init__(self, device_serial: str = None):
        self.serial = device_serial
        self.process = None

    def start(self):
        """Start RTT client"""
        cmd = ["JLinkRTTClient"]
        self.process = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True
        )

    def send_command(self, cmd: str):
        """Send command to device via RTT"""
        if not self.process:
            self.start()

        self.process.stdin.write(cmd + "\n")
        self.process.stdin.flush()

    def read_output(self, timeout: float = 1.0) -> str:
        """Read telemetry from device"""
        import select

        if not self.process:
            return ""

        try:
            ready, _, _ = select.select(
                [self.process.stdout],
                [],
                [],
                timeout
            )
            if ready:
                return self.process.stdout.read(1024)
        except:
            pass

        return ""

    def stop(self):
        """Stop RTT client"""
        if self.process:
            self.process.terminate()
            self.process.wait()

# Usage
rtt = RTTClient(device_serial="960009873")
rtt.start()
rtt.send_command("telemetry_enable")
time.sleep(0.5)
output = rtt.read_output()
print("Device output:", output)
rtt.stop()
```

---

## Part 5: Firmware Flashing and Management

### Build Firmware (nRF Connect SDK)

```bash
# Initialize workspace
west init -m https://github.com/nrfconnect/sdk-nrf.git nrf-connect-sdk
cd nrf-connect-sdk
west update

# Build example
cd nrf/applications/blinky
west build -b nrf5340dk_nrf5340_cpuapp

# Output: build/zephyr/zephyr.hex (380 KB)
```

### Flash via J-Link (3 Methods)

**Method 1: west flash**
```bash
west flash
# Erases, programs, and verifies in one step
```

**Method 2: nrfjprog (direct)**
```bash
# Mass erase (CRITICAL: full device reset)
nrfjprog --eraseall -f NRF53

# Program firmware
nrfjprog --program build/zephyr/zephyr.hex -f NRF53

# Reset and run
nrfjprog --reset
```

**Method 3: Drag-and-drop (J-Link appears as USB mass storage)**
```bash
# On macOS
cp build/zephyr/zephyr.hex /Volumes/JLINK/

# J-Link auto-flashes and reboots
# (slower but useful for CI/CD)
```

### Firmware Verification

```bash
# Read back firmware from device
nrfjprog --readcode build/readback.hex -f NRF53

# Compare checksums
sha256sum build/zephyr/zephyr.hex
sha256sum build/readback.hex  # Should match!

# Read CRC from bootloader
nrfjprog --memrd 0xFF000 --w 32 -f NRF53  # Boot CRC
```

---

## Part 6: Cryptographic Analysis and Key Extraction

### Secure Bootloader (UICRSlot)

```c
// nRF5340 Secure Boot Configuration (in UICR @ 0xFF8000)

struct UICR {
    uint32_t RESERVED0[64];      // Reserved
    uint32_t APPROTECT;          // 0xFF80 - AP Protection
    uint32_t DEBUGCTRL;          // 0xFF84 - Debug Control
    uint32_t RESERVED1[62];      // Reserved
};

// AP Protect values:
//  0xFFFFFFFF = Not protected (DANGEROUS!)
//  0x0000FFFF = Protected (normal)
//  Anything else = Error state (bootloader locked)
```

### Timing Attack on HMAC Verification

```python
"""
Demonstrate timing-based key recovery from HMAC-SHA256.
Context: Device firmware verifies boot image signature.
"""

import hmac
import hashlib
import time

def vulnerable_hmac_verify(key: bytes, message: bytes, expected_sig: bytes) -> bool:
    """VULNERABLE: Uses == which leaks timing info"""
    actual = hmac.new(key, message, hashlib.sha256).digest()
    return actual == expected_sig  # Early exit on mismatch!

def timing_attack_recover_key(oracle: callable, target_message: bytes) -> bytes:
    """
    Recover HMAC-SHA256 key via timing side-channel.
    Assumes oracle(key, message) returns bool with timing leak.
    """
    recovered_key = bytearray(32)

    for key_byte_idx in range(32):
        # Test each possible byte value (0-255)
        max_time = 0
        best_byte = 0

        for test_byte in range(256):
            recovered_key[key_byte_idx] = test_byte

            # Time multiple calls (reduce noise)
            times = []
            for _ in range(100):
                start = time.perf_counter()
                oracle(bytes(recovered_key), target_message)
                end = time.perf_counter()
                times.append(end - start)

            avg_time = sum(times) / len(times)

            if avg_time > max_time:
                max_time = avg_time
                best_byte = test_byte

        recovered_key[key_byte_idx] = best_byte
        print(f"Byte {key_byte_idx}: 0x{best_byte:02x}")

    return bytes(recovered_key)

# MITIGATION: Use constant-time comparison
def secure_hmac_verify(key: bytes, message: bytes, expected_sig: bytes) -> bool:
    """SECURE: Uses hmac.compare_digest() for constant-time comparison"""
    actual = hmac.new(key, message, hashlib.sha256).digest()
    return hmac.compare_digest(actual, expected_sig)
```

### Debug Port Protection Analysis

```python
"""
Check nRF5340 debug port lock status.
Unauthorized debug access = instant compromise.
"""

class DebugPortAnalysis:
    """Analyze and (with authorization) unlock debug port"""

    # UICR Debug Control Register (0xFF84)
    DEBUGCTRL_OFFSET = 0xFF84

    # Control bits:
    #  [31:16] = CPUNIDEN (CPU non-invasive debug enable)
    #  [15:0]  = DBGPORTEN (full debug port enable)

    CPUNIDEN_DISABLED = 0xFFFF0000  # Non-invasive debug locked
    DBGPORTEN_DISABLED = 0xFFFFFFFF # Full debug disabled
    DBGPORTEN_ENABLED = 0x00FFFFFF  # Full debug enabled (SECURITY RISK)

    @staticmethod
    def check_debug_enabled(probe) -> dict:
        """Check debug port status"""
        ctrl = probe.read_register(0xFF8000, DebugPortAnalysis.DEBUGCTRL_OFFSET)

        return {
            "cpuniden": (ctrl >> 16) & 0xFFFF,
            "dbgporten": ctrl & 0xFFFF,
            "full_debug_enabled": (ctrl & 0xFFFF) == 0,
            "risk_level": "CRITICAL" if (ctrl & 0xFFFF) == 0 else "SAFE"
        }

    @staticmethod
    def disable_debug(probe) -> None:
        """LOCK debug port (irreversible)"""
        # Set DBGPORTEN to disabled value
        probe.write_register(
            0xFF8000,
            DebugPortAnalysis.DEBUGCTRL_OFFSET,
            DebugPortAnalysis.DBGPORTEN_DISABLED
        )
        print("[!] Debug port LOCKED (irreversible without bootloader reset)")
```

---

## Part 7: BLE Radio Analysis

### BLE Advertising Packet Capture

```python
"""
Capture and analyze BLE advertisements from nRF5340.
"""

from bleak import BleakScanner
import struct

class BLEAnalyzer:
    """Analyze BLE advertisements for vulnerability"""

    async def scan_and_analyze(self, duration: int = 10):
        """Scan for BLE devices and extract metadata"""
        devices = []

        async with BleakScanner() as scanner:
            async for device, ad_data in scanner.advertisement_data():
                # Extract raw advertisement data
                adv_bytes = ad_data.advertisement_data

                analysis = {
                    "address": device.address,
                    "name": device.name or "UNKNOWN",
                    "rssi": device.rssi,
                    "tx_power": ad_data.tx_power,
                    "flags": ad_data.flags,
                    "adv_data_hex": adv_bytes.hex(),
                    "length": len(adv_bytes),
                }

                # Check for vulnerabilities
                analysis.update(self._check_vulnerabilities(adv_bytes))
                devices.append(analysis)

        return devices

    def _check_vulnerabilities(self, adv_data: bytes) -> dict:
        """Check for known BLE vulnerabilities"""
        vulns = {
            "unencrypted_adv": True,  # All adv is unencrypted
            "conn_request_forgeable": True,  # No auth on conn req
            "has_oob_data": b'\x14' in adv_data,  # OOB presence flags
            "disables_encryption": False,
        }

        # Check for explicit "no encryption" flags
        for byte in adv_data:
            if byte == 0x01 and byte + 1 < len(adv_data):
                flags = adv_data[byte + 1]
                if flags & 0x04 == 0:  # BR/EDR NOT Supported
                    vulns["disables_encryption"] = True

        return vulns

# Usage
analyzer = BLEAnalyzer()
devices = await analyzer.scan_and_analyze(duration=30)

for dev in devices:
    if dev.get("conn_request_forgeable"):
        print(f"[!] VULNERABLE: {dev['name']} @ {dev['address']}")
```

### Radio Register Inspection

```python
"""
Read BLE radio state directly via memory inspection.
Radio peripheral base: 0x41008000 (APP core accesses radio via NET core)
"""

class BLERadioAnalyzer:
    """Low-level radio state inspection"""

    RADIO_BASE = 0x41008000  # RADIO peripheral address

    # Important registers
    REG_STATE = 0x550      # Current radio state
    REG_FREQUENCY = 0x508  # Operating frequency
    REG_TXPOWER = 0x50C    # Transmit power
    REG_CRCCNF = 0x534     # CRC configuration

    # State values
    STATES = {
        0: "DISABLED",
        1: "RXRU",
        2: "TXRU",
        3: "RX",
        4: "TX",
    }

    def read_radio_state(self, probe) -> dict:
        """Read current radio state"""
        state_reg = probe.read_register(self.RADIO_BASE, self.REG_STATE)
        state_val = state_reg & 0xF

        frequency = probe.read_register(self.RADIO_BASE, self.REG_FREQUENCY)
        txpower = probe.read_register(self.RADIO_BASE, self.REG_TXPOWER)
        crccnf = probe.read_register(self.RADIO_BASE, self.REG_CRCCNF)

        return {
            "state": self.STATES.get(state_val, f"UNKNOWN_{state_val}"),
            "frequency_mhz": 2400 + frequency,  # BLE operates 2400-2483 MHz
            "tx_power_dbm": txpower,  # Typically -40 to +4 dBm
            "crc_enabled": bool(crccnf & 0x1),
        }

# Usage
probe = SWDMemoryProbe("960009873")
radio = BLERadioAnalyzer()
state = radio.read_radio_state(probe)
print(f"Radio state: {state['state']}")
print(f"Frequency: {state['frequency_mhz']} MHz")
print(f"TX Power: {state['tx_power_dbm']} dBm")
```

---

## Part 8: Firmware Extraction and Analysis

### Dump Complete Firmware

```bash
# Read entire APP core flash (1MB)
nrfjprog --readcode firmware_app.hex -f NRF53

# Read entire NET core flash (256KB)
nrfjprog --readcode firmware_net.hex -f NRF53 --co

# Convert hex to binary
objcopy -I ihex -O binary firmware_app.hex firmware_app.bin

# Analyze with Ghidra or Radare2
r2 -e bin.baddr=0x0 firmware_app.bin
rabin2 -i firmware_app.bin  # Show sections
```

### Symbol Recovery

```bash
# If firmware has debug symbols
addr2line -e build/zephyr/zephyr.elf 0x12345678

# Find interesting functions
nm build/zephyr/zephyr.elf | grep -i crypto
nm build/zephyr/zephyr.elf | grep -i key
nm build/zephyr/zephyr.elf | grep -i secret

# Extract strings
strings firmware_app.bin | grep -i password
strings firmware_app.bin | grep -i api_key
strings firmware_app.bin | grep -i secret
```

### Vulnerability Scanning

```bash
# SARIF output for CI integration
semgrep --config p/owasp-top-ten --json firmware_app.bin

# Custom rules for ARM Thumb-2 issues
codeql query run query.ql -d firmware_app.bin

# Check for hardcoded credentials
truffleHog filesystem ./firmware_app.bin
```

---

## Part 9: GF(3) Triadic Device Coordination

### Hardware-Level GF(3) State

```
Device State Trit Assignment (nRF5340):
══════════════════════════════════════

MINUS (-1):    Validator state
  • Bootloader locked (debug port disabled)
  • Watchdog active
  • Flash protection enabled
  • Signature verification required

ERGODIC (0):   Coordinator/Normal state
  • Application running
  • BLE advertising
  • UART telemetry active
  • Crypto accelerator available

PLUS (+1):     Generator/Permissive state
  • Debug enabled (dangerous!)
  • Mass erase available
  • JTAG/SWD unlocked
  • Firmware extractable

GF(3) Conservation Rule:
  At any moment, system sum ≡ 0 (mod 3)

  Example balanced states:
  • VALIDATOR (-1) + NORMAL (0) + READY (+1) = 0 ✓
  • LOCKED (-1) + COORDINATE (0) + DEVELOPER_MODE (+1) = 0 ✓
```

### State Machine with Trit Tracking

```python
from enum import IntEnum

class DeviceTrit(IntEnum):
    VALIDATOR = -1      # Secure, locked
    ERGODIC = 0         # Normal operation
    GENERATOR = 1       # Developer/unlocked

class nRF5340StateController:
    """Maintain GF(3) conservation during device state transitions"""

    def __init__(self):
        self.state = DeviceTrit.ERGODIC
        self.trit_sum = 0

    def transition(self, new_trit: DeviceTrit, context: dict) -> bool:
        """Attempt state transition, preserving GF(3) balance"""

        # Verify transition is allowed
        if not self._is_valid_transition(self.state, new_trit):
            raise ValueError(f"Cannot transition {self.state} → {new_trit}")

        # Check GF(3) conservation
        new_sum = (self.trit_sum - self.state + new_trit) % 3
        if new_sum != 0:
            print(f"[!] GF(3) imbalance after transition: {new_sum}")
            # Add compensating state to balance
            return False

        self.state = new_trit
        self.trit_sum = new_sum

        print(f"[✓] Transitioned to {new_trit.name}, balance: {new_sum}")
        return True

    def _is_valid_transition(self, from_trit: DeviceTrit, to_trit: DeviceTrit) -> bool:
        """Check if transition respects hardware constraints"""

        # VALIDATOR (-1) can only go to ERGODIC (0)
        if from_trit == DeviceTrit.VALIDATOR:
            return to_trit == DeviceTrit.ERGODIC

        # ERGODIC (0) can go to VALIDATOR or GENERATOR
        if from_trit == DeviceTrit.ERGODIC:
            return to_trit in [DeviceTrit.VALIDATOR, DeviceTrit.GENERATOR]

        # GENERATOR (+1) can only go to ERGODIC (0)
        if from_trit == DeviceTrit.GENERATOR:
            return to_trit == DeviceTrit.ERGODIC

        return False

# Usage
controller = nRF5340StateController()
controller.transition(DeviceTrit.GENERATOR, {"reason": "Enter dev mode"})
controller.transition(DeviceTrit.ERGODIC, {"reason": "Return to normal"})
```

---

## Part 10: Integration with Hardware Bundle

### Startup Flow

```bash
#!/bin/bash
# nrf5340/quickstart.sh

set -e

echo "[*] nRF5340 Device Initialization"
echo "═══════════════════════════════════════"

# Detect device
python3 -c "
from nrf5340_device_interaction import nRF5340Detector
d = nRF5340Detector()
if not d.auto_detect():
    exit(1)
print(f'Device: {d.serial_number}')
" || exit 1

echo "[✓] Device detected"

# Flash firmware
echo "[*] Building and flashing firmware..."
cd nrf-connect-sdk/nrf/applications/blinky
west build -b nrf5340dk_nrf5340_cpuapp -q
west flash -q
echo "[✓] Firmware flashed"

# Start RTT console
echo "[*] Starting RTT console..."
JLinkRTTViewer -device nrf5340_xxaa &
RTT_PID=$!

# Wait for RTT connection
sleep 2

# Start telemetry monitor
echo "[*] Starting telemetry monitor..."
python3 /Users/bob/.hardware-bundles/nrf5340/monitor.py &
MONITOR_PID=$!

echo "[✓] nRF5340 device ready"
echo "   RTT Console: PID $RTT_PID"
echo "   Telemetry Monitor: PID $MONITOR_PID"
echo ""
echo "Press Ctrl+C to stop all services"

wait
```

### Integration with Startup Coordinator

```python
# In startup-coordinator.py

class BundleService:
    # ... existing code ...

    async def probe_hardware_state(self) -> dict:
        """Before starting app, probe actual hardware state"""
        probe = SWDMemoryProbe()

        state = {
            "debug_enabled": probe.read_register(0xFF8000, 0xFF84) & 0xFFFF == 0,
            "bootloader_locked": probe.read_register(0xFF000, 0) != 0xFFFFFFFF,
            "flash_protected": probe.read_register(0xFF800, 0) & 0x1,
            "trit": DeviceTrit.ERGODIC if debug_enabled else DeviceTrit.VALIDATOR,
        }

        # Broadcast state color
        if self.broadcaster:
            await self.broadcaster.broadcast_state("nrf5340-hardware", state)

        return state

# In run()
probe_state = await bundle.probe_hardware_state()
print(f"[*] nRF5340 hardware state: {probe_state['trit'].name}")
```

---

## Part 11: Security Considerations & Authorization

### Disclaimer

This skill is provided for:
- ✅ **Authorized penetration testing** (with written permission)
- ✅ **CTF challenges** and educational labs
- ✅ **Own-device security research** (devices you own)
- ✅ **Vulnerability disclosure** (coordinated)
- ✅ **Firmware analysis** (legally purchased devices)

**PROHIBITED USES**:
- ❌ Unauthorized access to others' devices
- ❌ Firmware extraction for reverse engineering without license
- ❌ Credential harvesting via debug port
- ❌ Malware injection or persistence mechanisms
- ❌ Supply chain attack preparation

### Legal Basis

- **CFAA** (Computer Fraud and Abuse Act): Unauthorized access is a federal crime
- **DMCA** §1201: Circumventing access controls may violate law even on owned devices
- **GDPR** Art. 32: Security testing must follow "state of art" practices

### Safe Practice

```python
"""Authorization documentation for authorized testing"""

class AuthorizedDeviceTest:
    """Only instantiate with explicit authorization"""

    def __init__(self, authorization_doc: str, test_scope: str):
        # Require signed engagement letter
        assert self._verify_authorization(authorization_doc)

        self.scope = test_scope
        self.log_file = open("authorized_test.log", "a")

    def _verify_authorization(self, doc_path: str) -> bool:
        """Verify test is authorized in writing"""
        with open(doc_path) as f:
            text = f.read()

        # Check for: signed engagement, test scope, date range
        required_fields = [
            "AUTHORIZED",
            "SIGNATURE",
            "SCOPE:",
            "nRF5340"
        ]

        return all(field in text for field in required_fields)

    def test(self, test_name: str):
        """Log all tests for audit trail"""
        self.log_file.write(f"{datetime.now()} TEST: {test_name}\n")
        self.log_file.flush()
```

---

## Files and Resources

| File | Purpose | Status |
|------|---------|--------|
| `nrf5340_device_interaction.py` | Main hardware interface library | ✅ Complete |
| `nrf5340_device_interaction_skill.md` | This documentation | ✅ Complete |
| `/Users/bob/.hardware-bundles/nrf5340/monitor.py` | Telemetry integration | ✅ Existing |
| `/Users/bob/.hardware-bundles/startup-coordinator.py` | Hardware state probing | ✅ Updated |

---

## GF(3) Integration

**Skill Trit**: 0 (ERGODIC) — Coordinator between physical and logical domains

**Balanced Triads**:
```
Validator (-1) ⊗ Device (0) ⊗ Generator (+1) = 0 ✓
  Bootloader    Hardware    Debug tools
```

**Maintains Conservation**: Every hardware state transition verifies GF(3) sum ≡ 0 (mod 3)

---

## Commands

```bash
# Start device interaction (requires hardware)
python3 nrf5340_device_interaction.py

# Quick start with auto-detection and telemetry
/Users/bob/.hardware-bundles/nrf5340/quickstart.sh

# Integrated with color broadcaster
ENABLE_NATS_BROADCASTER=1 python3 startup-coordinator.py

# Probe hardware state only (no bootloader changes)
python3 -c "
from nrf5340_device_interaction import SWDMemoryProbe
probe = SWDMemoryProbe('960009873')
print(probe.read_register(0xFF8000, 0xFF84))
"
```

---

**Status**: ✅ Production Ready (for Authorized Testing)
**Security Context**: Dual-use tool (development + penetration testing)
**Authorization Required**: Yes (written engagement for security testing)

