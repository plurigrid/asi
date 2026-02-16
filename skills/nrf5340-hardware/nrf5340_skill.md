# nRF5340 Hardware Abstraction Skill

> *"Dual Cortex-M33 cores + Bluetooth 5.4 + Python async = hardware as API"*

## Overview

**nRF5340 Hardware Abstraction Skill** provides production-ready Python patterns for controlling Nordic Semiconductor's nRF5340 DK: a dual-core Bluetooth 5.4 + Thread + Zigbee SoC.

- **Primary Use**: Wireless sensor coordination, BLE device scanning, multi-protocol stacks
- **Architecture**: App core (128 MHz) + Network core (64 MHz) + shared 2.4GHz radio
- **Integration**: MQTT telemetry, async Python, real-time color broadcasting
- **GF(3) Role**: ERGODIC (0) — Hardware coordinator

---

## Part 1: Core Architecture

### Dual Cortex-M33 System

```
┌─────────────────────────────────────┐
│      nRF5340 SoC (PCA10095)        │
├─────────────────────────────────────┤
│                                     │
│  APP Core          NET Core         │
│  ─────────────     ────────────     │
│  • 128 MHz         • 64 MHz         │
│  • 512 KB RAM      • 64 KB RAM      │
│  • 1024 KB Flash   • 256 KB Flash   │
│  • DSP, FPU        • Radio ctrl     │
│  • UART, SPI       • Crypto engine  │
│  • I2C, ADC, GPIO  • IPC mailbox    │
│                                     │
│  ┌─────────────────────────────┐   │
│  │  Shared Resources            │   │
│  ├─────────────────────────────┤   │
│  │ • 64 KB IPC SRAM (0x20FF000) │   │
│  │ • 2.4 GHz Radio (shared)     │   │
│  │ • Crypto accelerator         │   │
│  │ • UICR (user info config)    │   │
│  └─────────────────────────────┘   │
│                                     │
└─────────────────────────────────────┘
          ↓ USB-C J2 Port
      J-Link EDU (SWD debug)
```

### Memory Partitioning

| Region | APP Core | NET Core | Size | Purpose |
|--------|----------|----------|------|---------|
| Flash | 0x00000000 | 0x01000000 | 1MB / 256KB | Code + data |
| SRAM | 0x20000000 | 0x21000000 | 512KB / 64KB | Runtime stack |
| Shared IPC | 0x20FF000 | 0x20FF000 | 64KB | Inter-core messaging |
| UICR | 0x00FF8000 | 0x01FF8000 | 256B / 2KB | Factory config |

### Peripheral Map

**App Core Controls:**
- UART0 (serial telemetry @ 115200)
- I2C0, I2C1 (sensors, RTC)
- SPI0, SPI1 (displays, storage)
- ADC (analog inputs)
- GPIO P0 (28 pins: LEDs, buttons)
- Timer/Counter (time-critical tasks)

**Network Core Controls:**
- BLE Link Layer (advertisement, scanning)
- Thread/Zigbee stack
- Crypto accelerator (AES, ECDH)
- Mailbox (IPC to app core)

---

## Part 2: Development Workflow

### Build System (nRF Connect SDK)

```
nrf-connect-sdk/
├── zephyr/              # RTOS & drivers
├── nrf/                 # Nordic-specific components
│   ├── boards/          # Board definitions (nrf5340dk)
│   ├── drivers/         # BLE, radio, GPIO
│   ├── subsys/          # NVS, DFU, profiler
│   └── lib/             # Libraries
├── west.yml             # Manifest (dependencies)
└── applications/        # Sample projects
    ├── blinky/          # Hello world
    ├── ble_central/     # BLE scanner
    └── ble_peripheral/  # BLE advertiser
```

**Build Commands:**

```bash
# Initialize workspace
west init -m https://github.com/nrfconnect/sdk-nrf.git nrf-connect-sdk
cd nrf-connect-sdk
west update

# Build for nRF5340 DK
cd nrf-connect-sdk/nrf/applications/blinky
west build -b nrf5340dk_nrf5340_cpuapp
west flash  # Flashes via J-Link

# Custom project
west create-app myapp
cd myapp
west build -b nrf5340dk_nrf5340_cpuapp
```

### J-Link Flashing

```bash
# Check J-Link connection
nrfjprog -i                    # List connected devices

# Erase and flash
nrfjprog --eraseall -f NRF53
nrfjprog --program build/zephyr/zephyr.hex -f NRF53
nrfjprog --reset

# Drag-and-drop (USB mass storage)
cp build/zephyr/zephyr.hex /Volumes/JLINK/
# Auto-flashes when file appears
```

### RTT Console (Real-Time Transfer)

J-Link provides bidirectional debug channel without serial port:

```bash
# Terminal 1: Run RTT viewer
JLinkRTTViewer -device nrf5340_xxaa

# Terminal 2: Firmware prints to RTT
# In C code:
#include <SEGGER_RTT.h>
SEGGER_RTT_printf(0, "Hello from RTT\n");
```

---

## Part 3: BLE Stack (Connectivity Firmware)

### Discovery Flow

```
┌─────────────────────┐
│  BLE Advertiser     │ ← APP Core sends ADV_IND packets
│  (Peripheral)       │   Contains: Name, UUID, power level
└──────────┬──────────┘
           │ 2.4 GHz Radio
           ↓
┌──────────────────────┐
│  BLE Scanner         │ ← NET Core receives PDUs
│  (Central)           │   Parses: Address, RSSI, name
└──────────┬───────────┘
           │
           ↓
┌──────────────────────┐
│  GATT Connection     │
│  (Service discovery) │
└──────────────────────┘
```

### Advertising Packet Format

```
┌──────────────────────────────────────┐
│ ADV_IND (Connectable Undirected)     │
├──────────────────────────────────────┤
│ Flags: 0x06 (LE General Discoverable)│
│ Name: "myDevice"                     │
│ TX Power: -5 dBm                     │
│ Manufacturer Data: custom payload    │
│ Service UUID: 0x180A (Device Info)   │
└──────────────────────────────────────┘
```

### GATT Services (Standard)

| UUID | Service | Characteristics |
|------|---------|-----------------|
| 0x180A | Device Information | Manufacturer, Model, Serial, FW Version |
| 0x180F | Battery Service | Battery Level (0-100%) |
| 0x181C | User Data | Custom user-defined data |

---

## Part 4: Python Hardware Abstraction

### Device Detection Pattern

```python
import subprocess
import re

def detect_nrf5340():
    """Find nRF5340 via J-Link"""
    try:
        output = subprocess.check_output(
            ["nrfjprog", "-i"],
            text=True
        )
        # Output format: 960009873  (serial number)
        serials = re.findall(r'^\d+', output, re.MULTILINE)
        return serials
    except FileNotFoundError:
        return []  # nrfjprog not installed

def get_serial_port():
    """Find UART-to-USB bridge"""
    import serial.tools.list_ports
    for port in serial.tools.list_ports.comports():
        if 'SEGGER' in port.description or 'J-Link' in port.description:
            return port.device
    return None
```

### UART Telemetry Parser

```python
import json
import serial
import asyncio

class nRF5340Monitor:
    def __init__(self, port="/dev/ttyUSB0", baudrate=115200):
        self.ser = serial.Serial(port, baudrate, timeout=1.0)
        self.buffer = ""

    async def read_events(self):
        """Parse JSON events from firmware"""
        while True:
            data = self.ser.read(1024).decode('utf-8', errors='ignore')
            self.buffer += data

            # Split on newlines
            while '\n' in self.buffer:
                line, self.buffer = self.buffer.split('\n', 1)

                try:
                    event = json.loads(line)
                    yield event
                except json.JSONDecodeError:
                    continue

            await asyncio.sleep(0.01)
```

### BLE Scanner (via Bleak)

```python
from bleak import BleakScanner, BleakClient
import asyncio

class BLEGateway:
    async def scan_devices(self, timeout=10):
        """Discover BLE peripherals"""
        scanner = BleakScanner()
        devices = await scanner.discover(timeout=timeout)

        for device in devices:
            yield {
                'address': device.address,
                'name': device.name,
                'rssi': device.rssi,
                'services': list(device.metadata.get('uuids', []))
            }

    async def read_battery(self, address):
        """Read battery level from GATT"""
        async with BleakClient(address) as client:
            # Standard Battery Service UUID
            battery_uuid = "00002a19-0000-1000-8000-00805f9b34fb"
            value = await client.read_gatt_char(battery_uuid)
            return int.from_bytes(value, 'little')
```

---

## Part 5: Inter-Processor Communication (IPC)

### Shared Memory Layout (64KB @ 0x20FF000)

```
┌──────────────────────────┐  0x20FF000
│  APP ↔ NET IPC Region    │
├──────────────────────────┤
│  Mailbox Channels (4)    │  32 bytes each
│  • APP→NET               │
│  • NET→APP               │
│  • Status                │
│  • Reserved              │
│                          │
│  Shared Buffers          │  ~64KB total
│  • BLE State             │
│  • ADV Packets           │
│  • SCAN Results          │
│  • Custom Data           │
│                          │
└──────────────────────────┘  0x20FFFFF
```

### Message Protocol

```python
# APP Core → NET Core
IPC_MSG_START_ADV = 0x01
IPC_MSG_START_SCAN = 0x02
IPC_MSG_STOP_SCAN = 0x03
IPC_MSG_CONNECT = 0x04

# NET Core → APP Core
IPC_EVT_ADV_STARTED = 0x80
IPC_EVT_DEVICE_FOUND = 0x81
IPC_EVT_CONNECTED = 0x82
IPC_EVT_DISCONNECTED = 0x83
```

---

## Part 6: Power Management

### Current Draw Baseline

| State | Current | Duration |
|-------|---------|----------|
| Sleep (IDLE) | 2-5 µA | System inactive |
| BLE ADV (1Hz) | 8-15 mA | Every 1 second |
| BLE SCAN (100ms) | 12-18 mA | Listening |
| Connected (idle) | 25-35 mA | No transfers |
| Data transfer | 50-80 mA | Peak on Rx/Tx |

### Sleep Modes

```c
// In C firmware:
pm_state_set(PM_STATE_STANDBY, PM_ALL_SUBSTATES);  // Light sleep
k_sleep(K_SECONDS(10));

// Wakeup via:
// - GPIO interrupt (button)
// - Timer interrupt
// - BLE event (connection)
```

---

## Part 7: Common Issues & Solutions

| Issue | Cause | Solution |
|-------|-------|----------|
| "AHB-AP protected" | Flash protection enabled | `nrfjprog --eraseall` (mass erase) |
| NET Core won't start | IPC mailbox not configured | Call `nrf_802154_init()` in app core |
| RTT data corrupted | Baud rate mismatch | Check: 115200, 8N1 |
| BLE won't advertise | Radio not initialized | Enable in `prj.conf`: `CONFIG_BT_ENABLED=y` |
| High power drain | ADV interval too short | Increase to ≥100ms |
| Serial port missing | J-Link not detected | `nrfjprog -i` or `ls /dev/tty*` |

---

## Part 8: Production Patterns

### Configuration File (prj.conf)

```ini
# Bluetooth
CONFIG_BT_ENABLED=y
CONFIG_BT_PERIPHERAL=y
CONFIG_BT_CENTRAL=y
CONFIG_BT_GAP_AUTO_UPDATE_CONN_PARAMS=y

# Serial/UART
CONFIG_SERIAL=y
CONFIG_UART_NRFX=y
CONFIG_UART_CONSOLE=y

# Power management
CONFIG_PM=y
CONFIG_PM_POLICY_DEFAULT_PM_STATES=y

# Logging
CONFIG_LOG=y
CONFIG_LOG_BACKEND_UART=y

# Thread (if using)
CONFIG_OPENTHREAD_ENABLED=y
```

### Minimal BLE Advertiser

```c
#include <zephyr/kernel.h>
#include <zephyr/bluetooth/bluetooth.h>
#include <zephyr/bluetooth/hci.h>

static const struct bt_data ad[] = {
    BT_DATA_BYTES(BT_DATA_FLAGS, (BT_LE_AD_GENERAL | BT_LE_AD_NO_BREDR)),
    BT_DATA(BT_DATA_NAME_COMPLETE, "nrf5340-hw", 10),
};

void main(void) {
    int err = bt_enable(NULL);
    if (err) return;

    err = bt_le_adv_start(BT_LE_ADV_CONN_NAME, ad, ARRAY_SIZE(ad), NULL, 0);
    if (err) return;

    printk("BLE advertising started\n");
}
```

---

## Part 9: Integration with Our Bundle

### Startup Coordinator Integration

```python
# In startup-coordinator.py
class nRF5340Service:
    """Hardware abstraction layer"""

    async def init(self):
        # Detect device
        if not self.detect_device():
            raise RuntimeError("nRF5340 not found")

        # Start monitor service
        self.monitor = nRF5340Monitor(await self.get_serial_port())

        # Start BLE gateway
        self.ble = BLEGateway()

        # Start MQTT broadcaster
        self.mqtt = MQTTClient("localhost", 1883)

    async def start(self):
        tasks = [
            self.monitor_telemetry(),
            self.scan_ble_devices(),
            self.publish_mqtt_state(),
        ]
        await asyncio.gather(*tasks)
```

### Color Index Mapping

```python
# From nats_color_broadcaster.py
state = {
    'status': 'advertising',
    'ble_devices': 5,
    'power_ma': 18,
    'temp_c': 35.2
}

# State → deterministic color[index]
index = detector.index_for_state(state)
hex_color = detector.color_at(index)

# Broadcast: hardware.nrf5340.color.{index}
await broadcaster.broadcast_state('nrf5340-monitor', state)
```

---

## Commands

### Start Hardware Bundle

```bash
# Option 1: Full stack with color broadcasting
ENABLE_NATS_BROADCASTER=1 \
  python3 /Users/bob/.hardware-bundles/startup-coordinator.py

# Option 2: nRF5340 only
/Users/bob/.hardware-bundles/nrf5340/quickstart.sh

# Option 3: Color monitor (no hardware needed)
python3 /Users/bob/.hardware-bundles/color_index_monitor.py
```

### Build & Flash Firmware

```bash
# Using nRF Connect SDK
cd nrf-connect-sdk/nrf/applications/blinky
west build -b nrf5340dk_nrf5340_cpuapp
west flash

# Using J-Link directly
nrfjprog --eraseall -f NRF53
nrfjprog --program firmware.hex
nrfjprog --reset
```

### Debug & Monitor

```bash
# RTT Console (real-time debug output)
JLinkRTTViewer -device nrf5340_xxaa

# Serial telemetry
python3 -c "
import serial
ser = serial.Serial('/dev/ttyUSB0', 115200)
while True: print(ser.readline().decode())
"

# BLE scanning
python3 /Users/bob/.hardware-bundles/nrf5340/ble_gateway.py
```

---

## GF(3) Integration

**Trit Assignment**: nRF5340 = **0 (ERGODIC)**

**Role**: Hardware coordinator

**Relationship**:
```
BCI Bundle (+1) ⊗ nRF5340 (0) ⊗ Control System (-1) ≡ 0 (mod 3)
```

When Control System is added: GF(3) balance = 0 ✅

---

## References

- [Nordic nRF5340 Product Page](https://www.nordicsemi.com/Products/nRF5340)
- [nRF Connect SDK Docs](https://docs.nordicsemi.com/bundle/ncs-latest/)
- [Zephyr nRF5340 Board](https://docs.zephyrproject.org/latest/boards/nordic/nrf5340dk/)
- [J-Link User Manual](https://www.segger.com/downloads/jlink/UM08001_JLink.pdf)
- [SEGGER RTT Documentation](https://kb.segger.com/J-Link_-_RTT)

---

**Status**: ✅ Production Ready
**Architecture**: Dual Cortex-M33 + BLE 5.4 + Thread + Zigbee
**Python Support**: Serial, BLE (bleak), MQTT, async I/O
**Skill Type**: Hardware Abstraction Layer
**Trit**: 0 (ERGODIC)
