#!/usr/bin/env python3
"""
nRF5340 Device Interaction Library

Combines hardware abstraction (nrf5340-hardware skill) with low-level
blackhat patterns (SWD debugging, memory probing, firmware analysis).

Status: Production-ready for authorized testing
Authorization: Written engagement required for security testing
"""

import subprocess
import struct
import time
import sys
import re
import json
from pathlib import Path
from typing import Optional, Dict, List, Tuple
from enum import IntEnum
from dataclasses import dataclass, field
from datetime import datetime


# ============================================================================
# DEVICE DETECTION
# ============================================================================

class nRF5340Detector:
    """Auto-detect nRF5340 DK via multiple methods"""

    def __init__(self):
        self.device_found = False
        self.serial_number = None
        self.usb_port = None
        self.rtc_available = False
        self.detection_log = []

    def detect_via_nrfjprog(self) -> Optional[str]:
        """Find via nrfjprog -i (most reliable)"""
        try:
            output = subprocess.check_output(
                ["nrfjprog", "-i"],
                text=True,
                timeout=5,
                stderr=subprocess.DEVNULL
            )
            serials = re.findall(r'^(\d+)', output, re.MULTILINE)
            if serials:
                return serials[0]
        except (FileNotFoundError, subprocess.TimeoutExpired, subprocess.CalledProcessError):
            pass
        return None

    def detect_via_system_profiler(self) -> Optional[str]:
        """Find via system_profiler (macOS)"""
        try:
            output = subprocess.check_output(
                ["system_profiler", "SPUSBDataType"],
                text=True,
                timeout=5
            )
            if "SEGGER" in output or "J-Link" in output:
                serials = re.findall(r'Serial Number: (\d+)', output)
                if serials:
                    return serials[0]
        except (FileNotFoundError, subprocess.TimeoutExpired):
            pass
        return None

    def detect_uart_port(self) -> Optional[str]:
        """Find UART-to-USB bridge"""
        try:
            import serial.tools.list_ports
            for port in serial.tools.list_ports.comports():
                if any(x in port.description for x in ['SEGGER', 'J-Link', 'USB']):
                    return port.device
        except ImportError:
            pass
        return None

    def auto_detect(self) -> bool:
        """Try all detection methods"""
        methods = [
            ("nrfjprog", self.detect_via_nrfjprog),
            ("system_profiler", self.detect_via_system_profiler),
            ("UART port", self.detect_uart_port),
        ]

        print("[*] nRF5340 Device Detection")
        print("=" * 70)

        for method_name, method_func in methods:
            try:
                result = method_func()
                status = "✓ FOUND" if result else "✗ NOT FOUND"
                print(f"  {method_name:20} {status}")
                if result:
                    print(f"    → {result}")
                    if method_name == "nrfjprog":
                        self.serial_number = result
                    elif method_name == "UART port":
                        self.usb_port = result
                self.detection_log.append((method_name, result))
            except Exception as e:
                print(f"  {method_name:20} ERROR: {str(e)[:50]}")

        self.device_found = bool(self.serial_number or self.usb_port)

        print()
        if self.device_found:
            print("[✓] nRF5340 DK CONNECTED and READY")
            return True
        else:
            print("[✗] nRF5340 DK NOT DETECTED")
            print("    Ensure device is connected via USB")
            print("    Install nrf-tools: brew install nrf-tools")
            return False


# ============================================================================
# HID INPUT DEVICE DETECTION
# ============================================================================

# Nordic Semiconductor VendorID
NORDIC_VID = 0x1915
# SEGGER J-Link VendorID
SEGGER_VID = 0x1366

# nRF5340 DK GPIO (PCA10095)
GPIO_P0_BASE = 0x50842500
GPIO_P1_BASE = 0x50842800
GPIO_OUT_OFFSET = 0x504
GPIO_IN_OFFSET = 0x510
GPIO_DIR_OFFSET = 0x514
GPIO_PIN_CNF_BASE = 0x700  # + pin*4

# LED pins (active low on DK)
LED_PINS = {
    "LED1": 28,  # P0.28
    "LED2": 29,  # P0.29
    "LED3": 30,  # P0.30
    "LED4": 31,  # P0.31
}

# Button pins (active low, internal pull-up)
BUTTON_PINS = {
    "Button1": 23,  # P0.23
    "Button2": 24,  # P0.24
    "Button3": 8,   # P0.08
    "Button4": 9,   # P0.09
}


@dataclass
class HIDDeviceInfo:
    """Describes a detected HID device"""
    vendor_id: int = 0
    product_id: int = 0
    name: str = ""
    serial: str = ""
    path: str = ""
    transport: str = ""  # "usb" or "ble"
    is_nordic: bool = False
    hid_usage: str = ""  # "keyboard", "mouse", "gamepad", "custom"
    manufacturer: str = ""


class HIDDeviceEnumerator:
    """Enumerate nRF5340 as HID input device via USB and BLE"""

    def __init__(self):
        self.devices: List[HIDDeviceInfo] = []

    def scan_usb_hid(self) -> List[HIDDeviceInfo]:
        """Scan USB HID devices via system_profiler + ioreg"""
        found = []

        # Method 1: system_profiler for USB devices
        try:
            output = subprocess.check_output(
                ["system_profiler", "SPUSBDataType", "-json"],
                text=True, timeout=10
            )
            usb_data = json.loads(output)
            self._walk_usb_tree(usb_data, found)
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired,
                json.JSONDecodeError, FileNotFoundError):
            pass

        # Method 2: ioreg for HID devices (catches BLE HID too)
        try:
            output = subprocess.check_output(
                ["ioreg", "-r", "-c", "IOHIDDevice", "-a"],
                text=True, timeout=10
            )
            # plistlib parse
            import plistlib
            devices = plistlib.loads(output.encode())
            if isinstance(devices, list):
                for dev in devices:
                    info = self._parse_ioreg_hid(dev)
                    if info:
                        found.append(info)
            elif isinstance(devices, dict):
                info = self._parse_ioreg_hid(devices)
                if info:
                    found.append(info)
        except (subprocess.CalledProcessError, subprocess.TimeoutExpired,
                FileNotFoundError, Exception):
            pass

        self.devices = found
        return found

    def scan_ble_hid(self) -> List[HIDDeviceInfo]:
        """Scan for BLE HID devices (nRF5340 with HID-over-GATT)"""
        found = []
        try:
            import asyncio

            async def _scan():
                from bleak import BleakScanner
                devices = await BleakScanner.discover(timeout=5.0)
                for d in devices:
                    # Check for HID service UUID (0x1812)
                    uuids = [str(u).lower() for u in (d.metadata.get("uuids", []))]
                    has_hid = any("1812" in u for u in uuids)
                    is_nordic = (d.name and "nRF" in d.name) or has_hid
                    if is_nordic or has_hid:
                        info = HIDDeviceInfo(
                            name=d.name or "Unknown BLE HID",
                            path=d.address,
                            transport="ble",
                            is_nordic=is_nordic,
                            hid_usage="keyboard" if has_hid else "custom",
                        )
                        found.append(info)
                return found

            loop = asyncio.new_event_loop()
            found = loop.run_until_complete(_scan())
            loop.close()
        except ImportError:
            pass  # bleak not installed
        except Exception:
            pass

        self.devices.extend(found)
        return found

    def _walk_usb_tree(self, data, found: list, depth=0):
        """Recursively walk system_profiler USB JSON"""
        if isinstance(data, dict):
            for key, val in data.items():
                if isinstance(val, list):
                    for item in val:
                        self._walk_usb_tree(item, found, depth + 1)
                elif isinstance(val, dict):
                    # Check if this node is a USB device
                    vid_str = val.get("vendor_id", "")
                    if vid_str:
                        try:
                            vid = int(vid_str.replace("0x", ""), 16) if isinstance(vid_str, str) else int(vid_str)
                        except (ValueError, TypeError):
                            vid = 0
                        pid_str = val.get("product_id", "")
                        try:
                            pid = int(pid_str.replace("0x", ""), 16) if isinstance(pid_str, str) else int(pid_str)
                        except (ValueError, TypeError):
                            pid = 0

                        is_nordic = vid in (NORDIC_VID, SEGGER_VID)
                        name = val.get("_name", key)
                        serial = val.get("serial_num", "")
                        manufacturer = val.get("manufacturer", "")

                        if is_nordic or "Nordic" in str(manufacturer) or "SEGGER" in str(name):
                            info = HIDDeviceInfo(
                                vendor_id=vid,
                                product_id=pid,
                                name=str(name),
                                serial=str(serial),
                                transport="usb",
                                is_nordic=True,
                                manufacturer=str(manufacturer),
                            )
                            found.append(info)

                    # Recurse into sub-items
                    self._walk_usb_tree(val, found, depth + 1)
        elif isinstance(data, list):
            for item in data:
                self._walk_usb_tree(item, found, depth + 1)

    def _parse_ioreg_hid(self, dev: dict) -> Optional[HIDDeviceInfo]:
        """Parse an IOHIDDevice entry from ioreg"""
        vid = dev.get("VendorID", 0)
        pid = dev.get("ProductID", 0)
        name = dev.get("Product", dev.get("IORegistryEntryName", ""))
        manufacturer = dev.get("Manufacturer", "")
        transport = dev.get("Transport", "").lower()
        serial = dev.get("SerialNumber", "")

        is_nordic = vid in (NORDIC_VID, SEGGER_VID) or \
                    "Nordic" in str(manufacturer) or \
                    "nRF" in str(name)

        if not is_nordic:
            return None

        # Determine HID usage
        usage_page = dev.get("PrimaryUsagePage", 0)
        usage = dev.get("PrimaryUsage", 0)
        hid_usage = "custom"
        if usage_page == 1:  # Generic Desktop
            if usage == 6:
                hid_usage = "keyboard"
            elif usage == 2:
                hid_usage = "mouse"
            elif usage == 5:
                hid_usage = "gamepad"
        elif usage_page == 0xFF00:  # Vendor-specific
            hid_usage = "custom"

        return HIDDeviceInfo(
            vendor_id=vid,
            product_id=pid,
            name=str(name),
            serial=str(serial),
            path=dev.get("IORegistryEntryID", ""),
            transport=transport if transport else "usb",
            is_nordic=True,
            hid_usage=hid_usage,
            manufacturer=str(manufacturer),
        )

    def print_report(self):
        """Print detected HID devices"""
        print("\n[*] HID Input Device Scan")
        print("=" * 70)

        if not self.devices:
            print("  No Nordic/nRF5340 HID devices found")
            print("  Ensure device is connected and flashed with HID firmware")
            print(f"  Looking for VendorIDs: Nordic={hex(NORDIC_VID)}, SEGGER={hex(SEGGER_VID)}")
            return

        for i, dev in enumerate(self.devices):
            print(f"\n  Device {i+1}:")
            print(f"    Name:         {dev.name}")
            print(f"    VID:PID:      {hex(dev.vendor_id)}:{hex(dev.product_id)}")
            print(f"    Transport:    {dev.transport}")
            print(f"    HID Usage:    {dev.hid_usage}")
            print(f"    Manufacturer: {dev.manufacturer}")
            print(f"    Serial:       {dev.serial}")
            if dev.path:
                print(f"    Path:         {dev.path}")


# ============================================================================
# LED CONTROL (via SWD GPIO or HID reports)
# ============================================================================

class LEDController:
    """Control nRF5340 DK LEDs via SWD memory-mapped GPIO"""

    def __init__(self, probe: 'SWDMemoryProbe' = None):
        self.probe = probe
        self.led_state = {name: False for name in LED_PINS}

    def _configure_led_pin(self, pin: int):
        """Configure a GPIO pin as output (for LED)"""
        if not self.probe:
            return
        # PIN_CNF[pin]: direction=output(1), input disconnect, no pull, standard drive
        cnf_addr = GPIO_P0_BASE + GPIO_PIN_CNF_BASE + pin * 4
        # Bits: DIR=1 (output), INPUT=1 (disconnect), PULL=0 (none), DRIVE=0 (S0S1)
        cnf_value = 0x00000003  # DIR=Output, INPUT=Disconnected
        self.probe.write_memory(cnf_addr, struct.pack('<I', cnf_value))

    def _configure_button_pin(self, pin: int):
        """Configure a GPIO pin as input with pull-up (for button)"""
        if not self.probe:
            return
        cnf_addr = GPIO_P0_BASE + GPIO_PIN_CNF_BASE + pin * 4
        # DIR=0 (input), INPUT=0 (connected), PULL=3 (pull-up)
        cnf_value = 0x0000000C  # INPUT=Connected, PULL=Pullup
        self.probe.write_memory(cnf_addr, struct.pack('<I', cnf_value))

    def init_leds(self):
        """Initialize all LED pins as outputs"""
        if not self.probe:
            print("[!] No SWD probe connected, cannot control LEDs")
            return False

        print("[*] Initializing LED GPIO pins...")
        for name, pin in LED_PINS.items():
            self._configure_led_pin(pin)
            print(f"  {name} (P0.{pin}): configured as output")

        # Turn all LEDs off (active low: set high = off)
        self.all_off()
        return True

    def init_buttons(self):
        """Initialize all button pins as inputs"""
        if not self.probe:
            return False

        print("[*] Initializing Button GPIO pins...")
        for name, pin in BUTTON_PINS.items():
            self._configure_button_pin(pin)
            print(f"  {name} (P0.{pin}): configured as input with pull-up")
        return True

    def set_led(self, led_name: str, on: bool):
        """Set a single LED on/off (active low: clear bit = on)"""
        if not self.probe:
            return
        if led_name not in LED_PINS:
            print(f"[!] Unknown LED: {led_name}. Available: {list(LED_PINS.keys())}")
            return

        pin = LED_PINS[led_name]
        # Read current OUT register
        out_addr = GPIO_P0_BASE + GPIO_OUT_OFFSET
        data = self.probe.read_memory(out_addr, 4)
        current = struct.unpack('<I', data)[0]

        if on:
            # Active low: clear the bit to turn ON
            current &= ~(1 << pin)
        else:
            # Active low: set the bit to turn OFF
            current |= (1 << pin)

        self.probe.write_memory(out_addr, struct.pack('<I', current))
        self.led_state[led_name] = on

    def all_on(self):
        """Turn all LEDs on"""
        for name in LED_PINS:
            self.set_led(name, True)

    def all_off(self):
        """Turn all LEDs off"""
        for name in LED_PINS:
            self.set_led(name, False)

    def set_pattern(self, pattern: int):
        """Set LED pattern from 4-bit value (0x0-0xF)"""
        for i, name in enumerate(LED_PINS):
            self.set_led(name, bool(pattern & (1 << i)))

    def read_buttons(self) -> Dict[str, bool]:
        """Read all button states (active low: pressed = 0)"""
        if not self.probe:
            return {}

        in_addr = GPIO_P0_BASE + GPIO_IN_OFFSET
        data = self.probe.read_memory(in_addr, 4)
        gpio_in = struct.unpack('<I', data)[0]

        states = {}
        for name, pin in BUTTON_PINS.items():
            # Active low: bit=0 means pressed
            states[name] = not bool(gpio_in & (1 << pin))
        return states

    def blink_sequence(self, count: int = 3, interval: float = 0.25):
        """Blink all LEDs in sequence"""
        for _ in range(count):
            for i, name in enumerate(LED_PINS):
                self.all_off()
                self.set_led(name, True)
                time.sleep(interval)
        self.all_off()

    def print_status(self):
        """Print current LED and button states"""
        print("\n[*] GPIO Status")
        print("-" * 40)

        print("  LEDs:")
        for name, on in self.led_state.items():
            pin = LED_PINS[name]
            status = "ON " if on else "OFF"
            print(f"    {name} (P0.{pin:2d}): {status}")

        if self.probe:
            buttons = self.read_buttons()
            if buttons:
                print("  Buttons:")
                for name, pressed in buttons.items():
                    pin = BUTTON_PINS[name]
                    status = "PRESSED" if pressed else "released"
                    print(f"    {name} (P0.{pin:2d}): {status}")


# ============================================================================
# INPUT DEVICE MONITOR (poll-based)
# ============================================================================

class InputDeviceMonitor:
    """Monitor nRF5340 as input device (buttons + BLE HID events)"""

    def __init__(self, led_ctrl: LEDController = None):
        self.led_ctrl = led_ctrl
        self.running = False
        self.event_log: List[Dict] = []

    def poll_buttons(self, duration: float = 10.0, poll_hz: float = 20.0):
        """Poll buttons and react with LEDs"""
        if not self.led_ctrl or not self.led_ctrl.probe:
            print("[!] No SWD probe for button polling")
            return

        print(f"\n[*] Polling buttons for {duration}s at {poll_hz}Hz")
        print("    Press buttons on the DK to trigger LED feedback")
        print("-" * 40)

        self.running = True
        prev_buttons = {}
        start = time.time()

        while self.running and (time.time() - start) < duration:
            buttons = self.led_ctrl.read_buttons()

            for name, pressed in buttons.items():
                was_pressed = prev_buttons.get(name, False)
                if pressed and not was_pressed:
                    # Button press event
                    event = {
                        "type": "button_press",
                        "button": name,
                        "timestamp": datetime.now().isoformat(),
                    }
                    self.event_log.append(event)
                    print(f"  [{event['timestamp'][-12:]}] {name} PRESSED")

                    # Mirror: light corresponding LED
                    idx = list(BUTTON_PINS.keys()).index(name)
                    led_name = list(LED_PINS.keys())[idx] if idx < len(LED_PINS) else None
                    if led_name:
                        self.led_ctrl.set_led(led_name, True)

                elif not pressed and was_pressed:
                    event = {
                        "type": "button_release",
                        "button": name,
                        "timestamp": datetime.now().isoformat(),
                    }
                    self.event_log.append(event)
                    print(f"  [{event['timestamp'][-12:]}] {name} released")

                    idx = list(BUTTON_PINS.keys()).index(name)
                    led_name = list(LED_PINS.keys())[idx] if idx < len(LED_PINS) else None
                    if led_name:
                        self.led_ctrl.set_led(led_name, False)

            prev_buttons = buttons
            time.sleep(1.0 / poll_hz)

        self.running = False
        self.led_ctrl.all_off()
        print(f"\n  Total events: {len(self.event_log)}")

    def stop(self):
        self.running = False


# ============================================================================
# SWD MEMORY PROBING
# ============================================================================

class SWDMemoryProbe:
    """Low-level memory access via Serial Wire Debug"""

    def __init__(self, device_serial: str = None):
        self.serial = device_serial
        self._probe_log = []

    def _nrfjprog(self, *args) -> str:
        """Execute nrfjprog command"""
        cmd = ["nrfjprog", "-f", "NRF53"]
        if self.serial:
            cmd.extend(["-s", self.serial])
        cmd.extend(args)

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=10
            )

            if result.returncode != 0:
                raise RuntimeError(f"nrfjprog failed: {result.stderr}")

            return result.stdout
        except subprocess.TimeoutExpired:
            raise RuntimeError("nrfjprog timeout")

    def read_memory(self, address: int, size: int) -> bytes:
        """Read memory bytes at address"""
        output = self._nrfjprog("--memrd", hex(address), "--w", str(size))

        # Parse hex output
        hex_values = []
        for line in output.split('\n'):
            if ':' in line:
                hex_part = line.split(':')[1].strip()
                hex_values.extend(hex_part.split())

        data = bytes([int(h, 16) for h in hex_values[:size]])
        self._probe_log.append(f"READ @{hex(address)}: {data.hex()}")
        return data

    def write_memory(self, address: int, data: bytes) -> None:
        """Write memory bytes at address"""
        for i, byte_val in enumerate(data):
            offset = address + i
            self._nrfjprog("--memwr", hex(offset), "--val", hex(byte_val))
        self._probe_log.append(f"WRITE @{hex(address)}: {data.hex()}")

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

    def get_log(self) -> List[str]:
        """Return probe activity log"""
        return self._probe_log.copy()


# ============================================================================
# RTT CONSOLE
# ============================================================================

class RTTClient:
    """Real-Time Transfer console communication"""

    def __init__(self, device_serial: str = None):
        self.serial = device_serial
        self.process = None
        self.connected = False

    def start(self):
        """Start RTT client"""
        try:
            cmd = ["JLinkRTTClient"]
            self.process = subprocess.Popen(
                cmd,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                bufsize=1
            )
            time.sleep(0.5)  # Wait for connection
            self.connected = True
        except FileNotFoundError:
            print("[!] JLinkRTTClient not found. Install J-Link tools.")
            return False
        return True

    def send_command(self, cmd: str) -> None:
        """Send command to device"""
        if not self.process:
            return
        try:
            self.process.stdin.write(cmd + "\n")
            self.process.stdin.flush()
        except BrokenPipeError:
            self.connected = False

    def read_output(self, timeout: float = 1.0) -> str:
        """Read telemetry from device"""
        if not self.process:
            return ""

        try:
            import select
            ready, _, _ = select.select(
                [self.process.stdout],
                [],
                [],
                timeout
            )
            if ready:
                return self.process.stdout.readline()
        except:
            pass

        return ""

    def stop(self):
        """Stop RTT client"""
        if self.process:
            try:
                self.process.terminate()
                self.process.wait(timeout=2)
            except:
                self.process.kill()
            self.connected = False


# ============================================================================
# DEBUG PORT ANALYSIS
# ============================================================================

class DebugPortStatus(IntEnum):
    """UICR Debug Control status"""
    ENABLED = 0x00FFFFFF      # Full debug enabled (security risk!)
    CPUNIDEN_DISABLED = 0xFFFF0000  # Non-invasive debug locked
    DISABLED = 0xFFFFFFFF      # Fully locked


class DebugPortAnalysis:
    """Analyze and control debug port access"""

    UICR_BASE = 0xFF8000
    DEBUGCTRL_OFFSET = 0xFF84

    @staticmethod
    def check_debug_enabled(probe: SWDMemoryProbe) -> Dict:
        """Check debug port lock status"""
        ctrl = probe.read_register(DebugPortAnalysis.UICR_BASE, DebugPortAnalysis.DEBUGCTRL_OFFSET)

        return {
            "raw_value": hex(ctrl),
            "cpuniden": (ctrl >> 16) & 0xFFFF,
            "dbgporten": ctrl & 0xFFFF,
            "full_debug_enabled": (ctrl & 0xFFFF) == 0,
            "risk_level": "🔴 CRITICAL" if (ctrl & 0xFFFF) == 0 else "🟢 SAFE",
        }

    @staticmethod
    def disable_debug(probe: SWDMemoryProbe) -> None:
        """LOCK debug port (IRREVERSIBLE!)"""
        print("[!] WARNING: This operation is IRREVERSIBLE")
        print("[!] Once locked, debug port cannot be re-enabled without bootloader reset")

        response = input("Type 'LOCK_DEBUG' to confirm: ")
        if response != "LOCK_DEBUG":
            print("Cancelled.")
            return

        probe.write_register(
            DebugPortAnalysis.UICR_BASE,
            DebugPortAnalysis.DEBUGCTRL_OFFSET,
            DebugPortStatus.DISABLED
        )
        print("[✓] Debug port LOCKED")


# ============================================================================
# BLE RADIO ANALYSIS
# ============================================================================

class BLERadioAnalyzer:
    """Low-level radio state inspection"""

    RADIO_BASE = 0x41008000

    # Registers
    REG_STATE = 0x550
    REG_FREQUENCY = 0x508
    REG_TXPOWER = 0x50C
    REG_CRCCNF = 0x534

    # Radio states
    STATES = {
        0: "DISABLED",
        1: "RXRU",
        2: "TXRU",
        3: "RX",
        4: "TX",
    }

    @staticmethod
    def read_radio_state(probe: SWDMemoryProbe) -> Dict:
        """Read current radio state"""
        state_reg = probe.read_register(BLERadioAnalyzer.RADIO_BASE, BLERadioAnalyzer.REG_STATE)
        state_val = state_reg & 0xF

        frequency = probe.read_register(BLERadioAnalyzer.RADIO_BASE, BLERadioAnalyzer.REG_FREQUENCY)
        txpower = probe.read_register(BLERadioAnalyzer.RADIO_BASE, BLERadioAnalyzer.REG_TXPOWER)
        crccnf = probe.read_register(BLERadioAnalyzer.RADIO_BASE, BLERadioAnalyzer.REG_CRCCNF)

        return {
            "state": BLERadioAnalyzer.STATES.get(state_val, f"UNKNOWN_{state_val}"),
            "frequency_mhz": 2400 + (frequency % 100),
            "tx_power_dbm": txpower,
            "crc_enabled": bool(crccnf & 0x1),
        }


# ============================================================================
# GF(3) DEVICE STATE
# ============================================================================

class DeviceTrit(IntEnum):
    """GF(3) trit for device security state"""
    VALIDATOR = -1      # Secure, locked
    ERGODIC = 0         # Normal operation
    GENERATOR = 1       # Developer/unlocked


class nRF5340StateController:
    """Maintain GF(3) conservation during state transitions"""

    def __init__(self):
        self.state = DeviceTrit.ERGODIC
        self.trit_sum = 0
        self.transitions = []

    def probe_state(self, probe: SWDMemoryProbe) -> DeviceTrit:
        """Probe actual hardware state"""
        debug_status = DebugPortAnalysis.check_debug_enabled(probe)

        if debug_status["full_debug_enabled"]:
            state = DeviceTrit.GENERATOR
        elif debug_status["risk_level"].startswith("🟢"):
            state = DeviceTrit.VALIDATOR
        else:
            state = DeviceTrit.ERGODIC

        self.state = state
        return state

    def transition(self, new_trit: DeviceTrit, reason: str = "") -> bool:
        """Attempt state transition with GF(3) conservation"""

        if not self._is_valid_transition(self.state, new_trit):
            print(f"[!] Invalid transition: {self.state.name} → {new_trit.name}")
            return False

        # Check GF(3) conservation
        new_sum = (self.trit_sum - self.state + new_trit) % 3
        if new_sum != 0:
            print(f"[!] GF(3) imbalance after transition: {new_sum}")
            return False

        self.state = new_trit
        self.trit_sum = new_sum

        self.transitions.append({
            "from": self.state.name,
            "to": new_trit.name,
            "reason": reason,
            "timestamp": datetime.now().isoformat()
        })

        print(f"[✓] {self.state.name} → {new_trit.name}, GF(3) balance: {new_sum}")
        return True

    def _is_valid_transition(self, from_trit: DeviceTrit, to_trit: DeviceTrit) -> bool:
        """Check hardware state machine constraints"""
        valid_transitions = {
            DeviceTrit.VALIDATOR: [DeviceTrit.ERGODIC],
            DeviceTrit.ERGODIC: [DeviceTrit.VALIDATOR, DeviceTrit.GENERATOR],
            DeviceTrit.GENERATOR: [DeviceTrit.ERGODIC],
        }
        return to_trit in valid_transitions.get(from_trit, [])


# ============================================================================
# FIRMWARE MANAGEMENT
# ============================================================================

class FirmwareManager:
    """Build, flash, and verify firmware"""

    def __init__(self, sdk_path: str = None):
        self.sdk_path = Path(sdk_path) if sdk_path else Path.home() / "nrf-connect-sdk"
        self.build_dir = None

    def build(self, app_path: str = "nrf/applications/blinky") -> bool:
        """Build firmware via west"""
        try:
            app_dir = self.sdk_path / app_path
            if not app_dir.exists():
                print(f"[!] App path not found: {app_dir}")
                return False

            result = subprocess.run(
                ["west", "build", "-b", "nrf5340dk_nrf5340_cpuapp", "-q"],
                cwd=str(app_dir),
                capture_output=True,
                timeout=300
            )

            if result.returncode == 0:
                self.build_dir = app_dir / "build"
                print(f"[✓] Firmware built: {self.build_dir}")
                return True
            else:
                print(f"[!] Build failed: {result.stderr.decode()}")
                return False

        except Exception as e:
            print(f"[!] Build error: {e}")
            return False

    def flash(self) -> bool:
        """Flash firmware via J-Link"""
        if not self.build_dir:
            print("[!] No build directory set. Run build() first.")
            return False

        try:
            result = subprocess.run(
                ["west", "flash", "-q"],
                cwd=str(self.build_dir.parent),
                capture_output=True,
                timeout=60
            )

            if result.returncode == 0:
                print("[✓] Firmware flashed successfully")
                return True
            else:
                print(f"[!] Flash failed: {result.stderr.decode()}")
                return False

        except Exception as e:
            print(f"[!] Flash error: {e}")
            return False

    def verify(self) -> bool:
        """Verify flashed firmware"""
        if not self.build_dir:
            return False

        try:
            hex_file = self.build_dir / "zephyr" / "zephyr.hex"
            if not hex_file.exists():
                return False

            # Read back from device
            subprocess.run(
                ["nrfjprog", "--readcode", "readback.hex", "-f", "NRF53"],
                capture_output=True,
                timeout=30
            )

            # Compare checksums
            import hashlib

            with open(hex_file, 'rb') as f:
                original_hash = hashlib.sha256(f.read()).hexdigest()

            with open("readback.hex", 'rb') as f:
                readback_hash = hashlib.sha256(f.read()).hexdigest()

            match = original_hash == readback_hash
            status = "✓" if match else "✗"
            print(f"[{status}] Firmware verification: {'PASSED' if match else 'FAILED'}")

            return match

        except Exception as e:
            print(f"[!] Verification error: {e}")
            return False


# ============================================================================
# MAIN DEMO
# ============================================================================

def main():
    """Interactive device interaction demo"""
    print("\n" + "=" * 70)
    print("nRF5340 Device Interaction Skill")
    print("=" * 70)

    # --- HID Input Device Scan (always runs, no hardware required) ---
    hid_enum = HIDDeviceEnumerator()
    hid_enum.scan_usb_hid()
    hid_enum.scan_ble_hid()
    hid_enum.print_report()

    # --- SWD-based detection ---
    detector = nRF5340Detector()
    if not detector.auto_detect():
        print("\n[!] No SWD-connected device. Skipping probe-based tests.")
        print("    HID scan above shows any Nordic HID devices present.")
        return 1

    print(f"\nSerial: {detector.serial_number}")

    # Create probe
    probe = SWDMemoryProbe(detector.serial_number)

    # --- LED Control ---
    led = LEDController(probe)
    if led.init_leds():
        led.init_buttons()
        print("\n[*] LED Blink Test")
        led.blink_sequence(count=2, interval=0.15)
        led.print_status()

    # Analyze debug port
    print("\n[*] Debug Port Analysis")
    print("-" * 70)
    debug_status = DebugPortAnalysis.check_debug_enabled(probe)
    for key, value in debug_status.items():
        print(f"  {key:25} {value}")

    # Read radio state
    print("\n[*] BLE Radio State")
    print("-" * 70)
    radio = BLERadioAnalyzer.read_radio_state(probe)
    for key, value in radio.items():
        print(f"  {key:25} {value}")

    # GF(3) state check
    print("\n[*] GF(3) Device State")
    print("-" * 70)
    controller = nRF5340StateController()
    current_state = controller.probe_state(probe)
    print(f"  Current trit: {current_state.name}")
    print(f"  GF(3) sum: {controller.trit_sum}")

    # --- Interactive button→LED monitoring ---
    if "--monitor" in sys.argv:
        monitor = InputDeviceMonitor(led)
        try:
            monitor.poll_buttons(duration=30.0)
        except KeyboardInterrupt:
            monitor.stop()
            led.all_off()

    print("\n[+] Device interaction complete")
    return 0


if __name__ == "__main__":
    sys.exit(main())
