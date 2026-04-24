---
name: nrf5340-device-interaction
description: "Interact with nRF5340 devices over BLE, USB serial, and J-Link. Covers DFU firmware updates via mcumgr, BLE GATT service exploration, nRF Connect SDK CLI tools, RTT logging, and Zephyr shell commands. Use when flashing firmware, debugging BLE connections, reading sensor data, or managing nRF5340-based BCI receivers."
trit: +1
---

# nRF5340 Device Interaction

Talk to nRF5340 devices. Flash, debug, stream, monitor.

## Connection Methods

| Method | Tool | Speed | Use Case |
|--------|------|-------|----------|
| J-Link SWD | nrfjprog / west flash | Fast | Development, full flash |
| USB Serial | screen / minicom | 115200 | Zephyr shell, logs |
| BLE | nRF Connect app / bluetoothctl | Wireless | Production DFU, GATT |
| RTT | J-Link RTT Viewer | Real-time | Debug logging (no UART needed) |

## Flash Firmware

```bash
# Via west (preferred)
west flash --erase

# Via nrfjprog (J-Link)
nrfjprog --program app.hex --chiperase --verify
nrfjprog --reset

# Flash network core separately
nrfjprog --program net_core.hex --coprocessor CP_NETWORK --chiperase
nrfjprog --reset

# Recover bricked device
nrfjprog --recover
nrfjprog --recover --coprocessor CP_NETWORK
```

## DFU Over BLE (mcumgr)

```bash
# List images on device
mcumgr --conntype ble --connstring peer_name=BCI_RX image list

# Upload new firmware
mcumgr --conntype ble --connstring peer_name=BCI_RX image upload app_update.bin

# Confirm and reset
mcumgr --conntype ble --connstring peer_name=BCI_RX image confirm
mcumgr --conntype ble --connstring peer_name=BCI_RX reset
```

## DFU Over USB

```bash
# Create DFU package
nrfutil pkg generate --hw-version 52 --sd-req 0x00 \
  --application app.hex --application-version 1 dfu_pkg.zip

# Flash via USB serial
nrfutil dfu serial -pkg dfu_pkg.zip -p /dev/cu.usbmodem* -b 115200
```

## BLE GATT Exploration

```bash
# Scan for nRF5340 devices
bluetoothctl
> scan on
# Look for "BCI_RX" or "nRF5340"
> scan off
> connect AA:BB:CC:DD:EE:FF

# List services
gatttool -b AA:BB:CC:DD:EE:FF --primary

# Nordic UART Service (NUS) — common for BCI data streaming
# Service UUID: 6e400001-b5a3-f393-e0a9-e50e24dcca9e
# TX Char:      6e400003-b5a3-f393-e0a9-e50e24dcca9e (notify)
# RX Char:      6e400002-b5a3-f393-e0a9-e50e24dcca9e (write)

# Subscribe to notifications (BCI data stream)
gatttool -b AA:BB:CC:DD:EE:FF --char-write-req -a 0x0012 -n 0100 --listen
```

## Zephyr Shell (USB Serial)

```bash
# Connect to Zephyr shell
screen /dev/cu.usbmodem* 115200

# Useful shell commands
> kernel version
> kernel threads
> kernel stacks
> device list
> sensor get bme280
> flash read 0 0x0 32
> bt scan on
> bt connect AA:BB:CC:DD:EE:FF public
> log enable dbg app
```

## RTT Logging (No UART Pins Needed)

```bash
# Start J-Link RTT server
JLinkRTTViewerExe

# Or via command line
JLinkExe -device nRF5340_xxAA_APP -if SWD -speed 4000
> connect
> r
# RTT output appears automatically

# In Zephyr, enable RTT backend:
# CONFIG_USE_SEGGER_RTT=y
# CONFIG_LOG_BACKEND_RTT=y
# CONFIG_SHELL_BACKEND_RTT=y
```

## BCI Data Streaming Protocol

The zig-syrup-bci receiver uses NUS (Nordic UART Service) to stream:

```
Packet: [0xBC] [modality] [channel_count] [sample_count] [data...] [crc8]

Modality bytes:
  0x01 = EEG (from Cyton dongle relay)
  0x02 = fNIRS (from OpenNIRScap ADC)
  0x03 = Eye tracking (from Tobii/Pupil)
  0x04 = IMU (from onboard LSM6DSO)
  0x05 = Pose (from MediaPipe relay)

GF(3) trit per packet:
  EEG=0, fNIRS=+1, Eye=-1, IMU=0, Pose=0
```

## Power Profiling

```bash
# nRF Power Profiler Kit II
nrfutil toolchain-manager launch --ncs-version v2.6.0 -- \
  nrfutil ppk2 measure --period 10 --average

# Expected current draw:
# BLE advertising: ~1.5 mA
# BLE connected, streaming NUS: ~3.5 mA
# BLE + SPI ADC polling: ~5 mA
# System OFF: ~0.4 µA
```

## Troubleshooting

| Symptom | Cause | Fix |
|---------|-------|-----|
| nrfjprog: no debugger | J-Link not connected | Check USB, install J-Link drivers |
| BLE not advertising | Network core not flashed | Flash net core: `west flash --domain cpunet` |
| GATT empty | Services not registered | Check `bt_gatt_service_register()` in firmware |
| DFU fails "no slot" | MCUboot not configured | Build with `-DCONFIG_BOOTLOADER_MCUBOOT=y` |
| RTT no output | Wrong device selected | Use `nRF5340_xxAA_APP` not `nRF5340_xxAA_NET` |
| NUS no data | Notifications not enabled | Write `0100` to CCCD handle |
| High current in sleep | UART/SPI left active | Disable peripherals before sleep |

## Related Skills

| Skill | Connection |
|-------|-----------|
| nrf5340-hardware | Pin assignments, power domains, peripherals |
| cyton-dongle | 2.4GHz EEG data source relayed through nRF5340 |
| zig-syrup-bci | Firmware consuming this device's BLE stream |
| opennirscap-build | fNIRS sensor board connected via SPI to nRF5340 |
