---
name: nrf5340-hardware
description: "Nordic nRF5340 dual-core SoC hardware reference: application core (Cortex-M33 128MHz), network core (Cortex-M33 64MHz), 2.4GHz radio (BLE 5.3, Thread, Zigbee, ANT, 802.15.4, proprietary), GPIO/SPI/I2C/UART pinout, power domains, DFU bootloader. Use when designing BCI receiver firmware, configuring radio parameters, or debugging hardware peripherals."
trit: 0
---

# nRF5340 Hardware

Nordic Semiconductor dual-core wireless SoC. The BCI receiver target for zig-syrup-bci.

## Cores

| Core | CPU | Clock | Flash | RAM | Role |
|------|-----|-------|-------|-----|------|
| Application | Cortex-M33 + FPU + DSP | 128 MHz | 1 MB | 512 KB | User logic, DSP, crypto |
| Network | Cortex-M33 | 64 MHz | 256 KB | 64 KB | Radio stack, BLE, Thread |

Cores communicate via IPC (inter-processor communication) with shared RAM regions and hardware mutexes.

## Radio

- **Frequency**: 2400-2483.5 MHz (ISM band)
- **Protocols**: BLE 5.3, Thread 1.3, Zigbee 3.0, ANT, IEEE 802.15.4, proprietary 2.4GHz
- **TX Power**: -20 to +3 dBm (1 dB steps)
- **RX Sensitivity**: -98 dBm (1 Mbps BLE), -104 dBm (125 kbps coded PHY)
- **Data Rates**: 125 kbps, 500 kbps, 1 Mbps, 2 Mbps
- **Direction Finding**: AoA and AoD (antenna switching)

## Key Peripherals

| Peripheral | Count | Notes |
|------------|-------|-------|
| GPIO | 48 pins (P0.0-P0.31, P1.0-P1.15) | 3.3V, 6 mA drive |
| SPI | 4 (SPIM) | Up to 32 MHz, EasyDMA |
| I2C | 4 (TWIM) | Up to 400 kHz |
| UART | 4 (UARTE) | Up to 1 Mbps, EasyDMA, HW flow ctrl |
| ADC | 1 (SAADC) | 12-bit, 8 channels, 200 ksps |
| PWM | 4 | 16 MHz base, 4 channels each |
| PDM | 1 | Digital microphone interface |
| I2S | 1 | Audio codec interface |
| QSPI | 1 | External flash, up to 96 MHz |
| USB | 1 | Full-speed (12 Mbps), device only |
| Crypto | 1 (CryptoCell-312) | AES, SHA, RSA, ECC, TRNG |

## Power Domains

| Domain | Voltage | Peripherals |
|--------|---------|-------------|
| VDD | 1.7-5.5V | Main supply (internal LDO/DCDC to 1.1V) |
| VDDH | 2.5-5.5V | High-voltage GPIO, USB |
| DECN | 1.0-1.3V | Network core internal |
| DECA | 1.0-1.3V | Application core internal |

**Power modes**: Active (6 mA), Idle (1 mA), System ON sleep (1.5 µA), System OFF (0.4 µA)

Use DCDC converter for battery operation — drops from ~6 mA to ~3 mA active current.

## BCI Receiver Pin Assignment (zig-syrup-bci target)

| Pin | Function | Connected To |
|-----|----------|-------------|
| P0.06 | UART TX | Debug console |
| P0.08 | UART RX | Debug console |
| P0.13 | SPI SCK | fNIRS ADC (ADS1299) |
| P0.14 | SPI MOSI | fNIRS ADC |
| P0.15 | SPI MISO | fNIRS ADC |
| P0.16 | SPI CS | fNIRS ADC |
| P0.26 | I2C SDA | IMU (LSM6DSO) |
| P0.27 | I2C SCL | IMU |
| P1.00 | GPIO | LED status |
| P1.01 | GPIO | Button (DFU trigger) |
| P1.09 | ADC AIN5 | Battery voltage divider |

## DFU Bootloader

The nRF5340 uses MCUboot as the default bootloader:

```bash
# Build with MCUboot
west build -b nrf5340dk/nrf5340/cpuapp -- -DCONFIG_BOOTLOADER_MCUBOOT=y

# Flash via J-Link
west flash

# DFU over BLE (using mcumgr)
mcumgr --conntype ble --connstring peer_name=nRF5340_BCI image upload app_update.bin

# DFU over USB (using nrfutil)
nrfutil dfu serial -pkg dfu_package.zip -p /dev/cu.usbmodem*
```

## Zephyr RTOS

```bash
# Setup
west init -m https://github.com/nrfconnect/sdk-nrf
west update

# Build for application core
west build -b nrf5340dk/nrf5340/cpuapp app/

# Build for network core (BLE controller)
west build -b nrf5340dk/nrf5340/cpunet net/

# Flash both cores
west flash --erase
```

### Key Kconfig Options

```
CONFIG_BT=y                    # Enable Bluetooth
CONFIG_BT_PERIPHERAL=y         # Peripheral role
CONFIG_BT_DIS=y                # Device Information Service
CONFIG_BT_NUS=y                # Nordic UART Service
CONFIG_BT_CTLR=y               # BLE controller on network core
CONFIG_IPC_SERVICE=y            # Inter-core communication
CONFIG_HEAP_MEM_POOL_SIZE=8192
CONFIG_SYSTEM_WORKQUEUE_STACK_SIZE=2048
```

## Relevant Datasheets

- nRF5340 Product Specification v1.3: `infocenter.nordicsemi.com/index.jsp?topic=%2Fps_nrf5340`
- nRF5340-DK User Guide: `infocenter.nordicsemi.com/topic/ug_nrf5340_dk`

## Related Skills

| Skill | Connection |
|-------|-----------|
| zig-syrup-bci | BCI receiver firmware target |
| cyton-dongle | 2.4GHz radio comparison (RFDuino vs nRF5340) |
| opennirscap-build | fNIRS sensor connected via SPI |
| nrf5340-device-interaction | Software/firmware interaction patterns |
