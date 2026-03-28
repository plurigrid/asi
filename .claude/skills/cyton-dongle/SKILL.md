---
name: cyton-dongle
description: Connect and stream from OpenBCI Cyton/Daisy via USB dongle, including first-time radio channel pairing
---

# Cyton Dongle

USB wireless receiver (RFD22301/RFDuino) for OpenBCI Cyton 8/16-channel EEG board.

## Hardware

- **Dongle**: FTDI FT231X USB-UART → RFDuino 2.4 GHz radio
- **Serial**: 115200 baud, 8N1
- **Device**: `/dev/cu.usbserial-*` (macOS) or `/dev/ttyUSB*` (Linux)
- **Sample Rate**: 250 Hz
- **Channels**: 8 (Cyton) or 16 (Cyton + Daisy)
- **Packet**: 33 bytes (0xA0 start, 24 bytes channel data, 6 bytes aux, 1 byte counter, 0xC0 stop)

## First-Time Pairing (Critical)

A new dongle and board are typically on **different radio channels**. The standard `0xF0 0x01` channel-set command requires both sides to handshake — it **fails when they're on different channels**.

Use `0xF0 0x02` (CHANNEL_SET_OVERRIDE) to force the dongle to each channel without requiring board response, then check system status:

```python
import serial, time

ser = serial.Serial('/dev/cu.usbserial-XXXXX', 115200, timeout=2)
time.sleep(2)

for chan in range(26):
    ser.reset_input_buffer()
    ser.write(bytes([0xF0, 0x02, chan]))  # override dongle (no handshake)
    time.sleep(0.5)
    ser.read(ser.in_waiting or 512)

    ser.reset_input_buffer()
    ser.write(bytes([0xF0, 0x07]))        # system status query
    time.sleep(0.5)
    resp = ser.read(ser.in_waiting or 512).decode('utf-8', errors='ignore')

    if 'System is Up' in resp:
        print(f'FOUND BOARD ON CHANNEL {chan}')
        break
    else:
        print(f'Ch {chan}: Down')

ser.close()
```

## Radio Commands (0xF0 prefix)

| Bytes | Command | Notes |
|-------|---------|-------|
| `0xF0 0x00` | CHANNEL_GET | Returns current dongle channel |
| `0xF0 0x01 <ch>` | CHANNEL_SET | Coordinated change, **requires board online** |
| `0xF0 0x02 <ch>` | CHANNEL_OVERRIDE | **Dongle-only, no handshake** — use for pairing |
| `0xF0 0x03` | POLL_TIME_GET | Current poll time |
| `0xF0 0x04 <t>` | POLL_TIME_SET | Set poll time |
| `0xF0 0x05` | BAUD_DEFAULT | 115200 |
| `0xF0 0x06` | BAUD_FAST | 230400 |
| `0xF0 0x07` | SYS_STATUS | "System is Up" or "System is Down" |
| `0xF0 0x0A` | BAUD_HYPER | 921600 |

Channels are 0-25. Default for new boards is usually 1.

## Serial Commands

| Cmd | Action |
|-----|--------|
| `v` | Firmware version + board info |
| `b` | Start binary streaming |
| `s` | Stop streaming |
| `C` | Enable Daisy (16ch mode) |
| `D` | Query Daisy module |
| `?` | Print ADS1299 registers |
| `1`-`8` | Default channel settings (ch 1-8) |
| `!`-`*` | Default channel settings (ch 9-16, Daisy) |
| `d` | Reset all channel defaults |

## Parsing Binary Packets

```python
SCALE_UV = 4.5 / (24 * (2**23 - 1)) * 1e6  # ~0.02235 uV/count

def parse_24bit(b0, b1, b2):
    val = (b0 << 16) | (b1 << 8) | b2
    return val - 0x1000000 if val >= 0x800000 else val
```

**33-byte packet**: `0xA0 | sample_num | 8×3-byte channels | 6-byte aux | 0xC0`

With Daisy: odd sample numbers = channels 1-8, even = channels 9-16.

## Streaming and Channel Quality Check

```python
import serial, time, math

ser = serial.Serial('/dev/cu.usbserial-XXXXX', 115200, timeout=5)
time.sleep(2)
ser.reset_input_buffer()

# Override to known channel
ser.write(bytes([0xF0, 0x02, CHANNEL]))
time.sleep(1)
ser.read(ser.in_waiting or 512)

# Reset board
ser.write(b'v')
time.sleep(3)
ser.read(ser.in_waiting or 4096)
ser.reset_input_buffer()

SCALE_UV = 4.5 / (24 * (2**23 - 1)) * 1e6

def p24(b0, b1, b2):
    v = (b0 << 16) | (b1 << 8) | b2
    return v - 0x1000000 if v >= 0x800000 else v

# Start stream
ser.write(b'b')
time.sleep(1.5)
ser.read(ser.in_waiting or 2048)  # drain text

samples = {i: [] for i in range(16)}
t0 = time.time()

while (time.time() - t0) < 4:
    avail = ser.in_waiting
    if not avail:
        time.sleep(0.01)
        continue
    buf = ser.read(avail)
    i = 0
    while i < len(buf) - 32:
        if buf[i] == 0xA0 and buf[i+32] == 0xC0:
            sn = buf[i+1]
            is_daisy = (sn % 2 == 0)
            for ch in range(8):
                off = i + 2 + ch * 3
                raw = p24(buf[off], buf[off+1], buf[off+2])
                samples[ch + (8 if is_daisy else 0)].append(raw * SCALE_UV)
            i += 33
        else:
            i += 1

ser.write(b's')
ser.close()

# Assess quality
for ch in range(16):
    vals = samples[ch]
    if len(vals) < 10:
        print(f'Ch {ch+1}: NO DATA')
        continue
    mean = sum(vals) / len(vals)
    std = math.sqrt(sum((v - mean)**2 for v in vals) / len(vals))
    if abs(mean) > 187000: q = 'RAILED'
    elif std < 1:          q = 'FLAT'
    elif std > 200:        q = 'BAD CONTACT'
    elif std > 100:        q = 'NOISY'
    elif std < 50:         q = 'CLEAN'
    else:                  q = 'OK'
    print(f'Ch {ch+1}: {q} (std={std:.1f} uV)')
```

## Ultracortex Mark IV 16ch Montage (10-20)

| Ch | Position | Ch | Position |
|----|----------|----|----------|
| 1 | Fp1 | 9 | F7 |
| 2 | Fp2 | 10 | F8 |
| 3 | C3 | 11 | F3 |
| 4 | C4 | 12 | F4 |
| 5 | P7 | 13 | T7 |
| 6 | P8 | 14 | T8 |
| 7 | O1 | 15 | P3 |
| 8 | O2 | 16 | P4 |

## Daisy Module (16ch)

The Daisy stacks on top of the Cyton, adding a second ADS1299 for channels 9-16.

**Verifying Daisy**:
- `v` should report: `On Daisy ADS1299 Device ID: 0x3E`
- `D` returns Daisy firmware version (e.g., `060110`)
- `C` enables 16ch mode, returns `16`
- `c` (lowercase) disables Daisy, returns `daisy removed`

**Daisy interleaving**: In 16ch mode, the board alternates packets:
- **Odd sample numbers** (1,3,5...): channels 1-8 (main board)
- **Even sample numbers** (2,4,6...): channels 9-16 (Daisy)

Expect ~1:1 ratio of main:daisy packets. If Daisy packets are missing or all-zero, check that the Daisy board is firmly seated on the Cyton header pins.

## ADS1299 Registers

Query with `?`. Key registers per channel:

| Register | Default | Meaning |
|----------|---------|---------|
| `0x68` | Normal input, gain 24x, powered on |
| `0xE8` | Powered down (bit 7 set) |
| `0x60` | Normal input, gain 24x, SRB2 off |

- `BIAS_SENSP = 0xFF`: All channels feeding bias drive (good)
- `CONFIG1 = 0xB6`: 250 Hz sample rate, daisy mode
- `CONFIG3 = 0xEC`: Internal reference, bias enabled

## Electrode Quality Thresholds

| Std Dev (uV) | Status | Meaning |
|--------------|--------|---------|
| < 1 | FLAT | Shorted to reference or no contact |
| < 50 | CLEAN | Good signal, usable for all analysis |
| 50-100 | OK | Usable for most band power analysis |
| 100-200 | NOISY | May work for gross features (eye blinks) |
| > 200 | BAD CONTACT | Electrode touching but loose |
| mean ±187500 | RAILED | Not touching skin, pinned to ADC rail |

## Session Persistence

The dongle **does not persist** the channel override across serial sessions. Every time you open a new serial connection, you must re-send `0xF0 0x02 <channel>`. Keep the serial port open for the duration of your recording, or store the known channel and re-override on connect.

The board also goes to **sleep after extended idle** with no streaming. Toggle the power switch OFF→PC to wake it, then re-scan.

## Dongle Switch Position

The dongle has a small switch with two positions:

| Position | Mode | Use |
|----------|------|-----|
| **GPIO_6** | Normal operation | **Use this for data streaming** |
| **Reset** | Bootloader/programming | Firmware upload only |

If the switch is on "Reset", commands may partially work (radio config, `v`, `?`) but **binary streaming will fail** — the RFDuino stays in bootloader mode and cannot relay continuous data. This is easy to miss because single-shot commands still get responses.

## Troubleshooting

| Symptom | Cause | Fix |
|---------|-------|-----|
| "Device failed to poll Host" | Channel mismatch | Use `0xF0 0x02` override scan (see above) |
| "System is Down" | Board off or wrong channel | Check power, scan channels |
| Channel stuck on set | `0x01` needs board handshake | Use `0x02` override instead |
| RAILED at ±187500 uV | Electrode not connected | Check pin seating and wire |
| FLAT near 0 | Shorted to ref or no contact | Apply gel, press electrode |
| FLAT at exactly 0.0 | Daisy wires not plugged in | Check header pin connections |
| High noise (>200 uV std) | Poor electrode contact | Tighten cap, add paste |
| 0 packets after `b` | Dongle switch on "Reset" | Set switch to **GPIO_6** position |
| Commands work, stream doesn't | Dongle in bootloader mode | Check switch is GPIO_6, not Reset |
| Daisy ch all zero | Daisy not seated or `C` not sent | Reseat Daisy, send `C` before `b` |
| All channels railed one side | Cap too loose / wrong size | Tighten straps, try gel electrodes |
| Commands work but stream doesn't | Board slept during idle | Toggle OFF→PC, re-pair |

## Firmware Source

- Dongle: `github.com/OpenBCI/OpenBCI_Radios`
- Board: `github.com/OpenBCI/OpenBCI_32bit_Library`
