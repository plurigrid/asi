---
name: gnu-radio
description: GNU Radio SDR toolkit for signal processing flowgraphs with Python blocks
metadata:
  skill_type: SDR / Signal Processing / Python
  interface_ports:
  - Flowgraphs
  - Python Blocks
  - Hardware SDR
trit: -1
color: "#4A90D9"
parents: [muchas-radio, whitehole-audio, gay-mcp]
seed: 3800
---

# GNU Radio SDR Skill

**Status**: Active
**Trit**: -1 (MINUS - signal consumption/analysis)
**Seed**: 3800 (RF frequency reference)
**Color**: #4A90D9 (radio blue)

> *"Flowgraphs are signal poems. Blocks are the words."*

## Overview

GNU Radio is a free, open-source software development toolkit for signal processing. It provides:

- **Flowgraphs**: Visual signal processing chains
- **Blocks**: Modular DSP components (filters, modulators, decoders)
- **Python Integration**: Embedded Python blocks for custom processing
- **Hardware Support**: RTL-SDR, HackRF, USRP, PlutoSDR, and more

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                     GNU RADIO FLOWGRAPH                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│   ┌─────────┐    ┌─────────┐    ┌─────────┐    ┌─────────┐     │
│   │ Source  │───▶│ Filter  │───▶│ Demod   │───▶│  Sink   │     │
│   │ (SDR)   │    │ (LPF)   │    │ (FM)    │    │ (Audio) │     │
│   └─────────┘    └─────────┘    └─────────┘    └─────────┘     │
│       │              │              │              │            │
│       ▼              ▼              ▼              ▼            │
│   [complex]      [complex]      [float]       [float]          │
│   trit: +1       trit: 0        trit: -1      trit: +1         │
│                                                                  │
│   GF(3) Conservation: +1 + 0 + (-1) + (+1) ≡ 1 (mod 3)         │
└─────────────────────────────────────────────────────────────────┘
```

## Installation

```bash
# macOS with Flox
flox install gnuradio

# macOS with Homebrew
brew install gnuradio

# Ubuntu/Debian
sudo apt install gnuradio

# From source (GR4)
git clone https://github.com/gnuradio/gnuradio.git
cd gnuradio && mkdir build && cd build
cmake .. && make -j$(nproc) && sudo make install
```

## Block Types

| Type | Purpose | GF(3) Role |
|------|---------|------------|
| **Source** | Generate/receive signals | +1 (PLUS) |
| **Sync** | Sample-rate processing | 0 (ERGODIC) |
| **Sink** | Output/consume signals | -1 (MINUS) |
| **Hier** | Hierarchical sub-flowgraph | 0 (ERGODIC) |

## Embedded Python Block

```python
"""
Embedded Python Block - GF(3) Trit Tagger
Tags samples with spatial trit based on frequency
"""
import numpy as np
from gnuradio import gr

class blk(gr.sync_block):
    """GF(3) Trit Tagger for RF signals"""

    def __init__(self, center_freq=100e6):
        gr.sync_block.__init__(
            self,
            name='GF3 Trit Tagger',
            in_sig=[np.complex64],
            out_sig=[np.complex64]
        )
        self.center_freq = center_freq
        self.trit = self._freq_to_trit(center_freq)

    def _freq_to_trit(self, freq):
        """Map frequency to GF(3) trit"""
        # Frequency bands: VHF=+1, UHF=0, SHF=-1
        if freq < 300e6:      # VHF
            return 1
        elif freq < 3e9:      # UHF
            return 0
        else:                 # SHF+
            return -1

    def work(self, input_items, output_items):
        # Tag with trit metadata
        self.add_item_tag(
            0,  # output port
            self.nitems_written(0),
            pmt.intern("trit"),
            pmt.from_long(self.trit)
        )
        output_items[0][:] = input_items[0]
        return len(output_items[0])
```

## Flowgraph Examples

### FM Radio Receiver

```python
#!/usr/bin/env python3
# FM Radio with GF(3) tagging

from gnuradio import gr, blocks, analog, audio, filter
from gnuradio.filter import firdes
import osmosdr

class fm_radio(gr.top_block):
    def __init__(self, freq=100.1e6):
        gr.top_block.__init__(self, "FM Radio")

        # Source: RTL-SDR (+1 trit - generation)
        self.source = osmosdr.source(args="rtl=0")
        self.source.set_sample_rate(2.4e6)
        self.source.set_center_freq(freq)
        self.source.set_gain(40)

        # Filter: Low-pass (0 trit - processing)
        self.lpf = filter.fir_filter_ccf(
            10,  # decimation
            firdes.low_pass(1, 2.4e6, 100e3, 10e3)
        )

        # Demodulator: WBFM (-1 trit - extraction)
        self.demod = analog.wbfm_receive(
            quad_rate=240e3,
            audio_decimation=5
        )

        # Sink: Audio (+1 trit - output)
        self.audio_sink = audio.sink(48000)

        # Connect flowgraph
        self.connect(self.source, self.lpf, self.demod, self.audio_sink)

if __name__ == '__main__':
    tb = fm_radio(freq=100.1e6)
    tb.start()
    input('Press Enter to stop...')
    tb.stop()
    tb.wait()
```

### Spectrum Analyzer

```python
#!/usr/bin/env python3
# Spectrum analyzer with WebSocket output

from gnuradio import gr, blocks, fft
from gnuradio.fft import window
import numpy as np
import json

class spectrum_analyzer(gr.top_block):
    def __init__(self, center_freq=100e6, samp_rate=2.4e6):
        gr.top_block.__init__(self, "Spectrum Analyzer")

        self.fft_size = 1024

        # Source
        self.source = osmosdr.source(args="rtl=0")
        self.source.set_sample_rate(samp_rate)
        self.source.set_center_freq(center_freq)

        # FFT
        self.fft = fft.fft_vcc(
            self.fft_size,
            True,  # forward
            window.blackmanharris(self.fft_size),
            True   # shift
        )

        # Stream to vector
        self.s2v = blocks.stream_to_vector(
            gr.sizeof_gr_complex,
            self.fft_size
        )

        # Magnitude squared
        self.mag = blocks.complex_to_mag_squared(self.fft_size)

        # Python sink for WebSocket
        self.sink = blocks.probe_signal_vf(self.fft_size)

        self.connect(self.source, self.s2v, self.fft, self.mag, self.sink)

    def get_spectrum(self):
        """Get current spectrum as JSON"""
        data = self.sink.level()
        return json.dumps({
            'spectrum': data.tolist(),
            'trit': 0,  # ERGODIC - measurement
            'fft_size': self.fft_size
        })
```

## Integration with Muchas Radio

```python
# muchas_radio_sdr.py
# Bridge GNU Radio to MPD streaming

from gnuradio import gr, audio
import subprocess
import os

class RadioToMPD(gr.top_block):
    """Stream GNU Radio audio to MPD via FIFO"""

    def __init__(self, samp_rate=48000):
        gr.top_block.__init__(self, "Radio to MPD")

        # Create FIFO for MPD input
        self.fifo_path = "/tmp/gnuradio_audio.fifo"
        if not os.path.exists(self.fifo_path):
            os.mkfifo(self.fifo_path)

        # Audio source (from demodulator)
        self.audio_source = audio.source(samp_rate)

        # File sink to FIFO
        self.file_sink = blocks.file_sink(
            gr.sizeof_float,
            self.fifo_path,
            False  # don't append
        )

        self.connect(self.audio_source, self.file_sink)

    def start_mpd_stream(self):
        """Tell MPD to play from FIFO"""
        subprocess.run([
            "mpc", "add", f"file://{self.fifo_path}"
        ])
        subprocess.run(["mpc", "play"])
```

## GF(3) Signal Triads

```
┌─────────────────────────────────────────────────────────────────┐
│                    GF(3) SIGNAL TRIADS                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  RF Triad:                                                       │
│    Source (+1) ⊗ Channel (0) ⊗ Sink (-1) = 0 ✓                  │
│                                                                  │
│  Frequency Triad:                                                │
│    VHF (+1) ⊗ UHF (0) ⊗ SHF (-1) = 0 ✓                          │
│                                                                  │
│  Processing Triad:                                               │
│    Modulate (+1) ⊗ Filter (0) ⊗ Demodulate (-1) = 0 ✓           │
│                                                                  │
│  Audio Triad:                                                    │
│    Capture (+1) ⊗ Process (0) ⊗ Playback (-1) = 0 ✓             │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

## Hardware Support

| Device | Interface | Freq Range | Sample Rate |
|--------|-----------|------------|-------------|
| RTL-SDR | USB | 24-1766 MHz | 2.4 MS/s |
| HackRF | USB | 1-6000 MHz | 20 MS/s |
| USRP | USB/Eth | DC-6 GHz | 200 MS/s |
| PlutoSDR | USB | 70-6000 MHz | 61.44 MS/s |
| LimeSDR | USB | 100k-3.8 GHz | 61.44 MS/s |

## Commands

```bash
# Launch GNU Radio Companion (GUI)
gnuradio-companion

# Run flowgraph from command line
python3 my_flowgraph.py

# List available blocks
gr_modtool info

# Create new OOT module
gr_modtool newmod my_blocks

# Add Python block to module
gr_modtool add -t sync -l python my_block

# Install OOT module
cd build && cmake .. && make && sudo make install
```

## GR4 (Next Generation)

GNU Radio 4.0 brings:
- **C++20** with concepts and ranges
- **Reflection-based** block definitions
- **Graph-based** scheduling
- **Better performance** via SIMD

```cpp
// GR4 Block example
template<typename T>
struct Multiply : gr::Block<Multiply<T>> {
    gr::PortIn<T> in;
    gr::PortOut<T> out;
    float factor = 1.0f;

    gr::work::Status processBulk(auto& ins, auto& outs) {
        std::ranges::transform(ins, outs.begin(),
            [this](auto x) { return x * factor; });
        return gr::work::Status::OK;
    }
};
```

## Related Skills

| Skill | Connection |
|-------|------------|
| `muchas-radio` | Audio streaming integration |
| `whitehole-audio` | Audio loopback driver |
| `gay-mcp` | GF(3) trit coloring |
| `pluscode-zig` | Location-based frequency allocation |
| `fokker-planck-analyzer` | Signal diffusion analysis |

## Environment Variables

```bash
# GNU Radio paths
GR_CONF_CONTROLPORT_ON=True
GR_CONF_CONTROLPORT_EDGES_LIST=True
PYTHONPATH=/usr/local/lib/python3/dist-packages:$PYTHONPATH

# SDR device
SOAPY_SDR_ROOT=/usr/local
RTL_TCP_SERVER=127.0.0.1:1234

# GF(3) config
GR_TRIT_TAGGING=true
GR_TRIT_SOURCE=pluscode
```

---

**Skill Name**: gnu-radio
**Type**: SDR / Signal Processing / Python
**Trit**: -1 (MINUS - signal consumption)
**Seed**: 3800
**Key Insight**: Flowgraphs are compositional signal processing with GF(3) conservation
**Repository**: github.com/gnuradio/gnuradio
