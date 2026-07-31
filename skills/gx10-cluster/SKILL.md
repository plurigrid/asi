---
name: gx10-cluster
description: "3-node DGX Spark cluster networking: ConnectX-7 multi-host, kernel-6.17 + DGX-OS-7.5 specifics, link-local fabric, NCCL multi-node prereqs, host-color renaming protocol, physical-identification recipes."
trit: 0
---
# GX10 Cluster — 3-Node DGX Spark Networking

## When to Use
- Configuring or debugging the 3-node DGX Spark cluster
- ConnectX-7 QSFP multi-host link-state issues
- Setting up NCCL multi-node + GPUDirect on kernel 6.17
- Recovering SSH access when authorized_keys gets reset
- Identifying a physical box by NIC LED pattern (no monitor required)

## Cluster Inventory (current — recolored 2026-04-30)
| Hex name | Old hex | Tailscale IP | LAN | DGX serial | Notes |
|---|---|---|---|---|---|
| **gx10-1a5f93** | gx10-acee | 100.90.238.119 | 192.168.0.56 (Vivarium) | TAMSAG000458WRK | hub-side, 200G×2 to c124b1 |
| **gx10-563e23** | gx10-94e2 | 100.95.223.101 | 169.254.x.x or DHCP | — | 100G×2 to c124b1; sometimes link-local-only |
| **gx10-c124b1** | gx10-4a97 | 100.107.33.61 | 192.168.0.134 (Vivarium) | TAMSAG002415HMP | central HUB; bridges Domain A↔B |
| 6cec13 | gx10-9641 | 100.64.215.62 | 169.254.x.x | — | 4th historical node, intermittent |
| gx10-9827 | (never renamed) | 100.110.149.7 | 10.0.0.247 (legacy LAN) | — | Seattle DERP, offline 47d+ |

Tailnet: `pirate-dragon.ts.net` (org `plurigrid.org.github`).

**SSH**: user `a`, password `${GX10_SUDO_PW}` (NOT the legacy `aaaaaa` referenced in older notes — that was wrong). 1a5f93 has NOPASSWD sudo; 563e23 + c124b1 require the password for sudo. Auth via `expect` heredoc (no `sshpass` on macOS); see "SSH key reset recovery" below.

## Hardware
- SoC: NVIDIA GB10 Grace Blackwell, 20-core Grace ARM64
- GPU: Blackwell GB10, ~1 PFLOP AI, driver 580.142, compute_cap 12.1
- Memory: 128GB unified LPDDR5x
- Storage: 4TB NVMe
- NIC: 2× ConnectX-7 (Mellanox MT2910 / PCI ID `15b3:1021`), 4 ports total per node, firmware **28.45.4028**
- Front-panel `enP7s7`: Realtek `r8127` (NOT a ConnectX) — used for management, often NO-CARRIER

## OS
- Ubuntu 24.04.4 LTS
- **DGX OS 7.5.0** (OTA 2026-04-30 from 7.4.0)
- Kernel **6.17.0-1014-nvidia** (post-dist-upgrade 2026-04-30)
- CUDA 13.0.3, NCCL 2.30.4 (where installed)

## Kernel 6.17 caveats
- **`nvidia-peermem` returns `EINVAL`** on this kernel — `ib_peer_mem` API removed upstream; GPUDirect now goes via **DMA-BUF** through `mlx5_ib` directly. Don't auto-load `nvidia-peermem` (drop any `/etc/modules-load.d/nvidia-peermem.conf`); NCCL ≥ 2.20 picks DMA-BUF transparently.
- **`mst_pci` / `mst_pciconf` not in `/lib/modules/6.17.0-1014-nvidia/`** — Mellanox MFT package ships userspace tools (`mlxconfig`, `mlxlink`, `mlxfwmanager`) that work in PCI-config-space fallback. `sudo mst start` will fail; `mlxconfig -d /sys/bus/pci/devices/0000:01:00.0 query` still works.

## ConnectX-7 logical layout
Each NIC has 2 physical ports; each port presents 2 logical interfaces (f0/f1) due to GB10 PCIe x4 width. Names:
```
NIC1 (PCI 0000:01:00.0/.1): enp1s0f0np0   enp1s0f1np1
NIC2 (PCI 0002:01:00.0/.1): enP2p1s0f0np0 enP2p1s0f1np1
```

## Cable inventory (observed 2026-04-30)
| Cable | Speed observed | Notes |
|---|---|---|
| Mellanox 5m QSFP28 DAC | **200 Gb/s PAM4** | only this length+vendor combo trains 200G across our pairs |
| Mellanox 1m + Amphenol 2m mix | 100 Gb/s NRZ | shorter / mixed-vendor → 100G NRZ only |
| 10Gtek 0.5m DAC | 100 Gb/s | works at QSFP28 NRZ |

NVIDIA's officially "approved" cables (QSFP112 400G) get full 400G PAM4 across BOTH lanes; non-approved cables only train one lane (100/200G).

## Physical topology (post-rewire 2026-04-30)
Hub-and-spoke. **c124b1 is the hub.**

```
        gx10-1a5f93                       gx10-c124b1                       gx10-563e23
   ┌─────────────┐   200G×2 (Mellanox  ┌─────────────┐  100G×2 (Amphenol  ┌─────────────┐
   │ ef ✗ DOWN   │     5m DAC)         │ 98 ✓ 200G   │       2m DAC)      │ e3 ✗ DOWN   │
   │ f0 ✓ 200G ══╪═════════════════════│ 9c ✓ 200G   │═══════════════════════│ e4 ✓ 100G │
   │ f3 ✗ DOWN   │                     │ 99 ✓ 100G   │                     │ e7 ✗ DOWN  │
   │ f4 ✓ 200G ══╪═════════════════════│ 9d ✓ 100G   │═══════════════════════│ e8 ✓ 100G │
   └─────────────┘                     └─────────────┘                     └─────────────┘
```

c124b1 routes between Domain A (200G to 1a5f93) and Domain B (100G to 563e23). No direct 1a5f93↔563e23 link unless the spare Mellanox-5m cable is moved to ef↔e3 / f3↔e7.

## LLDP "shared L2" trick — NOT a hidden 4th machine
Each ConnectX port sees its **sibling** port's LLDPDUs because the **hub box's NIC eSwitch internally bridges** between its two same-domain ports. e.g. on 1a5f93, port `f0` receives LLDP frames whose source MAC is `f4` (its OWN sibling). This looks like 4 boxes are on a shared wire; it's actually 2 hosts + the eSwitch. Verified by tcpdump source-MAC analysis — no unknown MACs ever appear.

## NCCL multi-node prereqs (install on every node)
```bash
sudo apt install -y libnccl2 libnccl-dev mft lldpd gdrcopy
sudo systemctl enable --now lldpd
# nvidia-peermem: don't bother — see "Kernel 6.17 caveats"
```
NCCL ≥ 2.30.4 ships with cuda-13.0.3 stack via NVIDIA's `cuda-compute-repo`.

## nccl-tests (build once, distribute)
```bash
git clone --depth 1 https://github.com/NVIDIA/nccl-tests.git ~/nccl-tests
cd ~/nccl-tests
make MPI=0 CUDA_HOME=/usr/local/cuda NCCL_HOME=/usr -j$(nproc)
# fan-out via tar stream:
ssh a@<src> 'cd ~ && tar cf - nccl-tests' > /tmp/nt.tar
ssh a@<dst1> 'cd ~ && tar xf -' < /tmp/nt.tar &
ssh a@<dst2> 'cd ~ && tar xf -' < /tmp/nt.tar &
wait
```

## Noise-suppression cleanup (do once per node)
Stops the recurring "Connection failed: activation of network connection failed" notification from NetworkManager and the failed `dnsmasq.service` unit.
```bash
for n in 1 2 3 4; do
  sudo nmcli con mod "Wired connection $n" connection.autoconnect no
  sudo nmcli con down "Wired connection $n" 2>/dev/null
done
sudo systemctl disable --now dnsmasq.service
sudo systemctl mask dnsmasq.service
```
`dnsmasq` ships configured for the front-panel `enP7s7` (DGX cluster-share / PXE feature) which has no neighbor here → fails forever.

## SSH key reset recovery
When `authorized_keys` gets cleared (happened mid-session 2026-04-30), re-push via `expect`:
```bash
PUBKEY=$(cat ~/.ssh/id_ed25519.pub)
for IP in 100.90.238.119 100.95.223.101 100.107.33.61; do
  /usr/bin/expect <<EXPECTEOF
    set timeout 30
    spawn ssh -o StrictHostKeyChecking=accept-new -o PubkeyAuthentication=no -o PreferredAuthentications=password a@$IP {mkdir -p ~/.ssh && chmod 700 ~/.ssh && grep -qF "$PUBKEY" ~/.ssh/authorized_keys 2>/dev/null || echo "$PUBKEY" >> ~/.ssh/authorized_keys; chmod 600 ~/.ssh/authorized_keys}
    expect {
      "*assword:" { send "${GX10_SUDO_PW}"; exp_continue }
      "yes/no"    { send "yes"; exp_continue }
      eof
    }
EXPECTEOF
done
```

## Physical-box identification (no monitor required)
DGX Spark has only HDMI audio output, so unattached boxes can't beep. Use NIC LEDs instead — `ethtool -p <iface> <duration>` makes the rear NIC LED blink. Hostname-encoded patterns:
```bash
# Encode the box's leading hex digits as blink-counts (e.g. 5-6-3 for gx10-563...)
PORTS='enp1s0f0np0 enp1s0f1np1 enP2p1s0f0np0 enP2p1s0f1np1'
flash() {
  for IF in $PORTS; do
    timeout $1 ethtool -p $IF 60 >/dev/null 2>&1 &
  done
  sleep $1
  pkill -f 'ethtool -p' 2>/dev/null
}
for n in 5 6 3; do
  for i in $(seq 1 $n); do flash 0.18; sleep 0.18; done
  sleep 1.4
done
# Pair with a CPU stress (`yes >/dev/null &` x N) for audible fan ramp.
```

## fwupd UEFI capsules
Post-dist-upgrade, capsules may be staged for next boot. Verify with `fwupdmgr get-history`. The 7.5.0 OTA on 2026-04-30 staged + applied EC + UEFI Device Firmware + USB-C PD updates on reboot.

## Tailscale tailnet identity
- Tailnet: `pirate-dragon.ts.net`
- Org: `plurigrid.org.github`
- DERP: all 3 active boxes use **sfo** relay (San Francisco area). `gx10-9827` was on **sea** (Seattle) — different geographic site, hence offline 47+ days from this cluster's perspective.
