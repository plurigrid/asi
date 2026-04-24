---
name: gx10-cluster
description: "3-node DGX Spark cluster networking: ConnectX-7 QSFP multi-host configuration, link-local ARP routing, NCCL multi-node setup. Covers non-approved cable workarounds and Tailscale mesh."
trit: 0
---

# GX10 Cluster — 3-Node DGX Spark Networking

## When to Use

- Configuring networking between DGX Spark units
- Debugging ConnectX-7 QSFP connectivity
- Setting up NCCL multi-node cluster
- Troubleshooting link-local routing on CX7 multi-host mode

## Cluster Inventory

| Node | Hostname | Tailscale IP | WiFi IP | Position |
|------|----------|-------------|---------|----------|
| Node 1 | gx10-9641 | 100.64.215.62 | 192.168.0.31 | Top |
| Node 2 | gx10-4a97 | 100.107.33.61 | 192.168.0.134 | Middle |
| Node 3 | gx10-94e2 | 100.95.223.101 | 192.168.0.167 | Bottom |

**SSH**: user `a`, password-based auth via `expect` (no `sshpass` available).

## Hardware

- **SoC**: NVIDIA GB10 Grace Blackwell Superchip
- **CPU**: 20-core Grace ARM64 (aarch64)
- **GPU**: Blackwell, 1 PFLOP AI
- **Memory**: 128GB unified LPDDR5x
- **Storage**: 4TB NVMe (~915GB usable)
- **OS**: Ubuntu 24.04, DGX Spark Version 7.4.0, kernel 6.17.0-1008-nvidia
- **NIC**: 2× ConnectX-7 (MT2910) per node, QSFP ports

## ConnectX-7 Multi-Host Architecture

Each physical QSFP port exposes **two logical interfaces** (f0, f1) due to GB10's PCIe x4 limitation. Two x4 PCIe links aggregate to achieve 200 Gbps per port.

```
Physical QSFP Port 1 → enp1s0f0np0 (PCIe domain 0000, func 0)
                      → enp1s0f1np1 (PCIe domain 0000, func 1)
Physical QSFP Port 2 → enP2p1s0f0np0 (PCIe domain 0002, func 0)
                      → enP2p1s0f1np1 (PCIe domain 0002, func 1)
```

With **approved QSFP112 cables**, both f0 and f1 come up → 200 Gbps aggregate.
With **QSFP28/QSFP56 cables**, only one function comes up → 100-200 Gbps single-lane.

## Cable Inventory

| Cable | Part Number | Type | Speed | Approved? |
|-------|-------------|------|-------|-----------|
| Amphenol (2m, black) | NDAAFF-0002 | QSFP28 passive DAC, 30AWG | 100G | No |
| HPE AOC (5m, aqua) | P06153-B22 | QSFP56 Active Optical | 200G | No |
| 10Gtek (0.5m) | CAB-ZQP/ZQP-P0.5M | QSFP28 passive DAC, 30AWG | 100G | No |

### NVIDIA-Approved Cables (recommended)

| Part | Type | Length | Price |
|------|------|--------|-------|
| Amphenol NJAAKK-N911 | QSFP112 400G DAC | 400mm | ~$180 |
| Amphenol NJAAKK-0006 | QSFP112 400G DAC | 500mm | ~$99 |
| Luxshare LMTQF022-SD-R | QSFP112 400G DAC | 400mm | ~$99 |

**Warning**: NVIDIA states only approved cables are supported. Others "may have active components that interfere with DGX's power and thermal envelope." Non-approved cables work at reduced speed but only one CX7 lane activates.

## Physical Topology

```
gx10-9641 (top)    ──── HPE 200G AOC ────── gx10-94e2 (bottom)
                                                  │
gx10-4a97 (middle) ── Amphenol 100G DAC ──────────┘
                   │
gx10-9641 (top)    ── 10Gtek 100G DAC ── gx10-4a97 (middle)
```

94e2 is the hub node (connected to both others). 9641↔4a97 direct link via 10Gtek cable.

## Networking Configuration

### Netplan (`/etc/netplan/40-cx7.yaml`)

Apply on all nodes:

```yaml
network:
  version: 2
  ethernets:
    enp1s0f0np0:
      link-local: [ ipv4 ]
    enp1s0f1np1:
      link-local: [ ipv4 ]
    enP2p1s0f0np0:
      link-local: [ ipv4 ]
    enP2p1s0f1np1:
      link-local: [ ipv4 ]
```

```bash
sudo wget -O /etc/netplan/40-cx7.yaml \
  https://github.com/NVIDIA/dgx-spark-playbooks/raw/main/nvidia/connect-two-sparks/assets/cx7-netplan.yaml
# Or write the extended version above for 3-node (includes Port 2)
sudo chmod 600 /etc/netplan/40-cx7.yaml
sudo netplan apply
```

### NetworkManager Connections

If NM overrides netplan with static IPs, fix per-interface:

```bash
sudo nmcli con mod <iface> ipv4.method link-local ipv4.addresses ""
sudo nmcli con up <iface>
```

If NM connections don't exist for Port 2:

```bash
sudo nmcli con add type ethernet con-name enP2p1s0f0np0 ifname enP2p1s0f0np0 ipv4.method link-local
sudo nmcli con add type ethernet con-name enP2p1s0f1np1 ifname enP2p1s0f1np1 ipv4.method link-local
sudo nmcli con up enP2p1s0f0np0
sudo nmcli con up enP2p1s0f1np1
```

### Critical: ARP and Routing Fixes for Multi-Host CX7

With non-approved cables, only one function (f0 or f1) activates per port. Since all interfaces share the 169.254.0.0/16 subnet, Linux sends replies out the wrong interface. **Both fixes are required:**

#### 1. ARP Filter (all nodes)

```bash
sudo sysctl -w net.ipv4.conf.all.arp_filter=1
sudo sysctl -w net.ipv4.conf.all.arp_announce=2
```

Persist in `/etc/sysctl.d/99-cx7.conf`:
```
net.ipv4.conf.all.arp_filter=1
net.ipv4.conf.all.arp_announce=2
```

#### 2. Policy-Based Routing (hub node with multiple connections)

For each CX7 interface with a link-local IP, add a source-based routing rule:

```bash
# Template: replace IP, IFACE, TABLE_NUM for each interface
sudo ip rule add from <LINK_LOCAL_IP> table <TABLE_NUM>
sudo ip route add 169.254.0.0/16 dev <IFACE> src <LINK_LOCAL_IP> table <TABLE_NUM>
```

Example for 94e2 (hub):
```bash
sudo ip rule add from 169.254.51.114 table 103
sudo ip route add 169.254.0.0/16 dev enp1s0f1np1 src 169.254.51.114 table 103
sudo ip rule add from 169.254.152.140 table 107
sudo ip route add 169.254.0.0/16 dev enP2p1s0f1np1 src 169.254.152.140 table 107
sudo ip rule add from 169.254.248.108 table 102
sudo ip route add 169.254.0.0/16 dev enp1s0f0np0 src 169.254.248.108 table 102
sudo ip rule add from 169.254.212.18 table 106
sudo ip route add 169.254.0.0/16 dev enP2p1s0f0np0 src 169.254.212.18 table 106
```

**Note**: Link-local IPs change on reboot. Persisted via `cx7-policy-routing.service` (see below).

### Persistence Across Reboots

All settings now persist via:

| Setting | Mechanism |
|---------|-----------|
| Link-local IPs + MTU 9000 | `/etc/netplan/40-cx7.yaml` |
| ARP filter/announce | `/etc/sysctl.d/99-cx7.conf` |
| Policy routing | `cx7-policy-routing.service` (systemd) |
| Sleep/suspend disabled | systemd targets masked + GNOME `sleep-inactive-ac-type=nothing` |

#### Policy Routing Service

`/usr/local/bin/cx7-policy-routing.sh` — runs at boot, reads current link-local IPs, creates per-interface routing tables:

```bash
#!/bin/bash
sleep 10  # wait for link-local IPs
TABLE=100
for IFACE in enp1s0f0np0 enp1s0f1np1 enP2p1s0f0np0 enP2p1s0f1np1; do
  IP=$(ip -4 addr show dev "$IFACE" 2>/dev/null | grep -oP '169\.254\.\d+\.\d+' | head -1)
  if [ -n "$IP" ]; then
    TABLE=$((TABLE + 1))
    ip rule del from "$IP" table "$TABLE" 2>/dev/null
    ip rule add from "$IP" table "$TABLE"
    ip route replace 169.254.0.0/16 dev "$IFACE" src "$IP" table "$TABLE"
  fi
done
```

Enabled via: `sudo systemctl enable cx7-policy-routing.service`

## Broken Netplan Files

DGX Spark generates `90-NM-*.yaml` files via NetworkManager that can contain invalid YAML (aliases, control characters). If `netplan apply` fails:

```bash
# Identify the broken file from the error message, then:
sudo mv /etc/netplan/90-NM-<uuid>.yaml /etc/netplan/90-NM-<uuid>.yaml.bak
sudo netplan apply
```

## Diagnostics

```bash
# Check CX7 detection
lspci | grep -i mellanox

# Check link status
ibdev2netdev

# Check interface IPs
ip -br addr show | grep -E 'enp1s0|enP2p1'

# Check link speed
ethtool enp1s0f0np0 | grep -i speed

# Check firmware
cat /sys/class/infiniband/*/fw_ver

# Check ARP neighbors
ip neigh show dev enp1s0f1np1

# Check routing
ip route show | grep 169.254
ip rule show
```

## NCCL + RoCE Configuration

### Software Stack

All nodes have: CUDA 13.0, Driver 580.142, NCCL 2.28.9 (built from source with Blackwell sm_121).

### Build NCCL from Source (all nodes)

```bash
sudo apt-get install -y libopenmpi-dev
git clone -b v2.28.9-1 https://github.com/NVIDIA/nccl.git ~/nccl/
cd ~/nccl/
make -j$(nproc) src.build NVCC_GENCODE="-gencode=arch=compute_121,code=sm_121"
```

### Build NCCL Tests (all nodes)

```bash
export CUDA_HOME=/usr/local/cuda
export MPI_HOME=/usr/lib/aarch64-linux-gnu/openmpi
export NCCL_HOME=$HOME/nccl/build
export LD_LIBRARY_PATH=$NCCL_HOME/lib:$CUDA_HOME/lib64:$MPI_HOME/lib:$LD_LIBRARY_PATH

git clone https://github.com/NVIDIA/nccl-tests.git ~/nccl-tests/
cd ~/nccl-tests/
make -j$(nproc) MPI=1
```

### SSH Keys

Passwordless SSH is required for MPI. Each node has `~/.ssh/id_ed25519` and a pre-existing `~/.ssh/id_ed25519_shared` (referenced in `~/.ssh/config`). Both pubkeys must be in `~/.ssh/authorized_keys` on all nodes. The shared key was the one that actually needed distributing.

### RoCE (RDMA over Converged Ethernet) — 8x faster than TCP

**Critical settings that made RoCE work:**

1. **MTU 9000** on CX7 interfaces (default 1500 gives only 1KB RDMA MTU):
   ```bash
   sudo ip link set enp1s0f0np0 mtu 9000
   ```

2. **NCCL environment variables**:
   ```bash
   export NCCL_SOCKET_IFNAME=enp1s0f0np0    # Bootstrap socket on CX7
   export NCCL_IB_HCA=rocep1s0f0             # Restrict to correct RDMA device
   export NCCL_IB_GID_INDEX=3                # RoCEv2 with IPv4-mapped GID
   export DISPLAY=                            # Suppress X11 auth errors
   ```

3. **MPI config** — separate control plane (WiFi) from data plane (CX7):
   ```bash
   --mca btl_tcp_if_include wlP9s9           # MPI control over WiFi
   --mca plm_rsh_agent "ssh -o StrictHostKeyChecking=no"
   ```

### Running NCCL Tests

#### 2-node test (94e2 ↔ 9641, 200G link)

```bash
export CUDA_HOME=/usr/local/cuda
export MPI_HOME=/usr/lib/aarch64-linux-gnu/openmpi
export NCCL_HOME=$HOME/nccl/build
export LD_LIBRARY_PATH=$NCCL_HOME/lib:$CUDA_HOME/lib64:$MPI_HOME/lib:$LD_LIBRARY_PATH
export DISPLAY=

mpirun -np 2 -H gx10-94e2:1,gx10-9641:1 \
  --mca plm_rsh_agent "ssh -o StrictHostKeyChecking=no" \
  --mca btl_tcp_if_include wlP9s9 \
  -x LD_LIBRARY_PATH \
  -x NCCL_SOCKET_IFNAME=enp1s0f0np0 \
  -x NCCL_IB_HCA=rocep1s0f0 \
  -x NCCL_IB_GID_INDEX=3 \
  -x DISPLAY \
  $HOME/nccl-tests/build/all_gather_perf -b 8 -e 128M -f 2 -g 1
```

#### TCP fallback (if RoCE fails)

Add `-x NCCL_IB_DISABLE=1` to the mpirun command. Expect ~2.2 GB/s instead of ~18 GB/s.

### Benchmark Results

#### RoCE (NET/IB) — 8 channels, GID index 3, MTU 9000

| Size | Algorithm BW (GB/s) | Bus BW (GB/s) |
|------|-------------------|---------------|
| 512KB | 8.05 | 4.03 |
| 1MB | 9.00 | 4.50 |
| 4MB | 15.42 | 7.71 |
| 16MB | 16.64 | 8.32 |
| 64MB | 17.79 | 8.89 |
| **128MB** | **18.03** | **9.01** |

**Avg bus bandwidth: 2.59 GB/s** (all sizes), **peak: 18 GB/s / 9 GB/s bus**

#### TCP fallback (NCCL_IB_DISABLE=1)

| Size | Algorithm BW (GB/s) | Bus BW (GB/s) |
|------|-------------------|---------------|
| 128MB | 2.23 | 1.12 |

**RoCE delivers ~8x improvement over TCP.**

### RoCE Diagnostics

```bash
# List RDMA devices
ibv_devices

# Check RDMA device details (port state, MTU, link layer)
ibv_devinfo -d rocep1s0f0

# Check GID table (need GID with RoCE v2 + IPv4-mapped address)
for i in 0 1 2 3; do
  echo -n "GID $i: "
  cat /sys/class/infiniband/rocep1s0f0/ports/1/gids/$i
  echo -n "  Type: "
  cat /sys/class/infiniband/rocep1s0f0/ports/1/gid_attrs/types/$i
done

# Verify active RDMA MTU (should be 4096 after setting interface MTU to 9000)
ibv_devinfo -d rocep1s0f0 | grep active_mtu
```

### Why RoCE Failed Initially

1. **Default MTU 1500** → RDMA active_mtu was only 1024 (too small for QP establishment)
2. **NCCL tried all RDMA devices** including ones connected to unreachable nodes → "unhandled system error"
3. **No GID index specified** → NCCL picked wrong GID (link-local IPv6 instead of IPv4-mapped)

Fix: restrict `NCCL_IB_HCA` to the correct device, set `NCCL_IB_GID_INDEX=3`, and set MTU 9000.

### Theoretical vs Actual Bandwidth

| Cable | Link Speed | Max Theoretical | Achieved (RoCE) | Utilization |
|-------|-----------|----------------|----------------|-------------|
| HPE P06153-B22 (200G AOC) | 200 Gbps | 25 GB/s | 18 GB/s | 72% |
| Amphenol NDAAFF-0002 (100G DAC) | 100 Gbps | 12.5 GB/s | TBD | TBD |
| 10Gtek CAB-ZQP (100G DAC) | 100 Gbps | 12.5 GB/s | TBD | TBD |

With approved QSFP112 cables (both CX7 lanes active), expect ~400 Gbps / 50 GB/s theoretical.

## Firmware Recovery (Bricked After Update)

1. Full power drain — unplug everything for 30+ minutes
2. Reconnect only power + direct display (try USB-C DP)
3. Hold ESC + press power to enter UEFI
4. Follow: https://docs.nvidia.com/dgx/dgx-spark-user-guide/system-recovery.html
5. If nothing works → NVIDIA support ticket

## References

- Spark Stacking Guide: https://docs.nvidia.com/dgx/dgx-spark/spark-clustering.html
- Connect Two Sparks Playbook: https://build.nvidia.com/spark/connect-two-sparks
- NCCL Two Sparks: https://build.nvidia.com/spark/nccl
- Approved cables: https://marketplace.nvidia.com/en-us/enterprise/personal-ai-supercomputers/
- CX7 multi-host explanation: https://forums.developer.nvidia.com/t/connectx-7-nic-in-dgx-spark/350417
- ConnectX-7 NIC disappearing: https://forums.developer.nvidia.com/t/connectx-7-nics-no-longer-appear/363193
