#!/usr/bin/env python3
"""
Unified Memory Circuit Model
=============================
Models the path from current state (3 DGX Sparks + 1 Mac on WiFi)
to unified memory fabric (all devices sharing coherent address space
over high-bandwidth interconnect).

Devices discovered 2026-02-12:
  - gx10-acee  (10.1.10.153)  128GB unified, 20-core Grace, GB10 Blackwell, 4xCX7 ports
  - gx10-573f  (10.1.10.115)  128GB unified, 20-core Grace, GB10 Blackwell, 4xCX7 ports
  - gx10-a733  (10.1.10.149)  128GB unified, 20-core Grace, GB10 Blackwell, 4xCX7 ports
  - causality  (10.1.10.213)  24GB unified, M5, Thunderbolt 4 (40Gbps)
  - MikroTik   (192.168.88.1) RouterOS, reachable from gx10-acee 10GbE port

Each DGX Spark has:
  - 2x ConnectX-7 NICs (4 QSFP56 ports total), each supporting up to 200GbE
  - 1x Realtek 10GbE (management)
  - 1x MediaTek WiFi
  - GPU-NIC topology: all NICs at NODE distance from GPU (no NVLink, PCIe bridge)
  - RoCE v1 capable, mlx5 driver, firmware 28.45.4028
  - NCCL for GPU collective ops

Current state: ALL CX7 ports have NO CABLE. Everything runs over WiFi at ~100Mbps.
"""

import json
import math
from dataclasses import dataclass, field
from typing import Optional

# ============================================================
# Device and Link models
# ============================================================

@dataclass
class Port:
    name: str
    kind: str           # "cx7-qsfp56", "10gbe", "wifi", "thunderbolt4"
    max_gbps: float
    state: str          # "no-cable", "up", "down"
    peer: Optional[str] = None  # "device:port" if connected
    mtu: int = 1500
    rdma: bool = False  # RoCE capable

@dataclass
class Device:
    hostname: str
    ip: str
    memory_gb: int
    cpu: str
    gpu: Optional[str]
    gpu_memory_gb: int  # 0 if unified with CPU
    unified_memory: bool
    ports: list = field(default_factory=list)

@dataclass
class Link:
    src: str    # "device:port"
    dst: str    # "device:port"
    gbps: float
    latency_us: float
    rdma: bool
    kind: str   # "direct-dac", "switched", "wifi", "thunderbolt"

@dataclass
class SwitchDevice:
    hostname: str
    ip: str
    model: str
    ports: list = field(default_factory=list)
    switching_capacity_tbps: float = 0

# ============================================================
# Build the CURRENT topology
# ============================================================

def build_current_topology():
    """What exists right now."""

    spark_ports = lambda: [
        Port("enp1s0f0np0",    "cx7-qsfp56", 200, "no-cable", rdma=True),
        Port("enp1s0f1np1",    "cx7-qsfp56", 200, "no-cable", rdma=True),
        Port("enP2p1s0f0np0",  "cx7-qsfp56", 200, "no-cable", rdma=True),
        Port("enP2p1s0f1np1",  "cx7-qsfp56", 200, "no-cable", rdma=True),
        Port("enP7s7",         "10gbe",       10, "up",        rdma=False),
        Port("wlP9s9",         "wifi",         0.1, "up",      rdma=False),
    ]

    acee = Device("gx10-acee", "10.1.10.153", 128, "Grace (10xX925 + 10xA725)",
                  "GB10 Blackwell", 0, True, spark_ports())
    # acee's 10GbE is connected to MikroTik at 192.168.88.x
    acee.ports[4].state = "up"
    acee.ports[4].peer = "mikrotik:ether1"  # 10GbE Spark side, but CRS812 ether1 is only 1GbE

    s573f = Device("gx10-573f", "10.1.10.115", 128, "Grace (10xX925 + 10xA725)",
                   "GB10 Blackwell", 0, True, spark_ports())
    # 573f's 10GbE shows no link
    s573f.ports[4].state = "no-link"

    a733 = Device("gx10-a733", "10.1.10.149", 128, "Grace (10xX925 + 10xA725)",
                  "GB10 Blackwell", 0, True, spark_ports())
    a733.ports[4].state = "no-link"

    mac = Device("causality", "10.1.10.213", 24, "Apple M5 (4P+6E)",
                 None, 0, True, [
                     Port("en0",     "wifi",          0.1, "up", rdma=False),
                     Port("en1",     "thunderbolt4",  40,  "inactive", rdma=False),
                     Port("en2",     "thunderbolt4",  40,  "inactive", rdma=False),
                     Port("en3",     "thunderbolt4",  40,  "inactive", rdma=False),
                 ])

    mikrotik = SwitchDevice("mikrotik", "192.168.88.1", "RouterOS (model TBD)", [
        Port("ether-to-acee", "10gbe", 10, "up", peer="gx10-acee:enP7s7"),
    ])

    devices = [acee, s573f, a733, mac]
    switches = [mikrotik]

    # Current links: everything over WiFi through Comcast router
    links = [
        Link("gx10-acee:wlP9s9", "comcast:wifi", 0.1, 5000, False, "wifi"),
        Link("gx10-573f:wlP9s9", "comcast:wifi", 0.1, 5000, False, "wifi"),
        Link("gx10-a733:wlP9s9", "comcast:wifi", 0.1, 5000, False, "wifi"),
        Link("causality:en0",    "comcast:wifi", 0.1, 5000, False, "wifi"),
        Link("gx10-acee:enP7s7", "mikrotik:ether1", 1, 100, False, "switched"),  # bottlenecked at 1GbE
    ]

    return devices, switches, links


# ============================================================
# Build the TARGET topology (unified memory fabric)
# ============================================================

def build_target_topology():
    """What we want: all 3 Sparks at 200GbE via switch, Mac at max possible."""

    # CONFIRMED: MikroTik CRS812-8DS-2DQ-2DDQ at 192.168.88.1
    # Serial: HKB0AJ5Z0E5, RouterOS 7.19.5, Marvell-98DX7335 switch chip
    # Ports (from REST API):
    #   ether1, ether2                          (1GbE RJ45, ether1 is management)
    #   qsfp56-dd-1-{1..8}                     (QSFP-DD slot 1, 8 lanes, up to 400G)
    #   qsfp56-dd-2-{1..8}                     (QSFP-DD slot 2, 8 lanes, up to 400G)
    #   qsfp56-{1,2}-{1..4}                    (QSFP56 slots 3-4, 4 lanes each, up to 200G)
    #   sfp56-{1..8}                            (SFP56 slots, up to 50G each)
    # Current state: ALL fiber ports are DOWN, no cables. Only ether1 is running.
    # VLAN filtering is OFF. Default bridge spans all ports.
    crs812 = SwitchDevice("crs812", "192.168.88.1", "MikroTik CRS812-8DS-2DQ-2DDQ", [
        # QSFP-DD slot 1 (400G, 8 lanes) - use for Spark 1+2 via breakout
        Port("qsfp56-dd-1-1", "qsfp-dd-lane", 50, "down"),
        Port("qsfp56-dd-1-2", "qsfp-dd-lane", 50, "down"),
        Port("qsfp56-dd-1-3", "qsfp-dd-lane", 50, "down"),
        Port("qsfp56-dd-1-4", "qsfp-dd-lane", 50, "down"),
        Port("qsfp56-dd-1-5", "qsfp-dd-lane", 50, "down"),
        Port("qsfp56-dd-1-6", "qsfp-dd-lane", 50, "down"),
        Port("qsfp56-dd-1-7", "qsfp-dd-lane", 50, "down"),
        Port("qsfp56-dd-1-8", "qsfp-dd-lane", 50, "down"),
        # QSFP-DD slot 2 (400G, 8 lanes) - use for Spark 3 via breakout
        Port("qsfp56-dd-2-1", "qsfp-dd-lane", 50, "down"),
        Port("qsfp56-dd-2-2", "qsfp-dd-lane", 50, "down"),
        Port("qsfp56-dd-2-3", "qsfp-dd-lane", 50, "down"),
        Port("qsfp56-dd-2-4", "qsfp-dd-lane", 50, "down"),
        Port("qsfp56-dd-2-5", "qsfp-dd-lane", 50, "down"),
        Port("qsfp56-dd-2-6", "qsfp-dd-lane", 50, "down"),
        Port("qsfp56-dd-2-7", "qsfp-dd-lane", 50, "down"),
        Port("qsfp56-dd-2-8", "qsfp-dd-lane", 50, "down"),
        # QSFP56 slots 3-4 (200G each, 4 lanes)
        Port("qsfp56-1-1", "qsfp56-lane", 50, "down"),
        Port("qsfp56-1-2", "qsfp56-lane", 50, "down"),
        Port("qsfp56-1-3", "qsfp56-lane", 50, "down"),
        Port("qsfp56-1-4", "qsfp56-lane", 50, "down"),
        Port("qsfp56-2-1", "qsfp56-lane", 50, "down"),
        Port("qsfp56-2-2", "qsfp56-lane", 50, "down"),
        Port("qsfp56-2-3", "qsfp56-lane", 50, "down"),
        Port("qsfp56-2-4", "qsfp56-lane", 50, "down"),
        # SFP56 slots (50G each)
        Port("sfp56-1", "sfp56", 50, "down"),
        Port("sfp56-2", "sfp56", 50, "down"),
        Port("sfp56-3", "sfp56", 50, "down"),
        Port("sfp56-4", "sfp56", 50, "down"),
        Port("sfp56-5", "sfp56", 50, "down"),
        Port("sfp56-6", "sfp56", 50, "down"),
        Port("sfp56-7", "sfp56", 50, "down"),
        Port("sfp56-8", "sfp56", 50, "down"),
        # Management
        Port("ether1", "1gbe", 1, "up", peer="gx10-acee:enP7s7"),
        Port("ether2", "1gbe", 1, "down"),
    ], switching_capacity_tbps=1.6)

    # Each Spark uses ONE CX7 port at 200GbE to the switch
    # (second CX7 reserved for direct Spark-to-Spark DAC if needed)
    target_links = [
        # Spark 1 -> CRS812 qsfp-dd3 (native 200G)
        Link("gx10-acee:enP2p1s0f0np0", "crs812:qsfp-dd3", 200, 2, True, "switched"),
        # Spark 2 -> CRS812 qsfp-dd4 (native 200G)
        Link("gx10-573f:enP2p1s0f0np0", "crs812:qsfp-dd4", 200, 2, True, "switched"),
        # Spark 3 -> CRS812 qsfp-dd1 breakout lane 0 (200G)
        Link("gx10-a733:enP2p1s0f0np0", "crs812:qsfp-dd1", 200, 2, True, "switched"),
        # Mac -> CRS812 via Thunderbolt-to-10GbE adapter on qsfp28 port
        # (TB4 is 40Gbps raw, but 10GbE adapter is the practical ceiling without QSFP NIC)
        Link("causality:en1", "crs812:qsfp28-1", 10, 10, False, "thunderbolt-to-10gbe"),
        # Spark management: 10GbE stays for out-of-band
        Link("gx10-acee:enP7s7", "crs812:qsfp28-8", 10, 10, False, "switched"),
    ]

    # ALSO: direct DAC between pairs for NCCL ring topology
    direct_links = [
        # acee <-> 573f direct via second CX7 port
        Link("gx10-acee:enp1s0f0np0", "gx10-573f:enp1s0f0np0", 200, 1, True, "direct-dac"),
        # 573f <-> a733 direct via second CX7 port
        Link("gx10-573f:enp1s0f1np1", "gx10-a733:enp1s0f1np1", 200, 1, True, "direct-dac"),
        # a733 <-> acee direct via remaining CX7 port
        Link("gx10-a733:enp1s0f0np0", "gx10-acee:enp1s0f1np1", 200, 1, True, "direct-dac"),
    ]

    return crs812, target_links, direct_links


# ============================================================
# Gap analysis
# ============================================================

def compute_gaps():
    """What's missing between current and target."""
    gaps = []

    # 1. Switch -- ALREADY HAVE IT
    gaps.append({
        "component": "MikroTik CRS812-8DS-2DQ-2DDQ",
        "purpose": "200GbE switched fabric for all 3 Sparks + Mac management",
        "price_usd": 0,
        "status": "PRESENT - serial HKB0AJ5Z0E5, RouterOS 7.19.5, Marvell-98DX7335",
        "notes": "Connected to gx10-acee via ether1 (1GbE). All QSFP/SFP ports DOWN (no cables). "
                 "REST API accessible at http://192.168.88.1 admin:****. "
                 "Must disable autoneg and set 200G on QSFP-DD ports for Spark CX7."
    })

    # 2. QSFP56 DAC cables (Spark to switch)
    gaps.append({
        "component": "3x QSFP56 200G DAC cables (0.5-1m)",
        "purpose": "Connect each Spark CX7 -> CRS812 200G ports",
        "price_usd": 150,  # ~$50 each for passive DAC
        "status": "MISSING",
        "notes": "NVIDIA approved: Amphenol NJAAKK0006 or Luxshare LMTQF022-SD-R. "
                 "CRS812 QSFP-DD ports need breakout cables or native QSFP56."
    })

    # 3. Direct DAC cables (Spark to Spark ring)
    gaps.append({
        "component": "3x QSFP56 200G DAC cables (0.5m) for ring",
        "purpose": "Direct Spark-to-Spark NCCL ring (bypasses switch for allreduce)",
        "price_usd": 150,
        "status": "MISSING",
        "notes": "Uses the second CX7 NIC on each Spark. "
                 "Forms a 3-node ring: acee<->573f<->a733<->acee."
    })

    # 4. Mac connectivity upgrade
    gaps.append({
        "component": "Thunderbolt-to-10GbE adapter (e.g., OWC or Sonnet)",
        "purpose": "Connect Mac to CRS812 at 10Gbps (vs current WiFi ~100Mbps)",
        "price_usd": 100,
        "status": "MISSING",
        "notes": "TB4 can do 40Gbps but 10GbE adapters are $100 vs $500+ for 25GbE. "
                 "100x improvement over WiFi. Or use TB-to-SFP28 for 25G."
    })

    # 5. SSH keys for gx10-573f
    gaps.append({
        "component": "SSH key deployment to gx10-573f",
        "purpose": "Management access (currently user 'a' key works intermittently)",
        "price_usd": 0,
        "status": "PARTIAL - worked on retry",
        "notes": "ssh-copy-id from causality/acee to 573f needed for reliable access."
    })

    # 6. MikroTik access credentials -- HAVE THEM
    gaps.append({
        "component": "MikroTik admin credentials",
        "purpose": "Configure VLANs, port speeds, disable autoneg for 200G",
        "price_usd": 0,
        "status": "PRESENT - REST API confirmed working, WebFig/Winbox/API all accessible",
        "notes": "Full config read via REST API. All ports in default bridge, VLAN filtering OFF. "
                 "Need to: set QSFP-DD speed=200G, auto-negotiation=no, MTU=9000."
    })

    # 7. NCCL installation
    gaps.append({
        "component": "NCCL v2.28.3 on all 3 Sparks",
        "purpose": "GPU-to-GPU collective operations over RoCE fabric",
        "price_usd": 0,
        "status": "MISSING",
        "notes": "Not installed on any Spark. Required for distributed training. "
                 "See NVIDIA dgx-spark-playbooks for build instructions."
    })

    # 8. Netplan / IP configuration for CX7 ports
    gaps.append({
        "component": "Netplan config for CX7 interfaces on all Sparks",
        "purpose": "Assign IPs, enable RoCE, configure MTU 9000 for RDMA",
        "price_usd": 0,
        "status": "MISSING",
        "notes": "Use NVIDIA's cx7-netplan.yaml as template. "
                 "Set jumbo frames (MTU 9000+) for RDMA efficiency."
    })

    # 9. GDR (GPU Direct RDMA)
    gaps.append({
        "component": "GPUDirect RDMA (nvidia-peermem module)",
        "purpose": "Zero-copy GPU-to-GPU over network, bypassing CPU",
        "price_usd": 0,
        "status": "UNKNOWN",
        "notes": "Check if nvidia-peermem is loaded on Sparks. "
                 "Required for true unified memory semantics over fabric."
    })

    return gaps


# ============================================================
# Circuit metrics
# ============================================================

def compute_circuit_metrics():
    """Bandwidth, latency, and memory aggregation metrics."""

    total_memory_gb = 128 * 3 + 24  # 3 Sparks + Mac
    gpu_memory_gb = 128 * 3  # Sparks have unified CPU+GPU memory

    current = {
        "total_memory_gb": total_memory_gb,
        "gpu_accessible_gb": 128,  # single Spark, no fabric
        "aggregate_bandwidth_gbps": 0.4,  # all WiFi, 4 devices * ~100Mbps
        "worst_case_latency_us": 10000,  # WiFi
        "rdma_capable": False,
        "nccl_ring_bandwidth_gbps": 0,
        "bisection_bandwidth_gbps": 0.2,
    }

    target_switched = {
        "total_memory_gb": total_memory_gb,
        "gpu_accessible_gb": 128 * 3,  # all 3 Sparks via NCCL
        "aggregate_bandwidth_gbps": 200 * 3 + 10,  # 3x200G + Mac 10G
        "worst_case_latency_us": 5,  # switched RoCE
        "rdma_capable": True,
        "nccl_ring_bandwidth_gbps": 200,  # ring algo on 200G links
        "bisection_bandwidth_gbps": 400,  # 3-node: min cut = 2x200G
    }

    target_ring_plus_switch = {
        "total_memory_gb": total_memory_gb,
        "gpu_accessible_gb": 128 * 3,
        "aggregate_bandwidth_gbps": 200 * 6 + 10,  # 3x200G switch + 3x200G ring + 10G Mac
        "worst_case_latency_us": 2,  # direct DAC
        "rdma_capable": True,
        "nccl_ring_bandwidth_gbps": 200,  # ring saturates at link speed
        "bisection_bandwidth_gbps": 800,  # each node has 2x200G (switch + ring)
    }

    return current, target_switched, target_ring_plus_switch


# ============================================================
# Print circuit diagram
# ============================================================

def print_circuit():
    current, target_sw, target_full = compute_circuit_metrics()
    gaps = compute_gaps()
    devices, switches, links = build_current_topology()
    crs812, target_links, direct_links = build_target_topology()

    print("=" * 72)
    print("UNIFIED MEMORY CIRCUIT MODEL")
    print("=" * 72)

    print("\n## DEVICE INVENTORY")
    print(f"{'Device':<16} {'IP':<16} {'Mem':>6} {'CPU':<28} {'GPU':<16} {'CX7 Ports':>10}")
    print("-" * 96)
    for d in devices:
        cx7 = sum(1 for p in d.ports if p.kind == "cx7-qsfp56")
        print(f"{d.hostname:<16} {d.ip:<16} {d.memory_gb:>4}GB {d.cpu:<28} {d.gpu or 'N/A':<16} {cx7:>10}")

    print(f"\n## TOTAL RESOURCES")
    print(f"  Memory: {sum(d.memory_gb for d in devices)} GB ({sum(d.memory_gb for d in devices if d.gpu)}GB GPU-accessible)")
    print(f"  CX7 200GbE ports: {sum(1 for d in devices for p in d.ports if p.kind == 'cx7-qsfp56')} (all currently UNUSED)")
    print(f"  Thunderbolt 4 ports: {sum(1 for d in devices for p in d.ports if p.kind == 'thunderbolt4')} (all inactive)")

    print(f"\n## CURRENT TOPOLOGY (WiFi only)")
    print("  ┌─────────────┐")
    print("  │  Comcast AP  │  10.1.10.1")
    print("  │  (WiFi ~0.1G)│")
    print("  └──┬──┬──┬──┬─┘")
    print("     │  │  │  │")
    print("  ┌──┘  │  │  └──┐")
    print("  │     │  │     │")
    for d in devices:
        wifi_port = next((p for p in d.ports if p.kind == "wifi"), None)
        if wifi_port:
            print(f"  ├─ {d.hostname:<12} {d.ip:<16} {d.memory_gb}GB {'('+d.gpu+')' if d.gpu else ''}")
    print()
    print("  gx10-acee ──10GbE──> MikroTik (192.168.88.1) [only wired link]")

    print(f"\n## TARGET TOPOLOGY (200GbE fabric + ring)")
    print("  ┌──────────────────────────────────────────┐")
    print("  │  MikroTik CRS812-8DS-2DQ-2DDQ-RM         │")
    print("  │  2x400G-DD + 2x200G-DD + 8x50G           │")
    print("  │  Switching: 1.6 Tbps                      │")
    print("  └──┬────────┬────────┬────────┬─────────────┘")
    print("     │200G    │200G    │200G    │10G")
    print("     │        │        │        │")
    print("  ┌──┴──┐  ┌──┴──┐  ┌──┴──┐  ┌─┴──────┐")
    print("  │acee │  │573f │  │a733 │  │causality│")
    print("  │128GB│  │128GB│  │128GB│  │ 24GB    │")
    print("  │ GB10│  │ GB10│  │ GB10│  │ M5      │")
    print("  └──┬──┘  └──┬──┘  └──┬──┘  └─────────┘")
    print("     │        │        │")
    print("     └─200G───┴─200G───┘  (direct DAC ring)")
    print("     acee<->573f<->a733<->acee")

    print(f"\n## BANDWIDTH COMPARISON")
    print(f"{'Metric':<35} {'Current':>12} {'Switched':>12} {'Ring+Switch':>12}")
    print("-" * 75)
    for key in ["aggregate_bandwidth_gbps", "bisection_bandwidth_gbps",
                "nccl_ring_bandwidth_gbps", "worst_case_latency_us",
                "gpu_accessible_gb", "rdma_capable"]:
        c = current[key]
        s = target_sw[key]
        f = target_full[key]
        unit = ""
        if "gbps" in key: unit = " Gbps"
        elif "us" in key: unit = " us"
        elif "gb" in key: unit = " GB"
        label = key.replace("_", " ").title()
        print(f"  {label:<33} {str(c)+unit:>12} {str(s)+unit:>12} {str(f)+unit:>12}")

    speedup = target_full["aggregate_bandwidth_gbps"] / current["aggregate_bandwidth_gbps"]
    print(f"\n  Aggregate speedup: {speedup:.0f}x")

    print(f"\n## GAP ANALYSIS ({len(gaps)} items)")
    total_cost = 0
    for i, g in enumerate(gaps):
        status_icon = "X" if "MISSING" in g["status"] else ("~" if "PARTIAL" in g["status"] else "?")
        print(f"  [{status_icon}] {i+1}. {g['component']}")
        print(f"      Purpose: {g['purpose']}")
        if g['price_usd'] > 0:
            print(f"      Cost: ${g['price_usd']}")
            total_cost += g['price_usd']
        print(f"      Status: {g['status']}")
        print(f"      Notes: {g['notes']}")
        print()

    print(f"  TOTAL HARDWARE COST: ${total_cost}")
    print(f"  (excludes Thunderbolt-to-10GbE which is optional)")

    print(f"\n## UNIFIED MEMORY PATH")
    print("  Layer 1 (Physical):  QSFP56 DAC cables -> CRS812 switch + direct ring")
    print("  Layer 2 (Ethernet):  MikroTik VLAN 100 (GPU fabric), VLAN 1 (management)")
    print("  Layer 3 (IP):        192.168.100.0/24 on CX7 interfaces, jumbo MTU 9000")
    print("  Layer 4 (Transport): RoCE v2 (RDMA over Converged Ethernet)")
    print("  Layer 5 (Memory):    GPUDirect RDMA (nvidia-peermem) for zero-copy GPU-NIC")
    print("  Layer 6 (Compute):   NCCL v2.28.3 ring/tree allreduce across 3 GPUs")
    print("  Layer 7 (Framework): PyTorch DDP / DeepSpeed / vLLM tensor parallelism")
    print()
    print("  Effective unified memory: 384 GB (3x128GB)")
    print("  Max model size: ~200B params (384GB / ~2 bytes per param in FP16)")
    print("  Inter-GPU bandwidth: 200 Gbps (25 GB/s) per link")
    print("  AllReduce on ring: ~200 Gbps sustained with NCCL")

    print(f"\n## IMMEDIATE NEXT STEPS (ordered by impact)")
    print("  1. Get MikroTik admin credentials (WebFig at 192.168.88.1 from acee)")
    print("  2. Buy 6x QSFP56 DAC cables (3 for switch, 3 for ring) ~$300")
    print("  3. Buy or confirm MikroTik CRS812 (or use existing if it IS the 192.168.88.1)")
    print("  4. Cable: each Spark CX7 port 0 -> switch, CX7 port 1 -> next Spark (ring)")
    print("  5. Configure netplan on all 3 Sparks (192.168.100.{10,11,12}/24)")
    print("  6. Set CRS812 port speed to 200G (no autoneg), VLAN 100 untagged")
    print("  7. Install NCCL, verify with nccl-tests (all_reduce_perf)")
    print("  8. Load nvidia-peermem for GPUDirect RDMA")
    print("  9. Run distributed inference: vLLM --tensor-parallel-size 3")

    # Export as JSON for other tools
    circuit = {
        "devices": [
            {"hostname": d.hostname, "ip": d.ip, "memory_gb": d.memory_gb,
             "gpu": d.gpu, "unified_memory": d.unified_memory,
             "ports": [{"name": p.name, "kind": p.kind, "max_gbps": p.max_gbps,
                        "state": p.state, "rdma": p.rdma} for p in d.ports]}
            for d in devices
        ],
        "current_links": [
            {"src": l.src, "dst": l.dst, "gbps": l.gbps, "latency_us": l.latency_us,
             "rdma": l.rdma, "kind": l.kind}
            for l in links
        ],
        "target_links": [
            {"src": l.src, "dst": l.dst, "gbps": l.gbps, "latency_us": l.latency_us,
             "rdma": l.rdma, "kind": l.kind}
            for l in target_links + direct_links
        ],
        "gaps": gaps,
        "metrics": {
            "current": current,
            "target_switched": target_sw,
            "target_ring_plus_switch": target_full,
        }
    }

    with open("unified_memory_circuit.json", "w") as f:
        json.dump(circuit, f, indent=2)
    print(f"\n  Circuit model exported to unified_memory_circuit.json")


if __name__ == "__main__":
    print_circuit()
