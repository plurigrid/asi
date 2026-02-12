#!/usr/bin/env python3
"""
DGX Spark Fleet Provisioning Script
====================================
Provisions 4+ new DGX Sparks headlessly through MikroTik CRS812 switch.

Architecture:
  gx10-acee (10.1.10.153) -- 10GbE --> MikroTik CRS812 (192.168.88.1)
  New Sparks -- QSFP/CX7 cables --> CRS812 fiber ports
  
Three phases:
  Phase 1: Configure MikroTik DHCP for new Spark subnet
  Phase 2: Detect new Sparks as they boot and get DHCP leases
  Phase 3: Post-provision each Spark (SSH keys, netplan, NCCL, env vars)

References:
  - NVIDIA DGX Spark PXE Boot: https://docs.nvidia.com/dgx/dgx-spark/pxe.html
  - Spark Stacking: https://docs.nvidia.com/dgx/dgx-spark/spark-clustering.html
  - Connect Two Sparks: https://build.nvidia.com/spark/connect-two-sparks/stacked-sparks
  - Multi-Spark over switch (SIN3R6Y): reddit.com/r/LocalLLaMA/comments/1oieip0/
"""

import subprocess
import json
import time
import sys
import os
import argparse
from dataclasses import dataclass, field
from typing import Optional
from pathlib import Path

# ============================================================
# Configuration
# ============================================================

SPARK_USER = "a"
SPARK_PASSWORD = "aaaaaa"
SPARK_PASSWORD_HASH = "$6$1mA2NVWvZnHVHX40$I0aXGcQ61rG7tyyfVWpHE4iP8xErIkf5csISpWNwW9768c0vIldYCxPiPg.3Bq0fInZa4OUKv.A94BbwVSPAL0"

MIKROTIK_IP = "192.168.88.1"
MIKROTIK_USER = "admin"
MIKROTIK_PASS = "UALTKT9PVL"

# gx10-acee is our control node (already initialized)
CONTROL_NODE = "10.1.10.153"
CONTROL_NODE_BRIDGE_IP = "192.168.88.2"

# Existing initialized Sparks
EXISTING_SPARKS = {
    "gx10-acee": {"wifi_ip": "10.1.10.153", "bridge_ip": "192.168.88.2", "memory_gb": 128},
    "gx10-573f": {"wifi_ip": "10.1.10.115", "bridge_ip": None, "memory_gb": 128},
    "gx10-a733": {"wifi_ip": "10.1.10.149", "bridge_ip": None, "memory_gb": 128},
}

EXPECTED_NEW_SPARKS = 4
SPARK_MEMORY_GB = 128

# CX7 fabric subnet (separate from MikroTik management 192.168.88.0/24)
CX7_SUBNET = "192.168.100"
CX7_SUBNET2 = "192.168.200"  # Second CX7 half-complex

# CX7 interface names on each Spark
CX7_INTERFACES = {
    "half1_port1": "enp1s0f0np0",
    "half1_port2": "enp1s0f1np1",
    "half2_port1": "enP2p1s0f0np0",
    "half2_port2": "enP2p1s0f1np1",
}

ROCE_DEVICES = {
    "half1_port1": "rocep1s0f0",
    "half1_port2": "rocep1s0f1",
    "half2_port1": "roceP2p1s0f0",
    "half2_port2": "roceP2p1s0f1",
}


@dataclass
class SparkNode:
    hostname: str
    dhcp_ip: Optional[str] = None
    mac: Optional[str] = None
    cx7_ips: dict = field(default_factory=dict)
    provisioned: bool = False
    node_id: int = 0


def ssh_cmd(host, cmd, user=SPARK_USER, timeout=30):
    """Execute command via SSH, return (returncode, stdout, stderr)."""
    full = [
        "ssh", "-o", "ConnectTimeout=10",
        "-o", "StrictHostKeyChecking=no",
        "-o", "UserKnownHostsFile=/dev/null",
        "-o", "LogLevel=ERROR",
        f"{user}@{host}", cmd
    ]
    try:
        r = subprocess.run(full, capture_output=True, text=True, timeout=timeout)
        return r.returncode, r.stdout.strip(), r.stderr.strip()
    except subprocess.TimeoutExpired:
        return -1, "", "timeout"


def ssh_cmd_sudo(host, cmd, user=SPARK_USER, timeout=30):
    """Execute sudo command via SSH using password."""
    echo_pass = f"echo '{SPARK_PASSWORD}' | sudo -S {cmd}"
    return ssh_cmd(host, echo_pass, user=user, timeout=timeout)


def mikrotik_api(endpoint, method="GET", data=None):
    """Call MikroTik REST API from control node."""
    if method == "GET":
        curl_cmd = f"curl -s -u '{MIKROTIK_USER}:{MIKROTIK_PASS}' 'http://{MIKROTIK_IP}/rest{endpoint}'"
    else:
        json_data = json.dumps(data) if data else "{}"
        curl_cmd = f"curl -s -X {method} -u '{MIKROTIK_USER}:{MIKROTIK_PASS}' -H 'Content-Type: application/json' -d '{json_data}' 'http://{MIKROTIK_IP}/rest{endpoint}'"
    rc, out, err = ssh_cmd(CONTROL_NODE, curl_cmd, timeout=15)
    if rc == 0 and out:
        try:
            return json.loads(out)
        except json.JSONDecodeError:
            pass
    return None


# ============================================================
# Phase 1: MikroTik DHCP Configuration
# ============================================================

MIKROTIK_DHCP_SCRIPT = """
# Configure DHCP server on MikroTik CRS812 for new Spark provisioning
# This creates a DHCP pool on the bridge so new Sparks get IPs automatically

# Add IP to bridge if not already present
/ip address add address=192.168.88.1/24 interface=bridge1 comment="spark-provision"

# Create DHCP pool
/ip pool add name=spark-pool ranges=192.168.88.100-192.168.88.200

# Create DHCP network  
/ip dhcp-server network add address=192.168.88.0/24 gateway=192.168.88.1 dns-server=8.8.8.8,8.8.4.4

# Create DHCP server on bridge
/ip dhcp-server add name=spark-dhcp interface=bridge1 address-pool=spark-pool lease-time=1h disabled=no

# Enable NAT for internet access (so Sparks can download updates during first-boot)
/ip firewall nat add chain=srcnat out-interface=ether1 action=masquerade comment="spark-provision-nat"

# Enable IP forwarding
/ip settings set ip-forward=yes
"""


def phase1_configure_mikrotik():
    """Configure MikroTik DHCP server for new Spark provisioning."""
    print("\n" + "=" * 60)
    print("PHASE 1: MikroTik DHCP Configuration")
    print("=" * 60)

    # Check current state
    result = mikrotik_api("/ip/dhcp-server")
    if result and not isinstance(result, dict):
        print(f"  Existing DHCP servers: {len(result)}")
        for srv in result:
            print(f"    - {srv.get('name', '?')}: {srv.get('interface', '?')} ({srv.get('disabled', '?')})")
    else:
        print("  No DHCP servers found or API unreachable")
        print("  --> You need to configure DHCP manually on MikroTik")
        print()
        print("  Run these commands via MikroTik terminal (WebFig/WinBox/SSH):")
        print()
        for line in MIKROTIK_DHCP_SCRIPT.strip().split('\n'):
            if line.strip() and not line.strip().startswith('#'):
                print(f"    {line.strip()}")
        print()
        print("  OR via WebFig at http://192.168.88.1")
        return False

    # Try to configure via API
    print("  Configuring DHCP via REST API...")

    # Add pool
    r = mikrotik_api("/ip/pool", "PUT", {
        "name": "spark-pool",
        "ranges": "192.168.88.100-192.168.88.200"
    })
    print(f"  Pool: {r}")

    # Add network
    r = mikrotik_api("/ip/dhcp-server/network", "PUT", {
        "address": "192.168.88.0/24",
        "gateway": "192.168.88.1",
        "dns-server": "8.8.8.8,8.8.4.4"
    })
    print(f"  Network: {r}")

    # Add server
    r = mikrotik_api("/ip/dhcp-server", "PUT", {
        "name": "spark-dhcp",
        "interface": "bridge1",
        "address-pool": "spark-pool",
        "lease-time": "01:00:00",
        "disabled": "false"
    })
    print(f"  Server: {r}")

    return True


# ============================================================
# Phase 2: Detect New Sparks
# ============================================================

def phase2_detect_sparks(timeout_minutes=30):
    """Wait for new Sparks to appear on the network via DHCP leases."""
    print("\n" + "=" * 60)
    print("PHASE 2: Detecting New Sparks")
    print("=" * 60)
    print(f"  Waiting up to {timeout_minutes} minutes for {EXPECTED_NEW_SPARKS} new Sparks...")
    print("  Each Spark should:")
    print("    1. Be plugged into CRS812 via QSFP cable AND 10GbE management cable")
    print("    2. Have power connected (boots automatically)")
    print("    3. Go through first-boot wizard (see below)")
    print()
    print("  FIRST-BOOT OPTIONS (pick one):")
    print("  A) WiFi Hotspot: Connect laptop to each Spark's hotspot (SSID on sticker)")
    print("     -> Complete wizard in browser -> create user 'a', password 'aaaaaa'")
    print("  B) Monitor+Keyboard: Plug in, follow on-screen wizard")
    print("  C) If Spark has Ethernet with internet -> wizard skips WiFi, just create user")
    print()

    discovered = []
    known_macs = set()

    # Get existing ARP entries to filter
    rc, out, _ = ssh_cmd(CONTROL_NODE, "ip -j neigh show dev enP7s7 2>/dev/null || ip neigh show dev enP7s7")
    if rc == 0:
        try:
            entries = json.loads(out)
            for e in entries:
                if e.get("lladdr"):
                    known_macs.add(e["lladdr"].lower())
        except (json.JSONDecodeError, TypeError):
            for line in out.split('\n'):
                parts = line.split()
                if len(parts) >= 5:
                    known_macs.add(parts[4].lower())

    print(f"  Known MACs on bridge: {len(known_macs)}")
    start = time.time()

    while len(discovered) < EXPECTED_NEW_SPARKS and (time.time() - start) < timeout_minutes * 60:
        # Scan for new hosts on 192.168.88.0/24
        rc, out, _ = ssh_cmd(CONTROL_NODE,
            "for i in $(seq 100 200); do "
            "(ping -c1 -W1 192.168.88.$i &>/dev/null && echo 192.168.88.$i) & "
            "done; wait",
            timeout=60)

        if rc == 0 and out:
            for ip in out.strip().split('\n'):
                ip = ip.strip()
                if not ip or ip == CONTROL_NODE_BRIDGE_IP or ip == MIKROTIK_IP:
                    continue
                # Check if this is a new Spark
                already = any(s.dhcp_ip == ip for s in discovered)
                if already:
                    continue
                # Try SSH
                rc2, hostname, _ = ssh_cmd(ip, "hostname", timeout=10)
                if rc2 == 0 and hostname.startswith("gx10"):
                    node = SparkNode(
                        hostname=hostname,
                        dhcp_ip=ip,
                        node_id=len(EXISTING_SPARKS) + len(discovered) + 1
                    )
                    # Get MAC
                    rc3, mac_out, _ = ssh_cmd(ip, "cat /sys/class/net/enP7s7/address 2>/dev/null || cat /sys/class/net/eth0/address 2>/dev/null")
                    if rc3 == 0:
                        node.mac = mac_out.strip()
                    discovered.append(node)
                    print(f"  FOUND #{len(discovered)}: {hostname} at {ip} (MAC: {node.mac})")

        if len(discovered) < EXPECTED_NEW_SPARKS:
            remaining = EXPECTED_NEW_SPARKS - len(discovered)
            elapsed = int(time.time() - start)
            print(f"  [{elapsed}s] Found {len(discovered)}/{EXPECTED_NEW_SPARKS}, waiting for {remaining} more...")
            time.sleep(15)

    print(f"\n  Discovered {len(discovered)} new Sparks")
    return discovered


def phase2_manual_entry():
    """Manually enter Spark IPs if auto-detection isn't working."""
    print("\n" + "=" * 60)
    print("PHASE 2 (MANUAL): Enter Spark IPs")
    print("=" * 60)
    discovered = []
    print("  Enter IPs of new Sparks (empty line to finish):")
    while True:
        ip = input(f"  Spark #{len(discovered)+1} IP: ").strip()
        if not ip:
            break
        rc, hostname, _ = ssh_cmd(ip, "hostname", timeout=10)
        if rc == 0:
            node = SparkNode(
                hostname=hostname,
                dhcp_ip=ip,
                node_id=len(EXISTING_SPARKS) + len(discovered) + 1
            )
            rc2, mac_out, _ = ssh_cmd(ip, "cat /sys/class/net/enP7s7/address 2>/dev/null")
            if rc2 == 0:
                node.mac = mac_out.strip()
            discovered.append(node)
            print(f"    -> {hostname} (MAC: {node.mac})")
        else:
            print(f"    -> Cannot reach {ip} via SSH")
    return discovered


# ============================================================
# Phase 3: Post-Provisioning
# ============================================================

NETPLAN_CX7_SWITCHED = """network:
  version: 2
  ethernets:
    enp1s0f0np0:
      addresses:
        - {cx7_ip1}/24
      dhcp4: no
      mtu: 9000
    enp1s0f1np1:
      addresses:
        - {cx7_ip2}/24
      dhcp4: no
      mtu: 9000
    enP2p1s0f0np0:
      addresses:
        - {cx7_ip3}/24
      dhcp4: no
      mtu: 9000
    enP2p1s0f1np1:
      addresses:
        - {cx7_ip4}/24
      dhcp4: no
      mtu: 9000
"""

NCCL_ENV_SWITCHED = """# NCCL environment for multi-Spark over CRS812 switch
# Based on SIN3R6Y's guide: reddit.com/r/LocalLLaMA/comments/1oieip0/
export CUDA_HOME="/usr/local/cuda"
export MPI_HOME="/usr/lib/aarch64-linux-gnu/openmpi"
export NCCL_HOME="$HOME/nccl/build/"
export LD_LIBRARY_PATH="$NCCL_HOME/lib:$CUDA_HOME/lib64/:$MPI_HOME/lib:$LD_LIBRARY_PATH"

export IP_IF_NAME=enp1s0f0np0,enP2p1s0f1np1
export IB_IF_NAME=rocep1s0f0,roceP2p1s0f1

export UCX_NET_DEVICES=$IP_IF_NAME
export NCCL_SOCKET_IFNAME=$IP_IF_NAME
export NCCL_SOCKET_FAMILY=AF_INET
export NCCL_IB_HCA=$IB_IF_NAME
export NCCL_IB_GID_INDEX=3
export NCCL_IB_TC=3
export NCCL_IB_MERGE_NICS=1
export OMPI_MCA_btl_tcp_if_include=$IP_IF_NAME
"""


def provision_single_spark(node: SparkNode, all_nodes: list):
    """Post-provision a single Spark after first-boot is complete."""
    ip = node.dhcp_ip
    nid = node.node_id
    print(f"\n  --- Provisioning {node.hostname} (node {nid}) at {ip} ---")

    # Step 1: Deploy SSH key
    print(f"  [1/7] Deploying SSH key...")
    rc, out, err = ssh_cmd(CONTROL_NODE,
        f"ssh-copy-id -o StrictHostKeyChecking=no {SPARK_USER}@{ip} </dev/null 2>&1 || echo 'KEY_ALREADY_SET'",
        timeout=30)
    if "KEY_ALREADY_SET" not in out and rc != 0:
        print(f"    WARNING: ssh-copy-id may need password. Run manually:")
        print(f"    ssh-copy-id {SPARK_USER}@{ip}")

    # Step 2: Set hostname
    desired_hostname = f"spark-{nid:02d}"
    print(f"  [2/7] Setting hostname to {desired_hostname}...")
    ssh_cmd_sudo(ip, f"hostnamectl set-hostname {desired_hostname}")

    # Step 3: Configure CX7 netplan for switched fabric
    # Node gets 4 IPs: 192.168.100.{nid*10+0..3} and 192.168.200.{nid*10+0..3}
    base = nid * 10
    cx7_config = NETPLAN_CX7_SWITCHED.format(
        cx7_ip1=f"{CX7_SUBNET}.{base}",
        cx7_ip2=f"{CX7_SUBNET2}.{base + 1}",
        cx7_ip3=f"{CX7_SUBNET}.{base + 2}",
        cx7_ip4=f"{CX7_SUBNET2}.{base + 3}",
    )
    node.cx7_ips = {
        "enp1s0f0np0": f"{CX7_SUBNET}.{base}",
        "enp1s0f1np1": f"{CX7_SUBNET2}.{base + 1}",
        "enP2p1s0f0np0": f"{CX7_SUBNET}.{base + 2}",
        "enP2p1s0f1np1": f"{CX7_SUBNET2}.{base + 3}",
    }

    print(f"  [3/7] Deploying CX7 netplan config...")
    escaped = cx7_config.replace("'", "'\\''")
    ssh_cmd_sudo(ip, f"bash -c \"cat > /etc/netplan/40-cx7.yaml << 'NETPLANEOF'\n{cx7_config}NETPLANEOF\"")
    ssh_cmd_sudo(ip, "chmod 600 /etc/netplan/40-cx7.yaml")
    ssh_cmd_sudo(ip, "netplan apply")

    # Step 4: Enable jumbo frames on 10GbE too
    print(f"  [4/7] Setting MTU 9000 on CX7 interfaces...")
    for iface in CX7_INTERFACES.values():
        ssh_cmd_sudo(ip, f"ip link set {iface} mtu 9000 2>/dev/null")

    # Step 5: Load nvidia-peermem for GPU Direct RDMA
    print(f"  [5/7] Loading nvidia-peermem...")
    ssh_cmd_sudo(ip, "modprobe nvidia-peermem 2>/dev/null || true")
    ssh_cmd_sudo(ip, "bash -c 'echo nvidia-peermem >> /etc/modules-load.d/nvidia-peermem.conf'")

    # Step 6: Deploy NCCL environment
    print(f"  [6/7] Deploying NCCL environment config...")
    ssh_cmd(ip, f"cat >> ~/.profile << 'NCCLEOF'\n{NCCL_ENV_SWITCHED}NCCLEOF")

    # Step 7: Verify
    print(f"  [7/7] Verifying...")
    rc, out, _ = ssh_cmd(ip, "ibdev2netdev 2>/dev/null")
    print(f"    CX7 ports: {out}")
    rc, out, _ = ssh_cmd(ip, "nvidia-smi --query-gpu=name,memory.total --format=csv,noheader 2>/dev/null || echo 'GPU_CHECK_FAILED'")
    print(f"    GPU: {out}")
    rc, out, _ = ssh_cmd(ip, "lsmod | grep nvidia_peermem 2>/dev/null || echo 'peermem_not_loaded'")
    print(f"    nvidia-peermem: {out}")

    node.provisioned = True
    return node


def phase3_provision_all(nodes: list):
    """Post-provision all detected Sparks."""
    print("\n" + "=" * 60)
    print("PHASE 3: Post-Provisioning")
    print("=" * 60)
    print(f"  Provisioning {len(nodes)} new Sparks...")

    for node in nodes:
        provision_single_spark(node, nodes)

    provisioned = [n for n in nodes if n.provisioned]
    print(f"\n  Provisioned {len(provisioned)}/{len(nodes)} Sparks")
    return provisioned


# ============================================================
# Phase 4: Build NCCL Cluster
# ============================================================

def phase4_build_cluster(new_nodes: list):
    """Configure NCCL cluster across all Sparks."""
    print("\n" + "=" * 60)
    print("PHASE 4: Building NCCL Cluster")
    print("=" * 60)

    all_ips = []
    # Existing Spark (control node) CX7 IPs
    all_ips.append(f"{CX7_SUBNET}.10")  # gx10-acee
    for node in new_nodes:
        if node.cx7_ips:
            all_ips.append(node.cx7_ips.get("enp1s0f0np0", ""))

    # Create hostfile for MPI
    hostfile_lines = []
    hostfile_lines.append(f"{CX7_SUBNET}.10 slots=1")
    for node in new_nodes:
        if node.cx7_ips:
            hostfile_lines.append(f"{node.cx7_ips['enp1s0f0np0']} slots=1")

    hostfile_content = "\n".join(hostfile_lines)
    print(f"  MPI Hostfile ({len(hostfile_lines)} nodes):")
    for line in hostfile_lines:
        print(f"    {line}")

    # Deploy hostfile to all nodes
    for node in new_nodes:
        ssh_cmd(node.dhcp_ip, f"cat > ~/hostfile << 'EOF'\n{hostfile_content}\nEOF")

    # Deploy to control node too
    ssh_cmd(CONTROL_NODE, f"cat > ~/hostfile << 'EOF'\n{hostfile_content}\nEOF")

    # Verify cross-node connectivity
    print("\n  Verifying cross-node CX7 connectivity...")
    for node in new_nodes:
        if node.cx7_ips:
            target_ip = node.cx7_ips["enp1s0f0np0"]
            rc, out, _ = ssh_cmd(CONTROL_NODE, f"ping -c 1 -W 2 {target_ip} 2>/dev/null && echo OK || echo FAIL")
            status = "OK" if "OK" in out else "FAIL"
            print(f"    {CONTROL_NODE_BRIDGE_IP} -> {target_ip} ({node.hostname}): {status}")

    # Generate NCCL test command
    n_nodes = len(hostfile_lines)
    print(f"\n  NCCL Test Command ({n_nodes} nodes):")
    print(f"  mpirun -np {n_nodes} -hostfile ~/hostfile \\")
    print(f'    --mca plm_rsh_agent "ssh -o UserKnownHostsFile=/dev/null -o StrictHostKeyChecking=no" \\')
    print(f"    -x LD_LIBRARY_PATH=$LD_LIBRARY_PATH \\")
    print(f"    -x UCX_NET_DEVICES=enp1s0f0np0,enP2p1s0f1np1 \\")
    print(f"    -x NCCL_SOCKET_IFNAME=enp1s0f0np0,enP2p1s0f1np1 \\")
    print(f"    -x NCCL_SOCKET_FAMILY=AF_INET \\")
    print(f"    -x NCCL_IB_HCA=rocep1s0f0,roceP2p1s0f1 \\")
    print(f"    -x NCCL_IB_GID_INDEX=3 \\")
    print(f"    -x NCCL_IB_TC=3 \\")
    print(f"    -x NCCL_IB_MERGE_NICS=1 \\")
    print(f"    $HOME/nccl-tests/build/all_gather_perf -b 16G -e 16G -f 2")

    total_mem = (len(EXISTING_SPARKS) + len(new_nodes)) * SPARK_MEMORY_GB
    print(f"\n  Total unified memory target: {total_mem} GB")
    print(f"  Nodes: {len(EXISTING_SPARKS)} existing + {len(new_nodes)} new = {len(EXISTING_SPARKS) + len(new_nodes)}")


# ============================================================
# Summary and Export
# ============================================================

def export_cluster_state(new_nodes: list):
    """Export cluster state to JSON."""
    state = {
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "existing_sparks": {k: v for k, v in EXISTING_SPARKS.items()},
        "new_sparks": [],
        "total_memory_gb": (len(EXISTING_SPARKS) + len(new_nodes)) * SPARK_MEMORY_GB,
        "total_nodes": len(EXISTING_SPARKS) + len(new_nodes),
        "fabric": {
            "switch": "MikroTik CRS812-8DS-2DQ-2DDQ",
            "switch_ip": MIKROTIK_IP,
            "cx7_subnet1": f"{CX7_SUBNET}.0/24",
            "cx7_subnet2": f"{CX7_SUBNET2}.0/24",
            "protocol": "RoCE v2",
            "nccl_version": "2.28.3",
            "max_bandwidth_per_node_gbps": 200,
        },
        "nccl_env": {
            "NCCL_IB_HCA": "rocep1s0f0,roceP2p1s0f1",
            "NCCL_IB_GID_INDEX": 3,
            "NCCL_IB_TC": 3,
            "NCCL_IB_MERGE_NICS": 1,
            "NCCL_SOCKET_IFNAME": "enp1s0f0np0,enP2p1s0f1np1",
        },
    }
    for node in new_nodes:
        state["new_sparks"].append({
            "hostname": node.hostname,
            "dhcp_ip": node.dhcp_ip,
            "mac": node.mac,
            "cx7_ips": node.cx7_ips,
            "node_id": node.node_id,
            "provisioned": node.provisioned,
        })

    out_path = Path(__file__).parent / "cluster_state.json"
    with open(out_path, "w") as f:
        json.dump(state, f, indent=2)
    print(f"\n  Cluster state exported to {out_path}")
    return state


def print_summary(new_nodes: list):
    """Print final summary."""
    total = len(EXISTING_SPARKS) + len(new_nodes)
    total_mem = total * SPARK_MEMORY_GB
    provisioned = sum(1 for n in new_nodes if n.provisioned)

    print("\n" + "=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"  Existing Sparks: {len(EXISTING_SPARKS)}")
    for name, info in EXISTING_SPARKS.items():
        print(f"    {name}: {info['wifi_ip']} ({info['memory_gb']}GB)")
    print(f"  New Sparks: {len(new_nodes)} detected, {provisioned} provisioned")
    for node in new_nodes:
        status = "OK" if node.provisioned else "PENDING"
        print(f"    {node.hostname}: {node.dhcp_ip} [node {node.node_id}] ({status})")
        if node.cx7_ips:
            for iface, ip in node.cx7_ips.items():
                print(f"      {iface}: {ip}")
    print(f"  Total: {total} nodes, {total_mem} GB unified memory")
    print(f"  Fabric: CRS812 switch, RoCE v2, NCCL v2.28.3")
    print(f"  Max aggregate bandwidth: {total * 200} Gbps")
    print()
    print("  NEXT STEPS:")
    print("    1. Plug QSFP cables from CRS812 into each Spark's CX7 ports")
    print("    2. Verify CX7 links come up: ibdev2netdev (should show 'Up')")
    print("    3. Run NCCL all_gather_perf test (command printed above)")
    print("    4. Install NCCL v2.28.3 if not present:")
    print("       git clone https://github.com/NVIDIA/nccl.git && cd nccl && make -j src.build")
    print("    5. Build nccl-tests:")
    print("       git clone https://github.com/NVIDIA/nccl-tests.git && cd nccl-tests && make")


# ============================================================
# MikroTik Configuration Script (for manual execution)
# ============================================================

def generate_mikrotik_script():
    """Generate standalone MikroTik config script."""
    script = """#!/bin/bash
# MikroTik CRS812 Configuration for DGX Spark Provisioning
# Run these commands via MikroTik terminal (SSH, WebFig, or WinBox)
#
# Prerequisites:
#   - CRS812 accessible at 192.168.88.1
#   - gx10-acee connected to ether1 with IP 192.168.88.2

cat << 'MIKROTIK_COMMANDS'
# ============================================
# MikroTik CRS812 - DGX Spark Provisioning
# ============================================

# 1. Verify current state
/interface print
/ip address print

# 2. Add DHCP pool for new Sparks
/ip pool add name=spark-pool ranges=192.168.88.100-192.168.88.200

# 3. Configure DHCP network
/ip dhcp-server network add address=192.168.88.0/24 gateway=192.168.88.1 dns-server=8.8.8.8,8.8.4.4

# 4. Create DHCP server
/ip dhcp-server add name=spark-dhcp interface=bridge1 address-pool=spark-pool lease-time=1h disabled=no

# 5. Verify DHCP is running
/ip dhcp-server print

# 6. Monitor for new leases (watch this after powering on Sparks)
/ip dhcp-server lease print

# ============================================
# OPTIONAL: Enable internet access for first-boot updates
# Only needed if Sparks need to download updates during setup
# ============================================

# Check if NAT is needed (ether1 connects to upstream network)
# /ip firewall nat add chain=srcnat out-interface=ether1 action=masquerade

MIKROTIK_COMMANDS
"""
    out_path = Path(__file__).parent / "mikrotik_spark_config.sh"
    with open(out_path, "w") as f:
        f.write(script)
    os.chmod(out_path, 0o755)
    print(f"  MikroTik config script: {out_path}")
    return out_path


# ============================================================
# Main
# ============================================================

def main():
    parser = argparse.ArgumentParser(description="DGX Spark Fleet Provisioning")
    parser.add_argument("--phase", type=int, choices=[1, 2, 3, 4],
                       help="Run specific phase only")
    parser.add_argument("--manual", action="store_true",
                       help="Manually enter Spark IPs instead of auto-detection")
    parser.add_argument("--detect-timeout", type=int, default=30,
                       help="Minutes to wait for Spark detection (default: 30)")
    parser.add_argument("--generate-mikrotik", action="store_true",
                       help="Generate MikroTik config script and exit")
    parser.add_argument("--ips", nargs="+",
                       help="Directly specify new Spark IPs")
    args = parser.parse_args()

    if args.generate_mikrotik:
        generate_mikrotik_script()
        return

    print("DGX Spark Fleet Provisioning")
    print(f"Target: {len(EXISTING_SPARKS)} existing + {EXPECTED_NEW_SPARKS} new = {len(EXISTING_SPARKS) + EXPECTED_NEW_SPARKS} Sparks")
    print(f"Unified memory target: {(len(EXISTING_SPARKS) + EXPECTED_NEW_SPARKS) * SPARK_MEMORY_GB} GB")

    new_nodes = []

    if args.ips:
        # Direct IP specification
        for i, ip in enumerate(args.ips):
            rc, hostname, _ = ssh_cmd(ip, "hostname", timeout=10)
            node = SparkNode(
                hostname=hostname if rc == 0 else f"spark-unknown-{i}",
                dhcp_ip=ip,
                node_id=len(EXISTING_SPARKS) + i + 1
            )
            if rc == 0:
                rc2, mac, _ = ssh_cmd(ip, "cat /sys/class/net/enP7s7/address 2>/dev/null")
                if rc2 == 0:
                    node.mac = mac.strip()
            new_nodes.append(node)

    # Phase 1
    if not args.phase or args.phase == 1:
        phase1_configure_mikrotik()
        generate_mikrotik_script()

    # Phase 2
    if not args.phase or args.phase == 2:
        if not args.ips:
            if args.manual:
                new_nodes = phase2_manual_entry()
            else:
                new_nodes = phase2_detect_sparks(args.detect_timeout)

    # Phase 3
    if (not args.phase or args.phase == 3) and new_nodes:
        new_nodes = phase3_provision_all(new_nodes)

    # Phase 4
    if (not args.phase or args.phase == 4) and new_nodes:
        phase4_build_cluster(new_nodes)

    # Export and summarize
    if new_nodes:
        export_cluster_state(new_nodes)
        print_summary(new_nodes)
    else:
        print("\n  No new Sparks to provision.")
        print("  Run with --ips <ip1> <ip2> ... to provision specific IPs")
        print("  Or run with --manual to enter IPs interactively")
        print("  Or wait for auto-detection to find new DHCP leases")


if __name__ == "__main__":
    main()
