#!/bin/bash
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
