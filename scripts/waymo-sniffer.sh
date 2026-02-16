#!/usr/bin/env bash
# waymo-sniffer.sh — Embarrassingly parallel Waymo network recon
# Detects: devices traveling with us vs passing Waymos
# SSID signature: __operad
set -euo pipefail

OUT_DIR="/tmp/waymo-sniffer"
mkdir -p "$OUT_DIR"
PIDS=()
OUR_SSID="__operad"
OUR_IP=$(ifconfig en0 | grep "inet " | awk '{print $2}')
OUR_MAC=$(ifconfig en0 | grep ether | awk '{print $2}')
GATEWAY=$(netstat -rn | grep "^default.*en0" | head -1 | awk '{print $2}')
DURATION="${1:-30}"  # default 30 seconds, override with arg

cleanup() {
    echo ""
    echo "=== STOPPING ALL PROBES ==="
    for pid in "${PIDS[@]}"; do
        kill "$pid" 2>/dev/null || true
    done
    wait 2>/dev/null
    echo "=== ANALYSIS ==="
    analyze
}
trap cleanup INT TERM

log() { echo "[$(date +%H:%M:%S)] $1"; }

# ─── PROBE 1: ARP new devices ───
probe_arp() {
    tshark -i en0 -a "duration:$DURATION" -f "arp" \
        -T fields -e frame.time_relative -e arp.src.hw_mac -e arp.src.proto_ipv4 \
        -e arp.dst.hw_mac -e arp.dst.proto_ipv4 \
        > "$OUT_DIR/probe_arp.tsv" 2>/dev/null
}

# ─── PROBE 2: mDNS/Bonjour service discovery ───
probe_mdns() {
    tshark -i en0 -a "duration:$DURATION" -f "udp port 5353" \
        -T fields -e ip.src -e dns.qry.name -e dns.resp.name \
        -e dns.a -e dns.ptr.domain_name -e dns.srv.name \
        > "$OUT_DIR/probe_mdns.tsv" 2>/dev/null
}

# ─── PROBE 3: DNS queries (waymo/google patterns) ───
probe_dns() {
    tshark -i en0 -a "duration:$DURATION" -f "udp port 53" \
        -T fields -e frame.time_relative -e ip.src -e ip.dst \
        -e dns.qry.name -e dns.a -e dns.flags.response \
        > "$OUT_DIR/probe_dns.tsv" 2>/dev/null
}

# ─── PROBE 4: TLS SNI (Server Name Indication) ───
probe_tls_sni() {
    tshark -i en0 -a "duration:$DURATION" -f "tcp port 443" \
        -Y "tls.handshake.extensions_server_name" \
        -T fields -e ip.src -e ip.dst -e tls.handshake.extensions_server_name \
        > "$OUT_DIR/probe_tls_sni.tsv" 2>/dev/null
}

# ─── PROBE 5: IPv6 Neighbor Discovery ───
probe_ndp() {
    tshark -i en0 -a "duration:$DURATION" -f "icmp6" \
        -T fields -e frame.time_relative -e eth.src -e eth.dst \
        -e ipv6.src -e ipv6.dst -e _ws.col.Info \
        > "$OUT_DIR/probe_ndp.tsv" 2>/dev/null
}

# ─── PROBE 6: All broadcast/multicast ───
probe_broadcast() {
    tshark -i en0 -a "duration:$DURATION" -f "broadcast or multicast" \
        -T fields -e frame.time_relative -e eth.src -e eth.dst \
        -e ip.src -e ip.dst -e _ws.col.Protocol -e _ws.col.Info \
        > "$OUT_DIR/probe_broadcast.tsv" 2>/dev/null
}

# ─── PROBE 7: DHCP traffic (device hostnames) ───
probe_dhcp() {
    tshark -i en0 -a "duration:$DURATION" -f "udp port 67 or udp port 68" \
        -T fields -e frame.time_relative -e eth.src -e dhcp.hw.mac_addr \
        -e dhcp.option.hostname -e dhcp.option.vendor_class_id \
        -e dhcp.option.requested_ip_address \
        > "$OUT_DIR/probe_dhcp.tsv" 2>/dev/null
}

# ─── PROBE 8: WiFi scan loop (detect passing __operad SSIDs) ───
probe_wifi_scan() {
    local end_time=$((SECONDS + DURATION))
    > "$OUT_DIR/probe_wifi_scan.log"
    while [ $SECONDS -lt $end_time ]; do
        swift -e '
import CoreWLAN
import Foundation
let ts = ISO8601DateFormatter().string(from: Date())
if let iface = CWWiFiClient.shared().interface() {
    if let networks = try? iface.scanForNetworks(withName: nil) {
        for n in networks {
            let ssid = n.ssid ?? "<hidden>"
            let bssid = n.bssid ?? "?"
            let rssi = n.rssiValue
            let ch = n.wlanChannel?.channelNumber ?? 0
            print("\(ts)\t\(ssid)\t\(bssid)\t\(rssi)\t\(ch)")
        }
    }
}
' >> "$OUT_DIR/probe_wifi_scan.log" 2>/dev/null
        sleep 5
    done
}

# ─── PROBE 9: SSDP/UPnP discovery ───
probe_ssdp() {
    tshark -i en0 -a "duration:$DURATION" -f "udp port 1900" \
        -T fields -e ip.src -e http.server -e http.user_agent \
        -e _ws.col.Info \
        > "$OUT_DIR/probe_ssdp.tsv" 2>/dev/null
}

# ─── PROBE 10: Full packet stats (conversation summary) ───
probe_conversations() {
    tshark -i en0 -a "duration:$DURATION" -q -z conv,ip \
        > "$OUT_DIR/probe_conversations.txt" 2>/dev/null
}

# ─── PROBE 11: AWDL (Apple Wireless Direct Link) ───
probe_awdl() {
    tshark -i awdl0 -a "duration:$DURATION" \
        -T fields -e frame.time_relative -e eth.src -e eth.dst \
        -e ip.src -e ip.dst -e _ws.col.Protocol -e _ws.col.Info \
        > "$OUT_DIR/probe_awdl.tsv" 2>/dev/null || true
}

# ─── ANALYSIS ───
analyze() {
    echo ""
    echo "╔══════════════════════════════════════════════════╗"
    echo "║         WAYMO NETWORK RECON RESULTS             ║"
    echo "╠══════════════════════════════════════════════════╣"
    echo "║ Our SSID: $OUR_SSID"
    echo "║ Our IP:   $OUR_IP  MAC: $OUR_MAC"
    echo "║ Gateway:  $GATEWAY"
    echo "║ Duration: ${DURATION}s"
    echo "╚══════════════════════════════════════════════════╝"

    echo ""
    echo "── 1. DEVICES ON OUR NETWORK (traveling with us) ──"
    # Unique MACs from ARP
    if [ -s "$OUT_DIR/probe_arp.tsv" ]; then
        echo "  ARP-discovered MACs:"
        awk -F'\t' '{print $2, $3}' "$OUT_DIR/probe_arp.tsv" | sort -u | while read mac ip; do
            [ -z "$mac" ] && continue
            if [ "$mac" = "$OUR_MAC" ]; then
                echo "    $ip  $mac  ← US (causality)"
            elif [ "$ip" = "$GATEWAY" ]; then
                echo "    $ip  $mac  ← WAYMO AP/GATEWAY"
            else
                echo "    $ip  $mac  ← UNKNOWN DEVICE"
            fi
        done
    fi
    # Also from current ARP table
    echo "  Current ARP table:"
    arp -a | grep -v incomplete | grep "en0" | while read line; do
        echo "    $line"
    done

    echo ""
    echo "── 2. mDNS SERVICE ADVERTISEMENTS ──"
    if [ -s "$OUT_DIR/probe_mdns.tsv" ]; then
        awk -F'\t' 'NF>1{print $1, $5}' "$OUT_DIR/probe_mdns.tsv" | sort -u | head -20
    else
        echo "  (no mDNS traffic captured)"
    fi

    echo ""
    echo "── 3. DNS QUERIES (waymo/google patterns) ──"
    if [ -s "$OUT_DIR/probe_dns.tsv" ]; then
        echo "  Waymo/Google domains:"
        grep -iE "waymo|google|goog|gstatic|android|chromeos" "$OUT_DIR/probe_dns.tsv" | \
            awk -F'\t' '{print $2, "→", $4}' | sort -u | head -20
        echo "  All queried domains (top 20):"
        awk -F'\t' '$4!=""{print $4}' "$OUT_DIR/probe_dns.tsv" | sort | uniq -c | sort -rn | head -20
    else
        echo "  (no DNS traffic captured)"
    fi

    echo ""
    echo "── 4. TLS SNI (encrypted connections) ──"
    if [ -s "$OUT_DIR/probe_tls_sni.tsv" ]; then
        echo "  Waymo/Google SNIs:"
        grep -iE "waymo|google|goog|gstatic|android" "$OUT_DIR/probe_tls_sni.tsv" | \
            awk -F'\t' '{print $1, "→", $3}' | sort -u | head -20
        echo "  All SNIs (top 20):"
        awk -F'\t' '$3!=""{print $3}' "$OUT_DIR/probe_tls_sni.tsv" | sort | uniq -c | sort -rn | head -20
    else
        echo "  (no TLS SNI captured)"
    fi

    echo ""
    echo "── 5. PASSING WAYMOS (__operad SSIDs) ──"
    if [ -s "$OUT_DIR/probe_wifi_scan.log" ]; then
        local operad_count=$(grep -c "__operad" "$OUT_DIR/probe_wifi_scan.log" 2>/dev/null || echo 0)
        echo "  Total __operad sightings: $operad_count"
        echo "  Unique __operad instances:"
        grep "__operad" "$OUT_DIR/probe_wifi_scan.log" | \
            awk -F'\t' '{print $2, "BSSID:"$3, "RSSI:"$4, "Ch:"$5}' | sort -u
        # Count unique channels — different channels likely = different vehicles
        echo "  Unique channels with __operad:"
        grep "__operad" "$OUT_DIR/probe_wifi_scan.log" | \
            awk -F'\t' '{print $5}' | sort -u
        local unique_channels=$(grep "__operad" "$OUT_DIR/probe_wifi_scan.log" | awk -F'\t' '{print $5}' | sort -u | wc -l)
        # Our vehicle is on ch161 (5GHz) + ch2 (2.4GHz) = 2 channels
        if [ "$unique_channels" -gt 2 ]; then
            echo ""
            echo "  ⚠️  ALERT: Detected __operad on $unique_channels channels!"
            echo "  ⚠️  Likely $(( (unique_channels + 1) / 2 )) Waymo vehicles nearby!"
            # Show non-our channels
            echo "  Other Waymos (not our ch161/ch2):"
            grep "__operad" "$OUT_DIR/probe_wifi_scan.log" | \
                awk -F'\t' '$5!=161 && $5!=2 {print "    Ch:"$5, "RSSI:"$4, "BSSID:"$3, "at", $1}' | sort -u
        else
            echo "  ✓ Only our Waymo detected (ch161 + ch2 dual-band)"
        fi
    else
        echo "  (no WiFi scans completed)"
    fi

    echo ""
    echo "── 6. IPv6 NEIGHBOR DISCOVERY ──"
    if [ -s "$OUT_DIR/probe_ndp.tsv" ]; then
        awk -F'\t' '{print $2, $4, $6}' "$OUT_DIR/probe_ndp.tsv" | sort -u | head -10
    else
        echo "  (no NDP traffic)"
    fi

    echo ""
    echo "── 7. IP CONVERSATIONS ──"
    if [ -s "$OUT_DIR/probe_conversations.txt" ]; then
        # Show non-our-IP conversations (Waymo internal traffic)
        grep -v "^=\|^$\|Filter\|Conversations" "$OUT_DIR/probe_conversations.txt" | \
            grep -v "$OUR_IP" | head -10
        echo "  ---"
        echo "  Our traffic summary:"
        grep "$OUR_IP" "$OUT_DIR/probe_conversations.txt" | head -10
    fi

    echo ""
    echo "── 8. AWDL (Apple peer-to-peer) ──"
    if [ -s "$OUT_DIR/probe_awdl.tsv" ]; then
        wc -l < "$OUT_DIR/probe_awdl.tsv" | xargs echo "  Packets:"
        awk -F'\t' '{print $6}' "$OUT_DIR/probe_awdl.tsv" | sort | uniq -c | sort -rn | head -5
    else
        echo "  (no AWDL traffic)"
    fi

    echo ""
    echo "── 9. DEVICE CLASSIFICATION ──"
    echo "  OUR DEVICES (traveling with us):"
    echo "    $OUR_IP  $OUR_MAC  causality (MacBook)"
    arp -a | grep -v incomplete | grep "en0" | while read line; do
        ip=$(echo "$line" | grep -oE '\([0-9.]+\)' | tr -d '()')
        mac=$(echo "$line" | grep -oE '([0-9a-f]{1,2}:){5}[0-9a-f]{1,2}')
        [ "$ip" = "$GATEWAY" ] && echo "    $ip  $mac  WAYMO VEHICLE AP (gateway)" && continue
        [ "$ip" = "$OUR_IP" ] && continue
        # Check if LA bit set (locally administered = randomized MAC)
        first_byte=$(echo "$mac" | cut -d: -f1)
        la_bit=$(( 0x$first_byte & 0x02 ))
        if [ "$la_bit" -ne 0 ]; then
            echo "    $ip  $mac  UNKNOWN (randomized MAC)"
        else
            # OUI lookup
            oui=$(echo "$mac" | tr -d ':' | cut -c1-6 | tr '[:lower:]' '[:upper:]')
            vendor=$(grep -i "^$oui" /Users/bob/i/asi/docs/oui/wireshark_manuf.txt 2>/dev/null | head -1 | awk '{print $2}' || echo "?")
            echo "    $ip  $mac  $vendor"
        fi
    done

    echo ""
    echo "── SERIALIZED ──"
    echo "  Raw data: $OUT_DIR/"
    ls -la "$OUT_DIR/" | grep -v "^total\|^d"
}

# ─── LAUNCH ALL PROBES IN PARALLEL ───
log "Starting embarrassingly parallel Waymo sniffer (${DURATION}s)"
log "SSID: $OUR_SSID | IP: $OUR_IP | GW: $GATEWAY"
echo ""

log "Launching probe  1/11: ARP monitor"
probe_arp &
PIDS+=($!)

log "Launching probe  2/11: mDNS/Bonjour"
probe_mdns &
PIDS+=($!)

log "Launching probe  3/11: DNS queries"
probe_dns &
PIDS+=($!)

log "Launching probe  4/11: TLS SNI extraction"
probe_tls_sni &
PIDS+=($!)

log "Launching probe  5/11: IPv6 NDP"
probe_ndp &
PIDS+=($!)

log "Launching probe  6/11: Broadcast/multicast"
probe_broadcast &
PIDS+=($!)

log "Launching probe  7/11: DHCP hostnames"
probe_dhcp &
PIDS+=($!)

log "Launching probe  8/11: WiFi scan loop (__operad detector)"
probe_wifi_scan &
PIDS+=($!)

log "Launching probe  9/11: SSDP/UPnP"
probe_ssdp &
PIDS+=($!)

log "Launching probe 10/11: IP conversations"
probe_conversations &
PIDS+=($!)

log "Launching probe 11/11: AWDL sniff"
probe_awdl &
PIDS+=($!)

echo ""
log "All 11 probes running. Waiting ${DURATION}s..."
log "Press Ctrl-C to stop early and see results."
echo ""

# Wait for all probes
for pid in "${PIDS[@]}"; do
    wait "$pid" 2>/dev/null || true
done

analyze
