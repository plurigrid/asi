---
name: network-forensics
description: Analyze network traffic captures for security incidents, protocol anomalies, and data exfiltration. Uses tcpdump, tshark/Wireshark, Zeek, and ngrep for packet-level forensics in authorized testing environments.
---

# Network Forensics

## When to Use

Use when auditing network traffic, investigating incidents, analyzing protocol behavior, or reviewing packet captures from authorized security assessments.

## Tool Reference

| Tool | Package | Purpose |
|------|---------|---------|
| `tcpdump` | system | Live capture, BPF filtering |
| `tshark` | wireshark | CLI dissection, field extraction |
| `editcap` | wireshark | Split/merge/trim pcaps |
| `mergecap` | wireshark | Combine capture files |
| `ngrep` | ngrep | Regex pattern matching on packets |
| `zeek` | zeek | Protocol logging, script analysis |
| `suricata` | suricata | IDS/IPS rule matching |
| `termshark` | termshark | TUI packet browser |
| `scapy` | pip:scapy | Python packet crafting/parsing |
| `netflow` | nfdump | Flow record analysis |

## Methodology

### 1. Capture

```bash
# Capture with rotation (100MB files, keep 10)
tcpdump -i eth0 -w capture-%Y%m%d%H%M.pcap -C 100 -W 10 -Z root

# Capture specific traffic
tcpdump -i any 'port 443 and host 10.0.0.1' -w tls_traffic.pcap

# Ring buffer capture (continuous, overwrite oldest)
tcpdump -i eth0 -w ring.pcap -C 50 -W 20
```

### 2. Triage

```bash
# Protocol hierarchy
tshark -r capture.pcap -qz io,phs

# Conversation summary
tshark -r capture.pcap -qz conv,tcp

# Endpoint statistics
tshark -r capture.pcap -qz endpoints,ip

# HTTP requests overview
tshark -r capture.pcap -Y http.request -T fields \
  -e frame.time -e ip.src -e http.host -e http.request.uri
```

### 3. Deep Inspection

```bash
# Extract DNS queries
tshark -r capture.pcap -Y dns.qr==0 -T fields \
  -e frame.time -e ip.src -e dns.qry.name -e dns.qry.type

# TLS handshake analysis (SNI, ciphers, JA3)
tshark -r capture.pcap -Y 'tls.handshake.type==1' -T fields \
  -e ip.src -e ip.dst -e tls.handshake.extensions_server_name \
  -e ja3.hash

# Find cleartext credentials
ngrep -q -I capture.pcap 'pass|user|login|auth' 'port 80 or port 21 or port 25'

# Extract files from HTTP streams
tshark -r capture.pcap --export-objects http,exported_files/
```

### 4. Anomaly Detection

```bash
# DNS tunneling indicators (long queries, high frequency)
tshark -r capture.pcap -Y 'dns.qry.name.len > 50' -T fields \
  -e ip.src -e dns.qry.name | sort | uniq -c | sort -rn

# Beaconing detection (regular intervals)
tshark -r capture.pcap -Y 'ip.dst==suspicious.ip' -T fields \
  -e frame.time_epoch | awk '{if(NR>1) print $1-prev; prev=$1}'

# Large outbound transfers (exfiltration)
tshark -r capture.pcap -qz conv,tcp | sort -k8 -rn | head -20

# Non-standard port usage
tshark -r capture.pcap -Y 'tcp.port > 1024 and not ssl' \
  -qz io,stat,60,"COUNT(tcp.port)tcp.port"
```

### 5. Zeek Log Analysis

```bash
# Process pcap with Zeek
zeek -r capture.pcap local

# Unusual user agents
cat http.log | zeek-cut user_agent | sort | uniq -c | sort -rn | head

# Long connections (C2 indicators)
cat conn.log | zeek-cut duration id.orig_h id.resp_h id.resp_p | \
  awk '$1 > 3600' | sort -rn

# DNS query frequency per host
cat dns.log | zeek-cut id.orig_h query | sort | uniq -c | sort -rn

# File extraction from Zeek
ls extract_files/  # Zeek auto-extracts transferred files
```

## Code Review Patterns

### Insecure Protocol Usage
```python
# FINDING: Cleartext protocol in use
# LOOK FOR: socket connections without TLS wrapper
sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
sock.connect((host, 80))  # No TLS
sock.send(credentials.encode())  # Cleartext creds on wire
```

### DNS Exfiltration Surface
```python
# FINDING: User-controlled data in DNS queries enables exfiltration
query = f"{user_data}.example.com"  # Data encoded in subdomain
resolver.resolve(query, 'A')
```

### Missing Certificate Validation
```python
# FINDING: TLS verification disabled
requests.get(url, verify=False)  # Accepts any cert
ssl_context = ssl.create_default_context()
ssl_context.check_hostname = False  # MitM possible
```

## Scapy Recipes

```python
from scapy.all import *

# Read and filter pcap
pkts = rdpcap("capture.pcap")
dns_pkts = [p for p in pkts if p.haslayer(DNS)]

# Extract unique destination IPs
dsts = set(p[IP].dst for p in pkts if p.haslayer(IP))

# Reassemble TCP streams
sessions = pkts.sessions()
for session_id, session_pkts in sessions.items():
    payload = b"".join(bytes(p[TCP].payload) for p in session_pkts if p.haslayer(TCP))
```

## Output Format

```markdown
## Network Forensics Report

### Capture Summary
- **File**: capture.pcap (SIZE, DURATION)
- **Packets**: N total, N protocols
- **Time range**: START — END

### Findings

#### [SEVERITY] Finding Title
- **Evidence**: packet numbers, timestamps
- **Indicator**: what was observed
- **Impact**: security implication
- **Recommendation**: remediation

### IOCs Extracted
| Type | Value | Context |
|------|-------|---------|
| IP | x.x.x.x | C2 server |
| Domain | evil.com | DNS tunnel |
| JA3 | hash | Malware TLS fingerprint |
```

## 2600 Heritage

Network packet analysis has been a core 2600 topic since the magazine's founding — from early TCP/IP stack fingerprinting articles to modern TLS interception techniques. The 2600 community pioneered accessible network forensics tools and techniques that are now industry standard.
