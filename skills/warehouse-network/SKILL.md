---
name: warehouse-network
description: Connect to warehouse machines (DGX Spark, etc.) via local network or Tailscale. Use when SSH-ing into warehouse hosts, managing Tailscale connectivity, or accessing gx10-acee.
---

# Warehouse Network

Manage SSH connections to machines on the warehouse network, with Tailscale as the cross-network fallback.

## Hosts

| Host | Local IP | Tailscale IP | User | Password |
|------|----------|-------------|------|----------|
| gx10-acee (DGX Spark) | 10.1.10.153 | 100.74.215.96 | a | aaaaaa |

## Connection Strategy

1. **Same network**: SSH directly via local IP (`10.1.10.x`)
2. **Different networks**: SSH via Tailscale IP (`100.x.x.x`)
3. **If Tailscale is offline/expired**: Must access via local network first, then run `sudo tailscale up --force-reauth`

## Quick Connect

```bash
# Try Tailscale first (works across networks)
ssh a@100.74.215.96

# Fall back to local
ssh a@10.1.10.153
```

## Connection Workflow

```bash
# 1. Check if host is on Tailscale
tailscale status | grep gx10

# 2. If online (no "offline" tag), ping to verify
tailscale ping --timeout=10s gx10-acee

# 3. If offline or node key expired, SSH via local network and re-auth
ssh a@10.1.10.153
sudo tailscale up --force-reauth
# Visit the printed auth URL in browser

# 4. Connect via Tailscale once authenticated
ssh a@100.74.215.96
```

## Discovering New Hosts

If a host IP is uncertain, probe a range:

```bash
for ip in 10.1.10.{150..155}; do
  ssh -o ConnectTimeout=5 -o BatchMode=yes a@$ip "echo $ip ok" 2>&1 &
done; wait
```

## Notes

- DGX Spark runs Ubuntu (aarch64), NVIDIA DGX Spark Version 7.4.0
- The machine has a `(spark-ai-env)` conda/venv activated by default
- Tailscale node keys can expire; re-auth with `--force-reauth`
- sudo password is the same as the login password
