# network

Network tools = tailscale + curl + ssh + nmap.

## Atomic Skills

| Skill | Domain |
|-------|--------|
| tailscale | Mesh VPN |
| curl | HTTP client |
| ssh | Remote shell |
| nmap | Port scan |

## Tailscale

```bash
tailscale up
tailscale ssh hostname
tailscale serve http://localhost:8080
tailscale funnel 443
```

## SSH

```bash
ssh user@host
ssh -L 8080:localhost:80 host  # Local forward
ssh -R 8080:localhost:80 host  # Remote forward
ssh -D 1080 host               # SOCKS proxy
```

## Curl

```bash
curl -X POST -H "Content-Type: application/json" \
  -d '{"key":"value"}' https://api.example.com

curl -O https://example.com/file.zip
```

## Discovery

```bash
nmap -sn 192.168.1.0/24
tailscale status --json | jq '.Peer | keys'
```
