---
name: gotosocial-apple-container
description: Run a local ActivityPub server on macOS using Apple container CLI (not Docker/Colima). Load when setting up GoToSocial for single-instance or per-VM setups with LAN HTTP access.
---

# GoToSocial on Apple Container (macOS)

## Assumptions

- macOS host with Apple `container` CLI available
- No Docker/Colima
- LAN HTTP is acceptable (Tailscale/HTTPS optional)

## Setup

### 1) Prepare directories

```bash
mkdir -p ~/gotosocial/data ~/gotosocial/.cache
```

### 2) Start container services

```bash
container system start
```

### 3) Run GoToSocial (LAN HTTP)

Replace `ap-wyvern.local` with your chosen host. Ensure it resolves for all VMs.

```bash
container run -d --name gotosocial \
  --publish 0.0.0.0:8080:8080 \
  --env GTS_HOST=ap-wyvern.local \
  --env GTS_PROTOCOL=http \
  --env GTS_DB_TYPE=sqlite \
  --env GTS_DB_ADDRESS=/gotosocial/storage/sqlite.db \
  --env GTS_WAZERO_COMPILATION_CACHE=/gotosocial/.cache \
  --env GTS_LETSENCRYPT_ENABLED=false \
  --volume "$HOME/gotosocial/data:/gotosocial/storage" \
  --volume "$HOME/gotosocial/.cache:/gotosocial/.cache" \
  docker.io/superseriousbusiness/gotosocial:latest
```

### 4) Verify server

```bash
curl -i http://127.0.0.1:8080/
curl -i http://<LAN_IP>:8080/
```

### 5) Hostname resolution (VMs)

Add to `/etc/hosts` on macOS + each VM:

```bash
<LAN_IP> ap-wyvern.local
```

### 6) Create users

```bash
container exec gotosocial /gotosocial/gotosocial admin account create \
  --username green --email green@ap-wyvern.local --password '<PASSWORD>'

container exec gotosocial /gotosocial/gotosocial admin account promote \
  --username green

container exec gotosocial /gotosocial/gotosocial admin account create \
  --username blue --email blue@ap-wyvern.local --password '<PASSWORD>'
```

### 7) Login URL

```text
http://ap-wyvern.local:8080/login
```

## Notes

- If you change `GTS_HOST`, wipe the DB first: `rm -f ~/gotosocial/data/sqlite.db`
- Tailscale HTTPS can be layered later with `tailscale serve` if allowed on the tailnet

## Troubleshooting

```bash
container list
container logs gotosocial
container inspect gotosocial
```
