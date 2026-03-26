---
name: nhero-pyhole
description: DNS-style medication routing layer for nhero devices. Intercepts scheduling commands like Pi-hole intercepts DNS, routes through scramble index, enforces blocklist/allowlist per killdispenser signals.
version: 0.1.0
trit: 0
color: "#00FF00"
tags: [nhero, pyhole, dns, routing, medication, intercept, mitmproxy]
---

# nhero-pyhole

Pi-hole for pill dispensers. Intercept, filter, route.

## Architecture

```
Hero App → [mitmproxy] → nhero-pyhole → [scramble index] → Hero Cloud
                              ↓
                     killdispenser signals
                              ↓
                   [blocklist / allowlist]
                              ↓
                     DISPENSE or HOLD
```

## DNS Analogy

| Pi-hole | nhero-pyhole |
|---------|-------------|
| DNS query | Dispense command |
| Blocklist domain | Controlled substance slot |
| Allowlist domain | OTC supplement slot |
| Upstream DNS | Hero cloud API |
| Local DNS cache | Scramble index (letter → med) |
| CNAME record | Derangement mapping (q → Vyvanse) |
| Gravity list | Nurse approval queue |

## mitmproxy Integration

nhero-pyhole runs as a mitmproxy addon:
```bash
mitmproxy -s /Users/alice/worlds/h/hero_intercept.py --mode regular --listen-port 8080
```

Local IP for iOS proxy config: `172.20.12.94:8080`

## Scramble Resolution

```
query("q") → CNAME → "Vyvanse" → CHECK blocklist → HOLD (controlled)
query("x") → CNAME → "Magnesium" → CHECK allowlist → DISPENSE (OTC)
```

## Parent
Part of the [nhero](../nhero/SKILL.md) hierarchy.
