---
name: ukraine
description: Mullvad VPN + jurisdiction routing for DeFi access. Use when planning trading setups that need specific geo-IP, checking DEX restricted countries, or configuring Mullvad exits.
---

# MuVault — Mullvad + Jurisdiction Routing

Route trading access through Mullvad VPN exits to non-restricted jurisdictions.

## Mullvad Ukraine Servers

| IP | Location | Provider | Network |
|----|----------|----------|---------|
| 149.102.240.66 | Kyiv | DataCamp | AS212238 |

Mullvad runs WireGuard and OpenVPN servers in Kyiv. All rented dedicated (not virtual), physically located where listed.

Check current server list: `https://mullvad.net/en/help/server-list` (filter by country: Ukraine)

## Ostium DEX Jurisdiction Map

**Restricted (BLOCKED):**
- United States
- Iran, Syria, Cuba, North Korea
- Crimea, Donetsk, Luhansk (Ukraine occupied territories)
- Any jurisdiction under comprehensive US economic sanctions

**Allowed:** Everything else. No whitelist — just the blacklist above.

**Key facts:**
- No KYC, connect via Web3 wallet or email
- Built on Arbitrum, 31+ markets, up to 200x leverage
- VPN circumvention explicitly prohibited in ToS for restricted persons
- Chernivtsi, Kyiv, Lviv, Odesa — all clean Ukrainian cities (not restricted regions)

## Setup Checklist

```
- [ ] Mullvad account (anonymous, pay with crypto)
- [ ] WireGuard config for ua-kyv exit
- [ ] Verify IP: curl -s https://am.i.mullvad.net/json | jq '.ip, .country'
- [ ] Arbitrum wallet funded (bridge from L1 or CEX withdraw to Arbitrum)
- [ ] Connect to app.ostium.com, verify no geo-block
```

## iMac IES Setup (Tailscale)

| Field | Value |
|-------|-------|
| Hostname | iess-imac |
| Tailscale IP | 100.107.8.33 |
| User | ies |
| Status | Check: `tailscale status \| grep imac` |

SSH: `ssh ies@100.107.8.33`

## XBOW Resilience Notes

When caching macOS security updates on trading infrastructure:
- **Tier 1** (no web surface): Apple Content Caching, Reposado
- **Tier 2** (managed surface): Jamf DDM Blueprints
- **Tier 3** (large surface): JFrog Artifactory

Principle: dumb caches + Apple crypto signatures beat smart dashboards against autonomous AI pentesters.

## Other DEX Jurisdiction Patterns

When checking any DEX, look for:
1. Terms of Use → "Restricted Person" definition
2. Usually: US + OFAC sanctioned countries + specific conflict zones
3. Most Arbitrum/Base DEXs follow similar patterns to Ostium
4. DeFiLlama for volume/TVL comparison: `https://defillama.com/protocol/ostium`
