# Trifurcated Transfer Skill

Multi-channel P2P file transfer using LocalSend protocol across Tailscale, LAN, and DNS discovery.

## Quick Start

```clojure
;; Load peer configuration
(def peers (edn/read-string (slurp "peers.edn")))

;; Available channels: :tailscale, :lan, :dns
;; Max chunk size: 7MB (7340032 bytes)
```

## Peers

| Name | Tailscale IP | LAN | Trusted |
|------|-------------|-----|---------|
| 2-monad (self) | 100.87.209.11 | - | - |
| causality | 100.69.33.107 | 192.168.1.40 | ✓ |
| hatchery | 100.72.249.116 | - | - |

## Usage

1. Try Tailscale first (most reliable)
2. Fall back to LAN for local transfers
3. DNS discovery as last resort

Voice announcements use "Emma (Enhanced)".
