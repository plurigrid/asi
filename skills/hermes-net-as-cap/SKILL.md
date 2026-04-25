---
name: hermes-net-as-cap
description: Replace Hermes' SSRF blocklist (resolve-then-connect with documented DNS-rebinding TOCTOU) with a Goblins network capability — a host-allowlist forwarder that mediates every connection at the socket layer. Connection-time validation by construction, not best-effort pre-flight.
type: bridge
parent: hermes-goblins-bridge
row: 17
proto: R
polarity: -1
status: stub
---

# hermes-net-as-cap

Phase 1. Closes the SSRF surface that Hermes' own docs flag as not-fixable-at-the-pre-flight-level (DNS rebinding, redirect bypass).

## Hermes signature

`/Users/bob/i/hermes-agent/tools/url_safety.py`

```python
def is_safe_url(url: str) -> bool:
    # urlparse → resolve hostname → reject if IP is private/loopback/CGNAT/multicast
    # Documented limits: DNS rebinding TOCTOU, redirect chains
def _is_blocked_ip(ip): ...    # private/loopback/link-local/reserved/multicast/CGNAT
```

`/Users/bob/i/hermes-agent/tools/website_policy.py` — host allow/deny lists per skill.

Used by: vision_tools, gateway adapters (telegram/whatsapp/qq), media cache, web tools (Firecrawl/Tavily). Each call site re-validates on each redirect via httpx event hooks. Authority pattern: **resolve-then-connect** — the resolve and the connect are separate syscalls; an attacker's DNS server can return different answers.

## Goblins signature

`/Users/bob/i/goblins-adapter/` — a `^net-cap` actor parameterised by a host-allowlist (or single-host attenuation), exposing `get`, `post`, `stream`. Validation happens inside the vat at socket-open time, not at URL-parse time.

```scheme
(define (^net-cap bcom allowlist)
  (methods
    ((get  url . headers)  (mediated-fetch 'GET  url headers))
    ((post url body . hd)  (mediated-fetch 'POST url body hd))
    ((subhost host)
     (if (member host allowlist)
         (spawn ^net-cap (list host))    ; attenuated single-host cap
         (raise 'cap-error)))))
```

`mediated-fetch` resolves and connects in one syscall (or via an egress proxy holding the only public-internet socket), so DNS rebinding cannot split them.

## Translation table

| Hermes call | Goblins message | Notes |
|---|---|---|
| `httpx.get(url)` | `(<- net-cap 'get url)` | cap mediates the connect |
| `is_safe_url(url) → connect` | `(<- net-cap 'get url)` | check folded into call — no TOCTOU |
| redirect via httpx event hook | `(<- net-cap 'follow-redirect new-url)` | cap re-validates each hop, refuses if outside allowlist |
| skill-scoped allowlist | `(<- net-cap 'subhost "api.openai.com")` | single-host attenuated forwarder |

## Failure modes (closed by this bridge)

- **DNS rebinding TOCTOU** — Hermes resolves, then connects; cap collapses the two into one mediated op (or routes through a single egress proxy that holds the only public socket).
- **Redirect chain to internal host** — every hop is a fresh `<-` call; cap re-checks containment at each hop, not just at request entry.
- **Forgotten `is_safe_url` callsite** — there is no raw `httpx.get`; if no cap, no call.
- **Skill exfiltrating data via attacker-controlled hostname** — cap's allowlist is parameterised at construction; the skill cannot widen it from inside.

## Failure modes (introduced; must mitigate)

- **Cap leakage to LLM context** — same Mandy nonce-registry remedy as fs-cap (Pattern B in parent SKILL): `/object/<base32-id>` URL handle, raw cap stays vat-side.
- **Allowlist ossification** — when a skill legitimately needs a new host, route through user-approval cap (`hermes-approval-as-revocable`, row 15) rather than re-deploying the agent.

## Test vector

```python
# Must reject:
net.get("http://169.254.169.254/latest/meta-data/")   # AWS metadata → CapError
net.get("http://localhost:8080/admin")                # loopback → CapError
net.get("http://attacker.com")  # where DNS later resolves to 127.0.0.1
                                # → CapError at connect time, not just at parse time
# Redirect-chain attack:
net.get("https://allowed.example/redirect-to-localhost")
# → CapError on the redirect hop, not silently followed

# Must accept:
sub = net.subhost("api.openai.com")
sub.post("https://api.openai.com/v1/chat/completions", body)   # OK
sub.get("https://elsewhere.example/")                          # CapError (sub is attenuated)
```

## Capability diff

| Property | Hermes (status quo) | Goblins (this bridge) |
|---|---|---|
| Authority source | ambient socket() | explicit cap reference |
| Validation time | URL-parse (TOCTOU) | socket-open / per-hop |
| Revocation | restart process | drop forwarder |
| Attenuation | new allowlist policy + audit | `subhost` returns scoped cap |
| Redirect handling | best-effort hooks | mediated by construction |
| Failure mode | forgotten check or DNS race = silent egress | no cap = no socket |

## Test-harness location

`~/i/goblins-adapter/tests/net-cap-bisim.scm` (todo) — bisim against Python entrypoint shim. Crucial probe: simulated DNS-rebinding adversary should pass-then-fail Hermes but always-fail the cap.

## Status: stub

Phase 1 priority. Pairs naturally with `hermes-fs-as-cap` (row 16) — together they close the two largest ambient-authority surfaces. Egress-proxy variant (Smokescreen-shaped) optional but recommended for defense-in-depth.
