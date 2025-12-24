# LocalSend Skill Continuation State

**Timestamp**: 2025-12-22T03:36:00Z
**Thread**: T-019b4405-2a14-7207-af89-748a784371d5
**Gist**: https://gist.github.com/bmorphism/331f78891d4e439616a19705d5467579

---

## CRITICAL STATE (Copy to Next Context)

```clojure
{:receiver {:status :ADVERTISING
            :pid 79949
            :port 53317
            :bind "0.0.0.0"
            :alias "causality"
            :fingerprint "27abcf48"}
 
 :self {:name "causality"
        :tailscale-ip "100.69.33.107"
        :tailscale-dns "causality.pirate-dragon.ts.net"
        :lan-ip "192.168.1.40"
        :lan-blocked true  ;; macOS firewall State=2
        :color "#117465"}
 
 :peer {:name "2-monad"
        :tailscale-ip "100.87.209.11"
        :lan-ip "192.168.1.44"
        :status :active
        :rtt-ms 15
        :color "#83D88F"
        :session-id "sess_1766374506685_x9hkcz"}
 
 :files-received [{:name "f1_1766373686054.bin" :size 67 :time "22:21"}
                  {:name "test_send.txt" :size 71 :time "22:17"}]
 
 :waiting-for :incoming-transfer
 :voice "Emma (Premium)"
 :channels [:tailscale :nats :voice]}
```

---

## STATE MACHINE (Maximally Redundant)

```
╔═══════════════════════════════════════════════════════════════════════════╗
║                         LOCALSEND P2P STATE MACHINE                        ║
╠═══════════════════════════════════════════════════════════════════════════╣
║                                                                            ║
║   ┌────────────────────────────────────────────────────────────────────┐  ║
║   │                           IDLE                                      │  ║
║   │  • No active session                                               │  ║
║   │  • Receiver may or may not be running                              │  ║
║   │  • Entry: on startup, after COMPLETE, after FAILED+reset           │  ║
║   └────────────────────────────────────────────────────────────────────┘  ║
║          │                                    │                            ║
║          │ advertise()                        │ discover()                 ║
║          ▼                                    ▼                            ║
║   ┌─────────────────────┐            ┌─────────────────────┐              ║
║   │    ADVERTISING      │            │    DISCOVERING      │              ║
║   ├─────────────────────┤            ├─────────────────────┤              ║
║   │ • Start HTTP server │            │ • Query Tailscale   │              ║
║   │ • Bind 0.0.0.0:53317│            │ • Scan multicast    │              ║
║   │ • Voice announce    │            │ • Check NATS        │              ║
║   │ • Multicast beacon  │            │ • List peers        │              ║
║   │ • NATS publish caps │            │                     │              ║
║   └─────────────────────┘            └─────────────────────┘              ║
║          │                                    │                            ║
║          │ peer_connects()                    │ select_peer()              ║
║          ▼                                    ▼                            ║
║   ┌────────────────────────────────────────────────────────────────────┐  ║
║   │                         NEGOTIATING                                 │  ║
║   ├────────────────────────────────────────────────────────────────────┤  ║
║   │  • Exchange capabilities                                           │  ║
║   │  • Agree on transport (Tailscale > LAN > NATS relay)              │  ║
║   │  • Set chunk size, parallelism                                     │  ║
║   │  • Create session ID                                               │  ║
║   │  • Probe throughput, calculate spectral gap                        │  ║
║   └────────────────────────────────────────────────────────────────────┘  ║
║          │                                                                 ║
║          │ session_ready()                                                 ║
║          ▼                                                                 ║
║   ┌────────────────────────────────────────────────────────────────────┐  ║
║   │                        TRANSFERRING                                 │  ║
║   ├────────────────────────────────────────────────────────────────────┤  ║
║   │  • Receive prepare-upload POST                                     │  ║
║   │  • Accept file metadata                                            │  ║
║   │  • Receive upload POST with file data                              │  ║
║   │  • Write to /tmp/localsend_received/                              │  ║
║   │  • Track bytes, update spectral gap                                │  ║
║   │  • Voice announce progress                                         │  ║
║   └────────────────────────────────────────────────────────────────────┘  ║
║          │                              │                                  ║
║          │ success()                    │ error()                          ║
║          ▼                              ▼                                  ║
║   ┌─────────────────┐            ┌─────────────────┐                      ║
║   │    COMPLETE     │            │     FAILED      │                      ║
║   ├─────────────────┤            ├─────────────────┤                      ║
║   │ • Voice confirm │            │ • Log error     │                      ║
║   │ • Update stats  │            │ • Voice alert   │                      ║
║   │ • Return IDLE   │            │ • Retry or IDLE │                      ║
║   └─────────────────┘            └─────────────────┘                      ║
║                                                                            ║
╚═══════════════════════════════════════════════════════════════════════════╝
```

---

## N+1 PIGEONHOLE REDUNDANCY

For N concurrent transfer attempts, maintain N+1 channels:

| N | Channels Active | Pigeonholes |
|---|-----------------|-------------|
| 1 | Tailscale | Tailscale + Voice |
| 2 | Tailscale + NATS | Tailscale + NATS + Voice |
| 3 | Tailscale + NATS + LAN | Tailscale + NATS + LAN + Voice |

**Current**: N=1 (Tailscale), Pigeonholes=2 (Tailscale + Voice)

---

## VOICE CHANNEL PROTOCOL

### Establishment Sequence

```
1. ANNOUNCE (outbound)
   Voice: "Attenzione! LocalSend peer causality available!"
   Content: IP, port, alias, fingerprint
   Rate: 150 WPM, Voice: Emma (Premium)

2. SEEK (outbound)  
   Voice: "Cercando peer sulla rete... Rispondete!"
   Purpose: Trigger response from listening peers

3. CONFIRM (on connection)
   Voice: "Connessione stabilita con [peer]!"
   
4. PROGRESS (during transfer)
   Voice: "Trasferimento in corso... [X] percento"

5. COMPLETE (on success)
   Voice: "File ricevuto: [filename]! Completato!"

6. ERROR (on failure)
   Voice: "Errore: [message]. Riprova."
```

### Multi-Voice Redundancy

| Voice | Language | Role |
|-------|----------|------|
| Emma (Premium) | Italian | Primary announcer |
| Anna (Premium) | German | Technical details |
| Amélie (Premium) | French | Confirmation |
| Kyoko (Enhanced) | Japanese | Fallback |
| Zuzana (Premium) | Czech | Error handling |

---

## SUBAGENT DISPATCH PATTERN

```clojure
(defn dispatch-with-pigeonholes! [n-transfers]
  (let [n+1 (inc n-transfers)
        agents (take n+1 [:tailscale :nats :voice :lan :multicast])]
    (doseq [agent agents]
      (future
        (case agent
          :tailscale (tailscale-discover!)
          :nats (nats-subscribe!)
          :voice (voice-announce!)
          :lan (multicast-beacon!)
          :multicast (udp-broadcast!))))))

;; Always have one more channel than needed
;; If any fails, others provide coverage
```

---

## CONNECTION ESTABLISHMENT COMMANDS

### From This Machine (causality)

```bash
# Start receiver
bb ~/.amp/skills/localsend-mcp/localsend.bb receive

# Discover peers
bb ~/.amp/skills/localsend-mcp/discovery.bb discover

# Voice announce
bb ~/.amp/skills/localsend-mcp/voice-exchange.bb announce

# NATS subscribe (if available)
bb ~/.amp/skills/localsend-mcp/nats-channel.bb sub
```

### For Remote Peer (2-monad) to Send

```bash
# Via Tailscale (RECOMMENDED - bypasses firewall)
curl -X POST http://100.69.33.107:53317/api/localsend/v2/prepare-upload \
  -H "Content-Type: application/json" \
  -d '{"info":{"alias":"2-monad"},"files":{"f1":{"id":"f1","fileName":"FILE.txt","size":SIZE}}}'

# Then upload
curl -X POST "http://100.69.33.107:53317/api/localsend/v2/upload?sessionId=SESSION&fileId=f1&token=TOKEN" \
  --data-binary @FILE.txt

# Or use LocalSend app → select "causality"
```

---

## FIREWALL STATUS

```
macOS Firewall: State=2 (BLOCKING)
LAN (192.168.1.40:53317): ❌ BLOCKED
Tailscale (100.69.33.107:53317): ✅ SHOULD WORK (VPN tunnel)
```

**Workaround**: Always use Tailscale IP, not LAN IP.

---

## RECOVERY COMMANDS

If receiver dies:
```bash
pkill -f localsend.bb
bb ~/.amp/skills/localsend-mcp/localsend.bb receive &
```

If no files received:
```bash
# Check logs
tail -50 /tmp/localsend_receiver.log

# Test endpoint
curl http://localhost:53317/

# Re-announce
say -v "Emma (Premium)" "LocalSend ready! Port 53317!"
```

---

## NEXT STEPS FOR CONTINUATION

1. **Sender (2-monad) must initiate** - receiver is passive
2. **Use Tailscale IP** (100.69.33.107) not LAN
3. **Check LocalSend app** on 2-monad for "causality" device
4. **If PIN prompted**: No PIN required, HTTP mode
5. **Files save to**: /tmp/localsend_received/

---

## SKILL LOCATIONS

| Agent | Skill Path | MCP Config |
|-------|------------|------------|
| Amp | ~/.amp/skills/localsend-mcp/ | ~/.config/amp/settings.json |
| Claude | ~/.claude/skills/localsend-mcp/ | ~/.claude/claude_desktop_config.json |
| Codex | ~/.codex/skills/localsend-mcp/ | music-topos/.codex/mcp.json |
| OpenCode | ~/.opencode/skills/localsend-mcp/ | ~/.config/opencode/config.json |

---

**Status**: ADVERTISING (waiting for incoming)
**Session**: sess_1766374506685_x9hkcz
**Peer**: 2-monad @ 100.87.209.11 (active, 15ms RTT)
