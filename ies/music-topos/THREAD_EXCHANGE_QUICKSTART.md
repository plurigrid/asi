# Thread Search + LocalSend P2P Exchange

**Goal**: Search your thread history, find relevant files, and exchange them with peers via P2P LocalSend protocol.

---

## Quick Start (5 minutes)

### 1. Make scripts executable
```bash
chmod +x /Users/bob/ies/music-topos/lib/thread_exchange.py
chmod +x /Users/bob/ies/music-topos/lib/thread_exchange.bb
```

### 2. Search for threads and exchange files (Python)
```bash
# Search for "skill" threads and exchange related files
python3 ~/ies/music-topos/lib/thread_exchange.py search skill

# Search for "MCP" threads
python3 ~/ies/music-topos/lib/thread_exchange.py search MCP

# Discover available peers
python3 ~/ies/music-topos/lib/thread_exchange.py discover
```

### 3. Or use Babashka version (faster)
```bash
# Search for threads
bb ~/ies/music-topos/lib/thread_exchange.bb search skill

# Exchange for specific thread
bb ~/ies/music-topos/lib/thread_exchange.bb exchange T-019b4405-2a14-7207-af89-748a784371d5

# Discover peers
bb ~/ies/music-topos/lib/thread_exchange.bb discover
```

---

## System Architecture

### Three-Layer System

```
┌─────────────────────────────────────────────────────────────┐
│ THREAD SEARCH LAYER                                         │
│ • DuckDB unified_thread_lake.duckdb (23+ threads)          │
│ • Concept indexing (26 concepts, 36 relations)             │
│ • GF(3) distributed coloring (RED/YELLOW/BLUE)            │
└─────────────────────────────────────────────────────────────┘
              ↓
┌─────────────────────────────────────────────────────────────┐
│ FILE DISCOVERY LAYER                                        │
│ • Map concepts → file extensions                           │
│ • Find matching files in project                           │
│ • Limit to 10 files per concept                            │
└─────────────────────────────────────────────────────────────┘
              ↓
┌─────────────────────────────────────────────────────────────┐
│ P2P EXCHANGE LAYER (LocalSend)                             │
│ • HTTP on port 53317 (Tailscale VPN tunnel)               │
│ • N+1 redundancy (Tailscale + Voice announcements)         │
│ • Peer: 2-monad @ 100.87.209.11:53317                     │
│ • Self: causality @ 100.69.33.107:53317                   │
└─────────────────────────────────────────────────────────────┘
```

---

## Key Components

### Thread Lake Database
```
Location: /Users/bob/ies/music-topos/lib/unified_thread_lake.duckdb
Contains: 23 threads, 2290+ messages, 26 concepts
```

**Top Hub Concepts** (by connectivity):
1. **skill** (9 connections) - Core capability abstraction
2. **ACSet** (8 connections) - Algebraic data structures
3. **MCP** (6 connections) - Model Context Protocol
4. **HyJAX** (6 connections) - Relational patterns
5. **GF3** (5 connections) - Ternary coloring system

**Concept Categories**:
- **Architecture**: skill, MCP, subagent, topos, ACSet
- **Data**: DuckDB, Babashka, Clojure, WORLD
- **Theory**: GF3, HyJAX, relational, alife, spectral
- **Tools**: LocalSend, justfile, Codex, NATS

### LocalSend Peers

**Your Machine (causality)**
```
Tailscale IP:  100.69.33.107
Tailscale DNS: causality.pirate-dragon.ts.net
LAN IP:        192.168.1.40 (BLOCKED by firewall)
Port:          53317
Status:        ADVERTISING (ready to receive)
Voice:         Emma (Premium) - Italian announcements
```

**Remote Peer (2-monad)**
```
Tailscale IP:  100.87.209.11
Tailscale DNS: 2-monad.pirate-dragon.ts.net
LAN IP:        192.168.1.44
Port:          53317
Status:        ACTIVE (RTT: 15ms)
Color:         #83D88F (green)
```

---

## Workflow Examples

### Example 1: Search "skill" and exchange
```bash
$ python3 ~/ies/music-topos/lib/thread_exchange.py search skill

======================================================================
  SEARCH & EXCHANGE: skill
======================================================================

[ANNOUNCING] LocalSend peer availability...
LocalSend peer causality ready on port 53317!
[SEARCH] Found 5 threads for 'skill'
  • T-019b4417-c005-743b-8a4c... (weight: 2)
  • T-019b4424-7b9e-7515-bb83... (weight: 2)
  • T-019b4405-2a14-7207-af89... (weight: 2)
...

======================================================================
  THREAD EXCHANGE: T-019b4417-c005-743b-8a4c-1b87bcfc806f
======================================================================

[CONCEPTS] skill, relational, HyJAX, subagent
[FILES FOUND] 7 files
  • skill_maker.py (0.45 MB)
  • thread_exchange.py (8.2 KB)
  • metaskill_ecosystem.md (15 KB)
  ...
[PEER DISCOVERY]
  Known peer: 2-monad @ 100.87.209.11:53317
[STARTING] LocalSend receiver on port 53317...
[✓] Receiver started
[TRANSFER] Sending to 2-monad (100.87.209.11)...
[SENDING] skill_maker.py (0.45 MB) to 2-monad@100.87.209.11...
[✓] File sent successfully
[SENDING] thread_exchange.py (8.2 KB) to 2-monad@100.87.209.11...
[✓] File sent successfully
[SENDING] metaskill_ecosystem.md (15 KB) to 2-monad@100.87.209.11...
[✓] File sent successfully
[RESULT] Sent 3/7 files
```

### Example 2: Exchange files for specific thread
```bash
$ python3 ~/ies/music-topos/lib/thread_exchange.py exchange T-019b4405-2a14-7207-af89-748a784371d5

[CONCEPTS] LocalSend, Babashka, P2P, alife
[FILES FOUND] 5 files
  • localsend.bb (13.4 KB)
  • thread_exchange.bb (6.2 KB)
  • announce.bb (2.4 KB)
  ...
[TRANSFER] Sending to 2-monad (100.87.209.11)...
[✓] Sent 3/5 files
```

### Example 3: List available peers
```bash
$ python3 ~/ies/music-topos/lib/thread_exchange.py discover

[PEER DISCOVERY]
  Known peer: 2-monad @ 100.87.209.11:53317
[ANNOUNCING] LocalSend peer availability...
[✓] Announced
```

---

## Concept-to-File Mapping

When you search for a concept, this script finds files with matching extensions:

| Concept | Extensions |
|---------|-----------|
| **skill** | .jl, .py, .rb, .bb |
| **MCP** | .json, .py, .bb |
| **DuckDB** | .duckdb, .sql, .py |
| **ACSet** | .jl, .py, .json |
| **GF3** | .py, .jl, .bb |
| **LocalSend** | .bb, .py, .edn |
| **Babashka** | .bb, .clj, .edn |
| **Clojure** | .clj, .cljs, .edn |
| **HyJAX** | .py, .jl, .bb |
| **alife** | .py, .jl, .json |
| **topos** | .jl, .py, .rb, .json |

---

## Advanced: Direct LocalSend Commands

### Start receiver
```bash
bb ~/.amp/skills/localsend-mcp/localsend.bb receive
```

### Announce availability
```bash
bb ~/.amp/skills/localsend-mcp/announce.bb

# Or manually
say -v "Emma (Premium)" "LocalSend ready on port 53317!"
```

### Discover peers via voice
```bash
say -v "Emma (Premium)" -r 200 "Seeking peers! Respond if you hear this!"
```

### Check if receiver is running
```bash
lsof -i :53317
```

### View received files
```bash
ls -la /tmp/localsend_received/
```

### Send file directly (Tailscale)
```bash
curl -X POST http://100.87.209.11:53317/api/localsend/v2/prepare-upload \
  -H "Content-Type: application/json" \
  -d '{"info":{"alias":"causality"},"files":{"f1":{"id":"f1","fileName":"FILE.txt","size":1024}}}'
```

---

## Troubleshooting

### "Port 53317 already in use"
```bash
pkill -f localsend.bb
sleep 2
bb ~/.amp/skills/localsend-mcp/localsend.bb receive
```

### "Peer not found"
```bash
# Check known peers
cat ~/.amp/skills/localsend-mcp/peers.edn

# Manually add peer
# Edit peers.edn and restart
```

### "Files not being found"
```bash
# Check file discovery
python3 -c "
from lib.thread_exchange import find_files_by_concepts
files = find_files_by_concepts(['skill', 'MCP'])
for f in files: print(f)
"
```

### "Connection refused on LAN IP"
```bash
# macOS firewall is blocking LAN (192.168.x.x)
# Use Tailscale IP (100.x.x.x) instead - it tunnels through VPN
```

### "Voice announcement not working"
```bash
# Check available voices
say -v '?' | grep Premium

# Install Emma voice if missing
# System Preferences → Accessibility → Speech → System Voice
```

---

## Integration with Other Skills

### With **alife** skill
```bash
bb thread_exchange.bb search alife
# Finds threads about artificial life and exchanges biology/evolution files
```

### With **code-refactoring** skill
```bash
bb thread_exchange.bb search relational
# Exchanges refactored code maintaining relational semantics
```

### With **acsets** skill
```bash
bb thread_exchange.bb search ACSet
# Exchanges categorical data structure definitions
```

---

## Performance Notes

- **Query time**: ~200ms for thread lake search (DuckDB)
- **File discovery**: ~500ms to traverse project (depends on size)
- **Transfer time**: ~1-5 seconds per file over Tailscale VPN
- **Startup time**: ~2 seconds to start receiver + announce

---

## Next Steps

1. **Automate**: Set up a cron job to periodically search and exchange
   ```bash
   # Every 6 hours, search for "skill" threads and exchange
   0 */6 * * * /usr/bin/python3 ~/ies/music-topos/lib/thread_exchange.py search skill
   ```

2. **Monitor**: Watch /tmp/localsend_received/ for incoming files
   ```bash
   watch -n 1 'ls -lh /tmp/localsend_received/ | tail -10'
   ```

3. **Scale**: Add more peers to peers.edn and they'll be discovered automatically
   ```clojure
   {:peers [{:name "3-cardinal" :ip "100.x.x.x" ...}
            {:name "4-sentinel" :ip "100.y.y.y" ...}]}
   ```

4. **Extend**: Modify concept-file-map to add your own file patterns
   ```python
   CONCEPT_FILE_MAP = {
       "my-concept": [".my", ".custom", ".extensions"],
       ...
   }
   ```

---

**Version**: 1.0
**Created**: 2025-12-21
**Peers**: causality (100.69.33.107) ↔ 2-monad (100.87.209.11)
**Status**: Ready for thread-based P2P exchange
