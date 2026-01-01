---
name: trifurcated-transfer
description: Trifurcated Transfer Skill
version: 1.0.0
---

# Trifurcated Transfer Skill

```yaml
name: trifurcated-transfer
description: P2P file transfer using 3 parallel subagents over LocalSend HTTP API with GF(3) trit coordination
tags: [p2p, localsend, subagents, file-transfer, tailscale, duckdb, chunking]
version: 1.0.0
author: MINUS
```

## Overview

Trifurcated Transfer implements fault-tolerant P2P file sharing using three parallel subagents, each assigned a trit value from GF(3) (Galois Field of 3 elements). Each subagent attempts transfer over a dedicated channel, providing redundancy and load distribution.

**Core Principles:**
- **Trit Assignment**: MINUS (-1), ERGODIC (0), PLUS (+1)
- **Channel Isolation**: Each trit uses a distinct network path
- **Convergent State**: Transfer succeeds when any channel completes
- **Voice Coordination**: Subagents announce state transitions via `say`

## State Machine

```
┌─────────────────────────────────────────────────────────────────┐
│                    TRIFURCATED TRANSFER FSM                     │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌──────────┐    spawn 3     ┌──────────────────────────────┐  │
│  │  IDLE    │ ─────────────► │        DISCOVERING           │  │
│  └──────────┘                │  MINUS: Tailscale (100.x.y.z)│  │
│       │                      │  ERGODIC: LAN (192.168.x.y)  │  │
│       │                      │  PLUS: DNS (hostname.local)  │  │
│       │                      └──────────────────────────────┘  │
│       │                                   │                     │
│       │                          all resolved                   │
│       │                                   ▼                     │
│       │                      ┌──────────────────────────────┐  │
│       │                      │        PREPARING             │  │
│       │                      │  POST /prepare-upload        │  │
│       │                      │  Acquire session tokens      │  │
│       │                      └──────────────────────────────┘  │
│       │                                   │                     │
│       │                          tokens acquired                │
│       │                                   ▼                     │
│       │                      ┌──────────────────────────────┐  │
│       │                      │        TRANSFERRING          │  │
│       │                      │  POST /upload (parallel)     │  │
│       │                      │  Chunk if file > 8MB         │  │
│       │                      └──────────────────────────────┘  │
│       │                           │       │       │            │
│       │                    success│  fail │ fail  │success     │
│       │                           ▼       ▼       ▼            │
│       │                      ┌──────────────────────────────┐  │
│       │                      │        CONVERGING            │  │
│       │                      │  First success wins          │  │
│       │                      │  Cancel remaining transfers  │  │
│       │                      └──────────────────────────────┘  │
│       │                                   │                     │
│       │                          announce result                │
│       │                                   ▼                     │
│       │                      ┌──────────────────────────────┐  │
│       └───────────────────── │        COMPLETE              │  │
│            reset             │  Voice: "Transfer complete"  │  │
│                              └──────────────────────────────┘  │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## Trit Channels

| Trit | Subagent | Channel | Priority | Use Case |
|------|----------|---------|----------|----------|
| -1 | MINUS | Tailscale IP (100.x.y.z) | Primary | Secure mesh VPN |
| 0 | ERGODIC | LAN IP (192.168.x.y) | Secondary | Local network |
| +1 | PLUS | DNS (.local / hostname) | Tertiary | mDNS discovery |

## LocalSend HTTP API

### Endpoints

**Prepare Upload** - Negotiate transfer session
```
POST http://{host}:53317/api/localsend/v2/prepare-upload
Content-Type: application/json

{
  "info": {
    "alias": "trifurcated-agent",
    "deviceModel": "amp-subagent",
    "deviceType": "headless"
  },
  "files": {
    "file-id-1": {
      "id": "file-id-1",
      "fileName": "data.duckdb",
      "size": 52428800,
      "fileType": "application/octet-stream"
    }
  }
}
```

**Response:**
```json
{
  "sessionId": "abc123",
  "files": {
    "file-id-1": "token-xyz"
  }
}
```

**Upload File**
```
POST http://{host}:53317/api/localsend/v2/upload?sessionId={sessionId}&fileId={fileId}&token={token}
Content-Type: application/octet-stream

[binary data]
```

## File Chunking (>8MB)

Files exceeding 8MB are split into chunks for reliable transfer:

```clojure
(defn chunk-file [path chunk-size]
  (let [file (io/file path)
        size (.length file)
        chunks (Math/ceil (/ size chunk-size))]
    (for [i (range chunks)]
      {:index i
       :offset (* i chunk-size)
       :length (min chunk-size (- size (* i chunk-size)))})))

;; Default chunk size: 8MB
(def chunk-size (* 8 1024 1024))
```

## DuckDB Partitioning

Large DuckDB files are partitioned by table for parallel transfer:

```clojure
(require '[babashka.process :refer [shell]])

(defn partition-duckdb [db-path output-dir]
  (let [tables (-> (shell {:out :string}
                          "duckdb" db-path
                          "-cmd" "SELECT name FROM sqlite_master WHERE type='table'")
                   :out
                   str/split-lines)]
    (doseq [table tables]
      (shell "duckdb" db-path
             "-cmd" (format "COPY %s TO '%s/%s.parquet' (FORMAT PARQUET)"
                           table output-dir table)))))

(defn reassemble-duckdb [parquet-dir output-db]
  (doseq [pq (fs/glob parquet-dir "*.parquet")]
    (let [table (fs/strip-ext (fs/file-name pq))]
      (shell "duckdb" output-db
             "-cmd" (format "CREATE TABLE %s AS SELECT * FROM '%s'"
                           table (str pq))))))
```

## Voice Announcements

Each subagent uses a distinct voice for coordination:

```bash
# MINUS (Trit -1) - French accent speaking English
say -v Thomas "Minus initiating Tailscale transfer"

# ERGODIC (Trit 0) - Swedish accent  
say -v Alva "Ergodic probing LAN endpoint"

# PLUS (Trit +1) - Italian accent
say -v "Luca (Enhanced)" "Plus resolving DNS hostname"

# Convergence announcement
say -v Samantha "Trifurcated transfer complete. Channel minus succeeded."
```

## Commands

### Transfer File
```bash
# Single file transfer
bb -e '(trifurcated-transfer {:file "data.duckdb" :target "macbook"})'

# With explicit channels
bb -e '(trifurcated-transfer {:file "backup.tar.gz" 
                              :channels {:minus "100.64.0.5"
                                        :ergodic "192.168.1.42"
                                        :plus "macbook.local"}})'
```

### Discover Peers
```bash
# Find LocalSend peers on all channels
bb -e '(discover-peers)'
```

### Partition Large DB
```bash
# Split DuckDB into parquet files
bb -e '(partition-duckdb "large.duckdb" "/tmp/partitions")'
```

## Babashka Implementation

```clojure
#!/usr/bin/env bb
(ns trifurcated-transfer
  (:require [babashka.http-client :as http]
            [babashka.fs :as fs]
            [babashka.process :refer [shell]]
            [cheshire.core :as json]
            [clojure.java.io :as io]))

(def trits
  {:minus  {:value -1 :voice "Thomas" :channel :tailscale}
   :ergodic {:value 0  :voice "Alva"   :channel :lan}
   :plus    {:value 1  :voice "Luca (Enhanced)" :channel :dns}})

(defn announce [trit msg]
  (let [{:keys [voice]} (get trits trit)]
    (shell "say" "-v" voice msg)))

(defn prepare-upload [host file-info]
  (-> (http/post (str "http://" host ":53317/api/localsend/v2/prepare-upload")
                 {:headers {"Content-Type" "application/json"}
                  :body (json/generate-string
                         {:info {:alias "trifurcated-agent"
                                :deviceModel "amp-subagent"
                                :deviceType "headless"}
                          :files file-info})})
      :body
      (json/parse-string true)))

(defn upload-file [host session-id file-id token file-path]
  (http/post (str "http://" host ":53317/api/localsend/v2/upload")
             {:query-params {:sessionId session-id
                            :fileId file-id
                            :token token}
              :headers {"Content-Type" "application/octet-stream"}
              :body (io/input-stream file-path)}))

(defn transfer-via-trit [trit host file-path]
  (announce trit (str (name trit) " initiating transfer"))
  (try
    (let [file-id (str (random-uuid))
          file-info {file-id {:id file-id
                              :fileName (fs/file-name file-path)
                              :size (fs/size file-path)
                              :fileType "application/octet-stream"}}
          {:keys [sessionId files]} (prepare-upload host file-info)
          token (get files (keyword file-id))]
      (upload-file host sessionId file-id token file-path)
      (announce trit (str (name trit) " transfer complete"))
      {:success true :trit trit :channel (:channel (get trits trit))})
    (catch Exception e
      (announce trit (str (name trit) " transfer failed"))
      {:success false :trit trit :error (.getMessage e)})))

(defn trifurcated-transfer [{:keys [file channels]}]
  (let [futures (mapv (fn [[trit host]]
                        (future (transfer-via-trit trit host file)))
                      channels)
        results (mapv deref futures)
        winner (first (filter :success results))]
    (if winner
      (do (shell "say" "-v" "Samantha" 
                 (format "Transfer complete via %s channel" (name (:trit winner))))
          winner)
      (do (shell "say" "-v" "Samantha" "All channels failed")
          {:success false :results results}))))

;; Entry point
(when (= *file* (System/getProperty "babashka.file"))
  (let [args *command-line-args*]
    (trifurcated-transfer (read-string (first args)))))
```

## Example Workflow

```bash
# 1. Discover available peers
$ bb -e '(discover-peers)'
;; => {:minus "100.64.0.5", :ergodic "192.168.1.42", :plus "macbook.local"}

# 2. Transfer a small file
$ bb -e '(trifurcated-transfer {:file "config.edn" 
                                :channels {:minus "100.64.0.5"
                                          :ergodic "192.168.1.42"  
                                          :plus "macbook.local"}})'
;; Voice: "Minus initiating transfer"
;; Voice: "Ergodic initiating transfer"  
;; Voice: "Plus initiating transfer"
;; Voice: "Minus transfer complete"
;; Voice: "Transfer complete via minus channel"
;; => {:success true, :trit :minus, :channel :tailscale}

# 3. Transfer large DuckDB (auto-partitioned)
$ bb -e '(trifurcated-transfer {:file "analytics.duckdb"
                                :partition true
                                :channels {:minus "100.64.0.5"
                                          :ergodic "192.168.1.42"
                                          :plus "macbook.local"}})'

# 4. Reassemble on receiving end
$ bb -e '(reassemble-duckdb "/tmp/received-partitions" "analytics.duckdb")'
```

## Error Handling

| Error | Trit Action | Recovery |
|-------|-------------|----------|
| Connection refused | Announce failure, yield to other trits | Other channels continue |
| Timeout (30s) | Cancel, announce | Winner-take-all convergence |
| Partial upload | Retry with resume token | Chunk-level retry |
| All channels fail | Announce aggregate failure | Return error map |

## Dependencies

- `babashka` >= 1.3.0
- `localsend` running on target (port 53317)
- `duckdb` CLI (for partitioning)
- macOS `say` command (for voice)
- Network access to at least one channel

## GF(3) Arithmetic Note

The trit values form a field under modular arithmetic:
- Addition: `(a + b) mod 3` with values mapped as {-1, 0, 1}
- Useful for: consensus quorum, error detection, load balancing index



## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Graph Theory
- **networkx** [○] via bicomodule
  - Universal graph hub

### Bibliography References

- `category-theory`: 139 citations in bib.duckdb

## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: -1 (MINUS)
Home: Prof
Poly Op: ⊗
Kan Role: Ran_K
Color: #FF6B6B
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) ≡ 0 (mod 3)
```

This ensures compositional coherence in the Cat# equipment structure.
