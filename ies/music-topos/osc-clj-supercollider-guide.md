# osc-clj SuperCollider Communication Guide

A comprehensive guide to using osc-clj for direct SuperCollider communication without Overtone dependency.

## Table of Contents
1. [Setup and Dependencies](#setup-and-dependencies)
2. [Basic OSC Communication](#basic-osc-communication)
3. [SuperCollider Server Commands](#supercollider-server-commands)
4. [Receiving OSC Notifications](#receiving-osc-notifications)
5. [Complete Working Example](#complete-working-example)
6. [Advanced Topics](#advanced-topics)

---

## Setup and Dependencies

### project.clj
```clojure
(defproject sc-osc-example "0.1.0-SNAPSHOT"
  :dependencies [[org.clojure/clojure "1.11.1"]
                 [overtone/osc-clj "0.9.0"]])
```

### Basic Imports
```clojure
(ns sc-osc.core
  (:require [overtone.osc :as osc]))
```

---

## Basic OSC Communication

### 1. Creating Client and Server

```clojure
;; SuperCollider default port is 57110
(def SC-SERVER-PORT 57110)
(def SC-CLIENT-PORT 57120)

;; Create a client to send messages to SuperCollider
(def sc-client (osc/osc-client "localhost" SC-SERVER-PORT))

;; Create a server to receive messages from SuperCollider
(def sc-listener (osc/osc-server SC-CLIENT-PORT))
```

### 2. Sending OSC Messages

The basic function is `osc-send`:

```clojure
;; General format: (osc-send client path & args)
(osc/osc-send sc-client "/status")
```

**Important**: osc-clj automatically infers types through reflection:
- Integers → OSC int32
- Floats/Doubles → OSC float32
- Strings → OSC string
- Byte arrays → OSC blob

```clojure
;; Examples of automatic type inference
(osc/osc-send sc-client "/test"
              42          ; int
              3.14        ; float
              "hello"     ; string
              (byte-array [1 2 3])) ; blob
```

---

## SuperCollider Server Commands

### /notify - Register for Notifications

Enable server notifications (required to receive /n_go, /n_end, etc.):

```clojure
(defn enable-notifications []
  ;; arg: 1 = enable, 0 = disable
  (osc/osc-send sc-client "/notify" 1))

(enable-notifications)
```

Reply: `/done /notify clientID`

### /status - Query Server Status

```clojure
(defn request-status []
  (osc/osc-send sc-client "/status"))
```

Reply format: `/status.reply [unused numUgens numSynths numGroups numSynthDefs avgCPU peakCPU nominalSR actualSR]`

### /s_new - Create New Synth

Format: `/s_new synthDefName synthID addAction targetID [controlName value ...]`

**Add Actions:**
- 0 = add to head of group
- 1 = add to tail of group
- 2 = add before node
- 3 = add after node
- 4 = replace node

```clojure
(defn create-synth
  "Create a synth with the given name and ID"
  [synth-name synth-id & {:keys [target-id add-action controls]
                          :or {target-id 1    ; default group
                               add-action 1   ; add to tail
                               controls []}}]
  (let [msg-args (concat [synth-name synth-id add-action target-id]
                         controls)]
    (apply osc/osc-send sc-client "/s_new" msg-args)))

;; Examples:
;; Create default synth with ID 1000 at tail of default group
(create-synth "default" 1000)

;; Create sine synth with controls
(create-synth "sine" 1001
              :controls ["freq" 440.0 "amp" 0.5])

;; Create with specific placement
(create-synth "filter" 1002
              :target-id 1001    ; target node
              :add-action 3      ; add after
              :controls ["cutoff" 2000.0])
```

### /n_set - Set Node Control Values

Format: `/n_set nodeID controlName value [controlName value ...]`

```clojure
(defn set-control
  "Set control values on a node"
  [node-id & name-value-pairs]
  (apply osc/osc-send sc-client "/n_set" node-id name-value-pairs))

;; Examples:
(set-control 1000 "freq" 220.0)
(set-control 1000 "freq" 440.0 "amp" 0.3 "pan" -0.5)

;; Using control indices instead of names
(set-control 1000 0 440.0 1 0.5)  ; index 0 and 1
```

### /n_free - Free a Node

Format: `/n_free nodeID [nodeID ...]`

```clojure
(defn free-node
  "Free one or more nodes"
  [& node-ids]
  (apply osc/osc-send sc-client "/n_free" node-ids))

;; Examples:
(free-node 1000)           ; free single node
(free-node 1000 1001 1002) ; free multiple nodes
```

### /d_recv - Receive Synth Definition

This loads a synth definition from bytes. In practice, you'd typically use `/d_load` to load .scsyndef files.

```clojure
(defn load-synthdef-file
  "Load a synth definition file"
  [filepath]
  (osc/osc-send sc-client "/d_load" filepath))

;; Example:
(load-synthdef-file "/path/to/synthdefs/mysynth.scsyndef")

;; With completion message (execute after loading)
(defn load-synthdef-with-completion
  [filepath completion-msg]
  ;; Completion message is an OSC blob
  (osc/osc-send sc-client "/d_load"
                filepath
                (osc/osc-msg-infer-types completion-msg)))
```

### /sync - Synchronization

Wait for all async commands to complete:

```clojure
(defn sync-server
  "Send sync message with unique ID"
  [sync-id]
  (osc/osc-send sc-client "/sync" sync-id))

;; Server will reply with /synced when all prior async commands complete
(sync-server 1234)
```

### /g_new - Create Group

Format: `/g_new groupID addAction targetID [groupID addAction targetID ...]`

```clojure
(defn create-group
  "Create a new group node"
  [group-id & {:keys [target-id add-action]
               :or {target-id 1
                    add-action 1}}]
  (osc/osc-send sc-client "/g_new" group-id add-action target-id))

;; Examples:
(create-group 100)                    ; create at tail of default group
(create-group 101 :target-id 100 :add-action 0)  ; at head of group 100
```

### /b_alloc - Allocate Buffer

Format: `/b_alloc bufNum numFrames [numChannels]`

```clojure
(defn alloc-buffer
  "Allocate a buffer"
  [buf-num num-frames & {:keys [num-channels]
                         :or {num-channels 1}}]
  (osc/osc-send sc-client "/b_alloc" buf-num num-frames num-channels))

;; Example:
(alloc-buffer 0 44100)      ; 1 second mono buffer at 44.1kHz
(alloc-buffer 1 88200 :num-channels 2)  ; 2 second stereo buffer
```

---

## Receiving OSC Notifications

### Setting Up Handlers

```clojure
(defn setup-handlers []
  ;; Handler for /status.reply
  (osc/osc-handle sc-listener "/status.reply"
    (fn [msg]
      (let [args (:args msg)]
        (println "Server Status:")
        (println "  UGens:" (nth args 1))
        (println "  Synths:" (nth args 2))
        (println "  Groups:" (nth args 3))
        (println "  SynthDefs:" (nth args 4))
        (println "  CPU avg:" (nth args 5) "%")
        (println "  CPU peak:" (nth args 6) "%"))))

  ;; Handler for /n_go (node started)
  (osc/osc-handle sc-listener "/n_go"
    (fn [msg]
      (let [[node-id parent-id prev-id next-id is-group] (:args msg)]
        (println (format "Node started: %d (parent: %d, type: %s)"
                        node-id parent-id
                        (if (= is-group 1) "group" "synth"))))))

  ;; Handler for /n_end (node ended)
  (osc/osc-handle sc-listener "/n_end"
    (fn [msg]
      (let [[node-id parent-id prev-id next-id is-group] (:args msg)]
        (println (format "Node ended: %d" node-id)))))

  ;; Handler for /done
  (osc/osc-handle sc-listener "/done"
    (fn [msg]
      (println "Command completed:" (:args msg))))

  ;; Handler for /synced
  (osc/osc-handle sc-listener "/synced"
    (fn [msg]
      (println "Server synced, ID:" (first (:args msg)))))

  ;; Handler for /fail
  (osc/osc-handle sc-listener "/fail"
    (fn [msg]
      (println "Command failed:" (:args msg))))

  ;; Generic listener for all messages (useful for debugging)
  (osc/osc-listen sc-listener
    (fn [msg]
      (println "Received:" (:path msg) (:args msg)))
    :debug))
```

### Message Structure

All received messages have this structure:

```clojure
{:src-host "127.0.0.1"
 :src-port 57110
 :path "/n_go"
 :type-tag "iiiii"  ; i=int, f=float, s=string, b=blob
 :args [1000 1 -1 -1 0]}
```

### Removing Handlers

```clojure
;; Remove specific handler
(osc/osc-rm-handler sc-listener "/status.reply")

;; Remove all handlers
(osc/osc-rm-all-handlers sc-listener)

;; Remove listener by key
(osc/osc-rm-listener sc-listener :debug)
```

---

## Complete Working Example

```clojure
(ns sc-osc.example
  (:require [overtone.osc :as osc]))

;; Configuration
(def SC-SERVER-PORT 57110)
(def SC-CLIENT-PORT 57120)

;; Global state
(def sc-client (atom nil))
(def sc-listener (atom nil))
(def next-node-id (atom 1000))

;; Helper to generate unique node IDs
(defn gen-node-id []
  (swap! next-node-id inc))

;; Initialize OSC communication
(defn init-osc []
  (reset! sc-client (osc/osc-client "localhost" SC-SERVER-PORT))
  (reset! sc-listener (osc/osc-server SC-CLIENT-PORT))
  (setup-handlers))

;; Setup all message handlers
(defn setup-handlers []
  ;; Status reply handler
  (osc/osc-handle @sc-listener "/status.reply"
    (fn [msg]
      (let [[_ ugens synths groups defs avg-cpu peak-cpu] (:args msg)]
        (println (format "Status: %d synths, %d groups, CPU: %.2f%% avg / %.2f%% peak"
                        synths groups avg-cpu peak-cpu)))))

  ;; Node lifecycle handlers
  (osc/osc-handle @sc-listener "/n_go"
    (fn [msg]
      (println "Synth started:" (first (:args msg)))))

  (osc/osc-handle @sc-listener "/n_end"
    (fn [msg]
      (println "Synth ended:" (first (:args msg)))))

  ;; Completion handlers
  (osc/osc-handle @sc-listener "/done"
    (fn [msg]
      (println "Command done:" (:args msg))))

  (osc/osc-handle @sc-listener "/synced"
    (fn [msg]
      (println "Server synced"))))

;; High-level API
(defn status []
  (osc/osc-send @sc-client "/status"))

(defn play-synth
  "Play a synth with optional parameters"
  [synth-name & {:keys [freq amp dur node-id]
                 :or {freq 440.0
                      amp 0.5
                      dur 1.0
                      node-id (gen-node-id)}}]
  (let [controls (cond-> []
                   freq (conj "freq" freq)
                   amp (conj "amp" amp)
                   dur (conj "dur" dur))]
    (apply osc/osc-send @sc-client "/s_new"
           synth-name node-id 1 1 controls)
    node-id))

(defn stop-synth [node-id]
  (osc/osc-send @sc-client "/n_free" node-id))

(defn set-synth-param [node-id param-name value]
  (osc/osc-send @sc-client "/n_set" node-id param-name value))

;; Example usage
(defn demo []
  ;; Initialize
  (init-osc)
  (Thread/sleep 100)  ; Give server time to start

  ;; Enable notifications
  (osc/osc-send @sc-client "/notify" 1)
  (Thread/sleep 100)

  ;; Check status
  (status)
  (Thread/sleep 100)

  ;; Play a synth (assumes 'default' synthdef exists)
  (let [synth-id (play-synth "default" :freq 440.0 :amp 0.3)]
    (println "Playing synth" synth-id)

    ;; Change frequency after 1 second
    (Thread/sleep 1000)
    (set-synth-param synth-id "freq" 880.0)
    (println "Changed frequency")

    ;; Stop after 2 more seconds
    (Thread/sleep 2000)
    (stop-synth synth-id)
    (println "Stopped synth")))

;; Cleanup
(defn shutdown []
  (when @sc-listener
    (osc/osc-close @sc-listener))
  (when @sc-client
    (osc/osc-close @sc-client)))
```

---

## Advanced Topics

### Using OSC Bundles (Timestamped Messages)

Bundles allow you to schedule messages with sample-accurate timing:

```clojure
(defn play-chord-bundle
  "Play multiple notes as a bundle for sample-accurate timing"
  [freqs]
  (let [now (osc/osc-now)  ; Current OSC time
        delay-ms 100]       ; Schedule 100ms in future
    (osc/in-osc-bundle @sc-client (+ now delay-ms)
      (doseq [freq freqs]
        (play-synth "default" :freq freq :amp 0.2)))))

;; Play a C major chord
(play-chord-bundle [261.63 329.63 392.00])
```

### Creating OSC Messages Manually

```clojure
;; Create message structure
(def my-msg (osc/osc-msg "/s_new" "default" 1000 1 1 "freq" 440.0))

;; Send the message
(osc/osc-send-msg @sc-client my-msg)

;; Create and send bundle
(def my-bundle
  (osc/osc-bundle (+ (osc/osc-now) 1000)  ; 1 second from now
                  [(osc/osc-msg "/s_new" "default" 1001 1 1)
                   (osc/osc-msg "/s_new" "default" 1002 1 1)]))

(osc/osc-send-bundle @sc-client my-bundle)
```

### Synth Definition as Data

While you typically load .scsyndef files, you can theoretically construct synth definitions as byte arrays. However, this is complex and not recommended. Instead:

```clojure
;; SuperCollider side - save synthdef
;; SynthDef(\sine, { |freq=440, amp=0.5|
;;     Out.ar(0, SinOsc.ar(freq, 0, amp) ! 2)
;; }).writeDefFile("/path/to/synthdefs");

;; Clojure side - load it
(defn load-sine-synth []
  (osc/osc-send @sc-client "/d_load"
                "/path/to/synthdefs/sine.scsyndef"))
```

### Pattern Matching in Handlers

osc-clj supports OSC pattern matching with wildcards:

```clojure
;; Match any status message
(osc/osc-handle @sc-listener "/status*"
  (fn [msg] (println "Status message:" msg)))

;; Match all node notifications
(osc/osc-handle @sc-listener "/n_*"
  (fn [msg] (println "Node notification:" (:path msg))))

;; Match with ? (single char wildcard)
(osc/osc-handle @sc-listener "/n_?o"
  (fn [msg] (println "Matches /n_go or /n_no")))

;; Match with character classes
(osc/osc-handle @sc-listener "/n_[gs]*"
  (fn [msg] (println "Node get or set message")))
```

### Error Handling

```clojure
(defn safe-send [path & args]
  (try
    (apply osc/osc-send @sc-client path args)
    (catch Exception e
      (println "OSC send error:" (.getMessage e)))))

;; Wait for response with timeout
(defn status-with-timeout [timeout-ms]
  (let [result (atom nil)
        done (promise)]
    ;; Set up temporary handler
    (osc/osc-handle @sc-listener "/status.reply"
      (fn [msg]
        (reset! result (:args msg))
        (deliver done true)))

    ;; Send request
    (status)

    ;; Wait with timeout
    (let [timeout (deref done timeout-ms false)]
      (osc/osc-rm-handler @sc-listener "/status.reply")
      (if timeout
        @result
        (println "Timeout waiting for status")))))
```

### Multi-Client Coordination

```clojure
(defn register-client []
  ;; Request client ID from server
  (let [client-id (atom nil)
        done (promise)]
    (osc/osc-handle @sc-listener "/done"
      (fn [msg]
        (when (= (first (:args msg)) "/notify")
          (reset! client-id (second (:args msg)))
          (deliver done true))))

    (osc/osc-send @sc-client "/notify" 1 0)  ; 0 = request ID
    (deref done 1000 false)
    @client-id))
```

---

## Reference: Common SuperCollider Commands

### Server Commands
- `/quit` - Quit server
- `/notify [0|1]` - Enable/disable notifications
- `/status` - Query server status
- `/dumpOSC [0-3]` - Set OSC message dumping level
- `/sync [id]` - Synchronization barrier
- `/version` - Query server version

### Node Commands
- `/n_free [nodeIDs...]` - Free nodes
- `/n_run [nodeID runFlag]...` - Start/stop nodes
- `/n_set [nodeID ctlName value...]` - Set controls
- `/n_query [nodeIDs...]` - Query node info
- `/n_trace [nodeIDs...]` - Trace node execution

### Synth Commands
- `/s_new [defName id action target controls...]` - Create synth
- `/s_get [id ctlNames...]` - Get control values
- `/s_noid [ids...]` - Auto-reassign IDs

### Group Commands
- `/g_new [id action target]...` - Create group
- `/g_freeAll [groupIDs...]` - Free all in group
- `/g_deepFree [groupIDs...]` - Deep free group
- `/g_dumpTree [groupID flag]` - Dump node tree
- `/g_queryTree [groupID flag]` - Query node tree

### Buffer Commands
- `/b_alloc [bufNum frames channels]` - Allocate buffer
- `/b_free [bufNum]` - Free buffer
- `/b_query [bufNums...]` - Query buffer info
- `/b_read [bufNum path...]` - Read audio file

---

## Troubleshooting

### Server Not Responding

```clojure
;; Check if scsynth is running
;; In terminal: pgrep scsynth

;; Try connecting to different port
(def sc-client (osc/osc-client "localhost" 57110))

;; Enable OSC debugging
(osc/osc-send sc-client "/dumpOSC" 1)
```

### Messages Not Received

```clojure
;; Verify listener is running
(osc/osc-debug true)  ; Enable debug output

;; Check notifications are enabled
(osc/osc-send @sc-client "/notify" 1)

;; Add catch-all listener
(osc/osc-listen @sc-listener
  (fn [msg] (println "ANY:" msg))
  :catch-all)
```

### Node ID Conflicts

```clojure
;; Use server-generated IDs
(osc/osc-send @sc-client "/s_new" "default" -1 1 1)
;; Server assigns ID and you can reference with -1 for next command

;; Or maintain your own ID pool
(def node-ids (atom (range 1000 2000)))

(defn get-node-id []
  (let [id (first @node-ids)]
    (swap! node-ids rest)
    id))
```

---

## Resources

- **osc-clj GitHub**: https://github.com/overtone/osc-clj
- **SuperCollider Server Command Reference**: https://doc.sccode.org/Reference/Server-Command-Reference.html
- **OSC Specification**: http://opensoundcontrol.org/spec-1_0
- **SuperCollider Server Architecture**: https://doc.sccode.org/Reference/Server-Architecture.html
