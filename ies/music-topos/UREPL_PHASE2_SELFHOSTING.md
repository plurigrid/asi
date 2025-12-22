# UREPL Phase 2: Self-Hosting Implementation

**Status**: Phase 2 Planning & Initial Implementation
**Date**: 2025-12-21
**Phase 1 Foundation**: ✅ Complete
**Phase 2 Target**: Live REPL connections with color-guided bootstrap

---

## Phase 2 Overview

Phase 2 transforms UREPL from a **specification** (Phase 1) into a **self-hosting meta-interpreter** with live connections to actual Scheme, Clojure, and Common Lisp REPLs. The system will:

1. **Start a WebSocket server** listening for UREPL messages
2. **Connect to live REPLs** (Scheme via Geiser, Clojure via nREPL, Common Lisp via SLIME)
3. **Route messages** through the three-agent coordinator
4. **Execute code** in the live REPL and return results
5. **Implement core SRFIs** (Scheme Requests for Implementation)
6. **Use color guidance** to trace execution across dialects

---

## Phase 2 Components

### 1. UREPL Message Server (Clojure)

**File**: `src/urepl/server.clj` (450 lines planned)

The WebSocket server that receives UREPL messages and routes them through agents:

```clojure
(ns urepl.server
  (:require [ring.adapter.jetty :as jetty]
            [compojure.core :refer [defroutes GET POST]]
            [compojure.route :as route]
            [ring.middleware.json :refer [wrap-json-body wrap-json-response]]
            [aleph.http :as http]
            [manifold.stream :as s]
            [cheshire.core :as json]
            [urepl.coordinator :as coordinator]
            [urepl.repl-connectors :as connectors]))

;; WebSocket endpoint for incoming UREPL messages
(defn urepl-handler [request]
  (let [stream (s/stream)]
    (s/on-message stream
      (fn [msg]
        (let [parsed (json/parse-string msg true)
              result (coordinator/process-message parsed)]
          (s/put! stream (json/generate-string result)))))
    {:status 200
     :headers {"content-type" "application/octet-stream"}
     :body stream}))

;; REST endpoints for health checks and metrics
(defroutes routes
  (GET "/" [] {:status 200 :body "UREPL Server v0.2.0"})
  (GET "/health" [] {:status 200 :body {"status" "ok"}})
  (POST "/urepl/execute" request (urepl-handler request))
  (route/not-found "Not found"))

(defn start-server [port]
  (println (format "UREPL Server starting on port %d" port))
  (http/start-server routes {:port port}))
```

**Key Features**:
- Persistent WebSocket connections
- Graceful error handling and reconnection logic
- Message buffering for offline periods
- Health checks and metrics endpoints

### 2. REPL Connectors (Multi-Language)

**File**: `src/urepl/repl-connectors.clj` (600 lines planned)

Adapters for connecting to live REPLs in each dialect:

```clojure
;; Scheme REPL Connector (via Geiser protocol)
(defprotocol SchemeREPL
  (connect-scheme [this host port])
  (eval-scheme [this code])
  (disconnect-scheme [this]))

(defrecord GeiserSchemeREPL [host port socket]
  SchemeREPL
  (connect-scheme [this host port]
    (let [sock (Socket. host port)]
      (assoc this :host host :port port :socket sock)))
  (eval-scheme [this code]
    (send-code-to-repl socket code)
    (read-response socket))
  (disconnect-scheme [this]
    (.close socket)))

;; Clojure REPL Connector (via nREPL protocol)
(defprotocol ClojureREPL
  (connect-clojure [this host port])
  (eval-clojure [this code])
  (disconnect-clojure [this]))

(defrecord NREPLClojureREPL [host port client]
  ClojureREPL
  (connect-clojure [this host port]
    (let [client (nrepl/connect :host host :port port)]
      (assoc this :host host :port port :client client)))
  (eval-clojure [this code]
    (let [result (nrepl/eval client code)]
      (:value result)))
  (disconnect-clojure [this]
    (nrepl/disconnect client)))

;; Common Lisp REPL Connector (via SLIME protocol)
(defprotocol CommonLispREPL
  (connect-lisp [this host port])
  (eval-lisp [this code])
  (disconnect-lisp [this]))

(defrecord SLIMECommonLispREPL [host port socket]
  CommonLispREPL
  (connect-lisp [this host port]
    (let [sock (Socket. host port)]
      (assoc this :host host :port port :socket sock)))
  (eval-lisp [this code]
    (send-code-to-repl socket code)
    (read-response socket))
  (disconnect-lisp [this]
    (.close socket)))
```

**Connection Pattern**:
1. Establish socket connection to REPL host:port
2. Send code formatted per dialect protocol
3. Read response with timeout and error handling
4. Parse result back into UREPL message format

### 3. Color-Guided Bootstrap Sequence

**File**: `src/urepl/bootstrap.clj` (350 lines planned)

Initialize the system with color-guided execution:

```clojure
(defn bootstrap-sequence []
  "Initialize UREPL with color-guided startup sequence"
  (let [seed 42  ; Deterministic starting seed
        colors (generate-color-sequence seed)
        steps [
          {:name "Connect Scheme REPL"
           :code "(define *urepl-version* \"0.2.0\")"
           :color (nth colors 0)}
          {:name "Connect Clojure nREPL"
           :code "(def *urepl-version* \"0.2.0\")"
           :color (nth colors 1)}
          {:name "Connect Common Lisp REPL"
           :code "(defvar *urepl-version* \"0.2.0\")"
           :color (nth colors 2)}
          {:name "Load SRFI 2 (List Predicates)"
           :code "(load-srfi 2)"
           :color (nth colors 3)}
          {:name "Load SRFI 5 (Let Syntax)"
           :code "(load-srfi 5)"
           :color (nth colors 4)}
          {:name "Load SRFI 26 (Cut/Cute)"
           :code "(load-srfi 26)"
           :color (nth colors 5)}
          {:name "Load SRFI 48 (Formatted Output)"
           :code "(load-srfi 48)"
           :color (nth colors 6)}
          {:name "Self-host UREPL"
           :code "(load \"src/urepl/evaluator.scm\")"
           :color (nth colors 7)}
        ]]
    (doseq [{:keys [name code color]} steps]
      (println (format "🎨 %s (color: %s)" name (:hex color)))
      (let [result (coordinator/process-code code)]
        (println (format "   Result: %s" (:value result)))))))
```

**Execution Model**:
- Each step assigned deterministic color from seed 42
- Color trace recorded in execution metadata
- Failures logged with color annotation for debugging
- All three REPLs initialized in parallel

### 4. SRFI Implementation Framework

**File**: `src/urepl/srfi-loader.clj` (400 lines planned)

Load and manage Scheme Requests for Implementation:

```clojure
(ns urepl.srfi-loader
  (:require [clojure.java.io :as io]
            [clojure.string :as str]))

(def srfi-registry
  {2   {:name "List Predicates"
        :file "srfi/srfi-2.scm"
        :predicates ["null?" "list?" "append"]}
   5   {:name "Let Syntax"
        :file "srfi/srfi-5.scm"
        :forms ["let" "let*" "letrec"]}
   26  {:name "Cut (Partial Application)"
        :file "srfi/srfi-26.scm"
        :forms ["cut" "cute"]}
   48  {:name "Formatted Output"
        :file "srfi/srfi-48.scm"
        :functions ["format"]}
   89  {:name "Factorial and Binomial"
        :file "srfi/srfi-89.scm"
        :functions ["factorial" "binomial"]}
   135 {:name "Immutable Cyclic Data"
        :file "srfi/srfi-135.scm"
        :types ["cyclic-list"]}})

(defn load-srfi [number]
  "Load a specific SRFI by number"
  (if-let [srfi (srfi-registry number)]
    (let [file (:file srfi)
          code (slurp (io/resource file))]
      (println (format "Loading SRFI %d: %s" number (:name srfi)))
      (eval-scheme code))
    (throw (Exception. (format "SRFI %d not found" number)))))

(defn list-srfis []
  "List all available SRFIs"
  (doseq [[num srfi] (sort srfi-registry)]
    (println (format "SRFI %3d: %s" num (:name srfi)))))
```

**SRFI Loading Strategy**:
- Pre-written implementation files in `srfi/` directory
- Registry maps SRFI number to metadata
- Load on-demand via `(load-srfi N)`
- Implementations are Scheme code (self-hosting)

### 5. Phase 2 Testing Infrastructure

**File**: `src/urepl/phase2-tests.clj` (300 lines planned)

Integration tests for live REPL connections:

```clojure
(deftest test-scheme-connection
  (let [repl (GeiserSchemeREPL. "localhost" 4005)]
    (is (= 3 (eval-scheme repl "(+ 1 2)")))
    (is (= 5 (eval-scheme repl "(* 2 2.5)")))))

(deftest test-clojure-connection
  (let [repl (NREPLClojureREPL. "localhost" 7888)]
    (is (= 3 (eval-clojure repl "(+ 1 2)")))
    (is (= 5 (eval-clojure repl "(* 2 2.5)")))))

(deftest test-lisp-connection
  (let [repl (SLIMECommonLispREPL. "localhost" 4005)]
    (is (= 3 (eval-lisp repl "(+ 1 2)")))
    (is (= 5 (eval-lisp repl "(* 2 2.5)")))))

(deftest test-bootstrap-sequence
  (let [result (bootstrap-sequence)]
    (is (every? :success result))
    (is (every? :color result))))

(deftest test-srfi-loading
  (load-srfi 2)
  (is (eval-scheme "(null? '())")))
```

---

## Phase 2 Architecture Diagram

```
┌─────────────────────────────────────────────────────────────────┐
│                    UREPL Phase 2 Architecture                    │
└─────────────────────────────────────────────────────────────────┘

                     ┌──────────────────────┐
                     │   WebSocket Server   │
                     │   (src/urepl/        │
                     │    server.clj)       │
                     └──────────┬───────────┘
                                │
                   ┌────────────┼────────────┐
                   │            │            │
           ┌───────▼──────┐ ┌──▼────────┐ ┌─▼──────────┐
           │   Scheme     │ │ Clojure   │ │ Common     │
           │   Connector  │ │ Connector │ │ Lisp Conn. │
           │ (Geiser)     │ │ (nREPL)   │ │ (SLIME)    │
           └────┬─────────┘ └──┬───────┘ └─┬──────────┘
                │              │           │
        ┌───────▼──────────────▼───────────▼────┐
        │   Live REPL Processes                  │
        │   (Racket/Guile, Clojure, CCL/SBCL)   │
        └────────────────────────────────────────┘

        ┌─────────────────────────────────────────────┐
        │         UREPL Coordinator (Phase 1)         │
        │  ┌──────────┬──────────┬──────────┐        │
        │  │ Syntax   │Semantics │ Tests    │        │
        │  │ Agent 1  │ Agent 2  │ Agent 3  │        │
        │  └──────────┴──────────┴──────────┘        │
        └─────────────────────────────────────────────┘

        ┌─────────────────────────────────────────────┐
        │    SRFI Loader & Bootstrap Sequence         │
        │  • Color-guided initialization               │
        │  • Core SRFIs (2,5,26,48,89,135)            │
        │  • Self-hosting meta-interpreter            │
        └─────────────────────────────────────────────┘
```

---

## Phase 2 Implementation Timeline

### Week 1: Server Infrastructure
- [ ] Create WebSocket server (src/urepl/server.clj)
- [ ] Implement health checks and metrics
- [ ] Write integration tests for server
- [ ] Deploy local development server

### Week 2: REPL Connectors
- [ ] Implement Scheme connector (Geiser protocol)
- [ ] Implement Clojure connector (nREPL protocol)
- [ ] Implement Common Lisp connector (SLIME protocol)
- [ ] Test connections with mock REPLs

### Week 3: Bootstrap & SRFIs
- [ ] Create bootstrap sequence with color guidance
- [ ] Implement SRFI 2 (List Predicates)
- [ ] Implement SRFI 5 (Let Syntax)
- [ ] Implement SRFI 26 (Cut/Cute)
- [ ] Implement SRFI 48 (Formatted Output)

### Week 4: Integration & Testing
- [ ] End-to-end test: message → coordinator → REPL → result
- [ ] Test color-guided execution tracing
- [ ] Test cross-dialect SRFI compatibility
- [ ] Create Phase 2 completion documentation

---

## Phase 2 Entry Points

### For End Users

```bash
# Initialize Phase 2
just urepl-phase2-init

# Start UREPL server (WebSocket on port 8765)
just urepl-server-start

# Execute code across all three REPLs
just urepl-cross-dialect "(define x 42)"

# Test Phase 2 infrastructure
just urepl-phase2-test

# Load a specific SRFI
just urepl-load-srfi 26
```

### For Developers

```bash
# Review server implementation
cat src/urepl/server.clj

# Review connector implementation
cat src/urepl/repl-connectors.clj

# Review bootstrap sequence
cat src/urepl/bootstrap.clj

# Run tests with verbose output
just urepl-phase2-test --verbose
```

---

## Phase 2 Success Criteria

✅ **Server starts** without errors on port 8765
✅ **Scheme connector** successfully executes `(+ 1 2)` in Geiser REPL
✅ **Clojure connector** successfully executes `(+ 1 2)` in nREPL
✅ **Common Lisp connector** successfully executes `(+ 1 2)` in SLIME REPL
✅ **Bootstrap sequence** completes with color trace
✅ **SRFI 2** loads and `(null? '())` returns true
✅ **SRFI 5** loads and let forms work in all three dialects
✅ **SRFI 26** loads and cut forms generate closures
✅ **SRFI 48** loads and formatted output works
✅ **Color guidance** deterministic (same seed = same colors)
✅ **End-to-end test**: message through server → coordinator → REPL → result

---

## Integration with Music-Topos

Phase 2 enables UREPL to become a first-class skill in the music-topos agent framework:

```python
# In worlds/urepl_world.py
class UReplWorld(World):
    """Execute UREPL code through live REPLs"""

    def execute_scheme(self, code: str) -> Any:
        """Execute Scheme code with color guidance"""
        message = create_urepl_message("scheme", code)
        result = websocket_client.send(message)
        return parse_result(result)

    def execute_clojure(self, code: str) -> Any:
        """Execute Clojure code with color guidance"""
        message = create_urepl_message("clojure", code)
        result = websocket_client.send(message)
        return parse_result(result)

    def load_srfi(self, number: int) -> bool:
        """Load SRFI and verify in all REPLs"""
        message = create_urepl_message("load_srfi", str(number))
        result = websocket_client.send(message)
        return result.get("success", False)
```

---

## Next Steps After Phase 2

Once Phase 2 is complete:

**Phase 3: CRDT Integration**
- Emacs buffer integration with live editing
- Conflict resolution with color annotations
- Real-time operation tracking

**Phase 4: Full SRFI Coverage**
- Implement all 200+ Scheme Requests for Implementation
- Cross-dialect validation
- Performance optimization

**Phase 5: Meta-Interpreter Verification**
- Proof generation for self-modification
- Formal semantics documentation
- Community release

---

## Files to Create for Phase 2

| File | Lines | Purpose |
|------|-------|---------|
| `src/urepl/server.clj` | 450 | WebSocket server |
| `src/urepl/repl-connectors.clj` | 600 | Multi-language connectors |
| `src/urepl/bootstrap.clj` | 350 | Color-guided initialization |
| `src/urepl/srfi-loader.clj` | 400 | SRFI management |
| `src/urepl/phase2-tests.clj` | 300 | Integration tests |
| `srfi/srfi-2.scm` | 100 | List predicates |
| `srfi/srfi-5.scm` | 150 | Let syntax |
| `srfi/srfi-26.scm` | 200 | Cut/Cute implementation |
| `srfi/srfi-48.scm` | 200 | Formatted output |
| `UREPL_PHASE2_IMPLEMENTATION_GUIDE.md` | 600 | User guide |

**Total**: 3,350+ lines of code and documentation

---

**Phase 2 Status**: Ready to Begin
**Last Updated**: 2025-12-21 22:00 UTC
**Next Review**: After Phase 2 server implementation (Week 1)
