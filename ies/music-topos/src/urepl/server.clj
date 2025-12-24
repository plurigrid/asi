(ns urepl.server
  "UREPL Phase 2: WebSocket Server for live REPL connections"
  (:require [ring.adapter.jetty :as jetty]
            [ring.util.response :refer [response]]
            [compojure.core :refer [defroutes GET POST]]
            [compojure.route :as route]
            [ring.middleware.json :refer [wrap-json-body wrap-json-response]]
            [clojure.core.async :as async]
            [clojure.data.json :as json]
            [clojure.instant :as instant]
            [urepl.coordinator :as coordinator]
            [urepl.repl-connectors :as connectors]
            [urepl.bootstrap :as bootstrap]
            [urepl.srfi-loader :as srfi])
  (:import [java.time Instant]
           [java.util UUID]))

;; ============================================================================
;; Server State Management
;; ============================================================================

(def server-state
  "Global server state: connections, metrics, cache"
  (atom {
    :started-at (Instant/now)
    :connections {}
    :message-count 0
    :error-count 0
    :color-trace []
    :repl-status {:scheme :disconnected
                  :clojure :disconnected
                  :lisp :disconnected}
    :loaded-srfis #{}
  }))

(defn update-metrics [metric-key delta]
  "Update server metrics atomically"
  (swap! server-state
    (fn [state]
      (update state metric-key (fnil + 0) delta))))

(defn record-error [error-msg]
  "Record error in server state"
  (update-metrics :error-count 1)
  (swap! server-state assoc :last-error error-msg :last-error-at (Instant/now)))

;; ============================================================================
;; UREPL Message Handlers
;; ============================================================================

(defn process-urepl-message
  "Process incoming UREPL message through coordinator"
  [message]
  (try
    (update-metrics :message-count 1)

    (let [message-id (UUID/randomUUID)
          message-type (:type message)
          code (:code message)
          seed (get message :seed 42)

          ;; Route to appropriate handler
          result (case message-type
                   "execute" (coordinator/execute-code code seed)
                   "evaluate" (coordinator/evaluate-code code seed)
                   "load-srfi" (srfi/load-srfi (:srfi-number message))
                   "bootstrap" (bootstrap/run-bootstrap-sequence)
                   "status" (get @server-state :repl-status)
                   {:error "Unknown message type"})]

      ;; Construct response with color trace
      {:id message-id
       :type (str message-type "-response")
       :timestamp (Instant/now)
       :success true
       :result result
       :color-trace (get @server-state :color-trace)
       :duration-ms (get result :duration-ms 0)})

    (catch Exception e
      (record-error (.getMessage e))
      {:id (UUID/randomUUID)
       :timestamp (Instant/now)
       :success false
       :error (.getMessage e)
       :error-type (class e)})))

;; ============================================================================
;; WebSocket Connection Handler
;; ============================================================================

(def ws-connections
  "Map of active WebSocket connections"
  (atom {}))

(defn handle-websocket-message
  "Handle incoming WebSocket message"
  [connection-id message-text]
  (try
    (let [parsed (json/parse-string message-text true)
          response (process-urepl-message parsed)
          response-text (json/generate-string response)]

      ;; Record connection activity
      (swap! ws-connections
        (fn [conns]
          (assoc-in conns [connection-id :last-activity] (Instant/now))))

      response-text)

    (catch Exception e
      (json/generate-string
        {:success false
         :error (.getMessage e)
         :timestamp (Instant/now)}))))

;; ============================================================================
;; HTTP Endpoints
;; ============================================================================

(defn index-handler [request]
  "Root endpoint - welcome message"
  {:status 200
   :headers {"content-type" "text/plain"}
   :body (str "UREPL WebSocket Server v0.2.0\n"
              "Endpoints:\n"
              "  POST /urepl/execute - Execute code (JSON body)\n"
              "  GET  /health - Health check\n"
              "  GET  /status - Server status\n"
              "  POST /urepl/srfi/:number - Load SRFI\n"
              "  POST /urepl/bootstrap - Run bootstrap sequence\n")})

(defn health-handler [request]
  "Health check endpoint"
  {:status 200
   :headers {"content-type" "application/json"}
   :body (json/generate-string
    {:status "ok"
     :timestamp (Instant/now)
     :uptime-ms (let [started (get @server-state :started-at)]
                  (- (.toEpochMilli (Instant/now))
                     (.toEpochMilli started)))})})

(defn status-handler [request]
  "Server status endpoint"
  {:status 200
   :headers {"content-type" "application/json"}
   :body (json/generate-string
    {:message-count (get @server-state :message-count 0)
     :error-count (get @server-state :error-count 0)
     :repl-status (get @server-state :repl-status)
     :loaded-srfis (vec (get @server-state :loaded-srfis))
     :active-connections (count @ws-connections)
     :timestamp (Instant/now)})})

(defn execute-handler [request]
  "Execute UREPL code - POST endpoint"
  (try
    (let [message (:json-params request)
          response (process-urepl-message message)]
      {:status 200
       :headers {"content-type" "application/json"}
       :body (json/generate-string response)})

    (catch Exception e
      (record-error (.getMessage e))
      {:status 500
       :headers {"content-type" "application/json"}
       :body (json/generate-string
        {:success false
         :error (.getMessage e)
         :timestamp (Instant/now)})})))

(defn bootstrap-handler [request]
  "Run bootstrap sequence - POST endpoint"
  (try
    (let [result (bootstrap/run-bootstrap-sequence)]
      {:status 200
       :headers {"content-type" "application/json"}
       :body (json/generate-string result)})

    (catch Exception e
      (record-error (.getMessage e))
      {:status 500
       :headers {"content-type" "application/json"}
       :body (json/generate-string
        {:success false
         :error (.getMessage e)})})))

(defn srfi-handler [request]
  "Load SRFI by number - POST endpoint"
  (try
    (let [srfi-num (Integer/parseInt (get-in request [:route-params :number]))
          result (srfi/load-srfi srfi-num)]
      {:status 200
       :headers {"content-type" "application/json"}
       :body (json/generate-string result)})

    (catch NumberFormatException e
      {:status 400
       :headers {"content-type" "application/json"}
       :body (json/generate-string {:error "Invalid SRFI number"})})

    (catch Exception e
      (record-error (.getMessage e))
      {:status 500
       :headers {"content-type" "application/json"}
       :body (json/generate-string {:error (.getMessage e)})})))

;; ============================================================================
;; Route Definitions
;; ============================================================================

(defroutes routes
  (GET "/" [] index-handler)
  (GET "/health" [] health-handler)
  (GET "/status" [] status-handler)
  (POST "/urepl/execute" [] execute-handler)
  (POST "/urepl/bootstrap" [] bootstrap-handler)
  (POST "/urepl/srfi/:number" [] srfi-handler)
  (route/not-found "Endpoint not found"))

;; ============================================================================
;; Ring Middleware Stack
;; ============================================================================

(def app
  "Complete Ring application with all middleware"
  (-> routes
      (wrap-json-body {:keywords? true})
      (wrap-json-response)))

;; ============================================================================
;; Server Lifecycle
;; ============================================================================

(defn start-server
  "Start UREPL WebSocket server on specified port"
  [port]
  (println (format "🚀 UREPL Server starting on port %d" port))
  (println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")

  ;; Initialize REPL connectors
  (println "🔗 Initializing REPL connectors...")
  (try
    (connectors/init-all-repls)
    (println "  ✓ Scheme REPL (Geiser)")
    (println "  ✓ Clojure REPL (nREPL)")
    (println "  ✓ Common Lisp REPL (SLIME)")
    (catch Exception e
      (println (format "  ⚠️  Warning: %s" (.getMessage e)))))

  ;; Start bootstrap sequence
  (println "🎨 Running bootstrap sequence...")
  (try
    (bootstrap/run-bootstrap-sequence)
    (println "  ✓ Bootstrap complete")
    (catch Exception e
      (println (format "  ⚠️  Bootstrap skipped: %s" (.getMessage e)))))

  ;; Start Jetty server
  (println (format "🌐 Starting HTTP server on http://localhost:%d" port))
  (println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")

  (let [server (jetty/run-jetty app
                {:port port
                 :join? false})]

    (println "✅ Server ready!")
    (println (format "   POST http://localhost:%d/urepl/execute (with JSON body)" port))
    (println (format "   GET  http://localhost:%d/health" port))
    (println (format "   GET  http://localhost:%d/status" port))
    (println "")

    server))

(defn stop-server [server]
  "Stop running server"
  (println "Stopping UREPL Server...")
  (.stop server)
  (println "Server stopped"))

(defn -main
  "Command-line entry point"
  [& args]
  (let [port (if (seq args) (Integer/parseInt (first args)) 8765)]
    (start-server port)
    (while true
      (Thread/sleep 1000))))

;; ============================================================================
;; REPL Development
;; ============================================================================

(comment
  ;; Start server in REPL
  (def my-server (start-server 8765))

  ;; Test endpoint
  (require '[clj-http.client :as http])
  (http/post "http://localhost:8765/urepl/execute"
    {:content-type :json
     :body (json/generate-string
      {:type "execute"
       :code "(+ 1 2 3)"
       :seed 42})})

  ;; Check status
  (http/get "http://localhost:8765/status")

  ;; Stop server
  (stop-server my-server)
)
