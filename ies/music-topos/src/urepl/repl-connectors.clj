(ns urepl.repl-connectors
  "UREPL Phase 2: Protocol adapters for Scheme, Clojure, and Common Lisp REPLs"
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [clojure.data.json :as json])
  (:import [java.net Socket]
           [java.io PrintWriter BufferedReader InputStreamReader]))

;; ============================================================================
;; Protocol Definitions
;; ============================================================================

(defprotocol SchemeREPL
  "Protocol for Scheme REPL (Geiser protocol)"
  (connect-scheme [this host port])
  (eval-scheme [this code] "Evaluate Scheme code")
  (disconnect-scheme [this] "Disconnect from REPL"))

(defprotocol ClojureREPL
  "Protocol for Clojure REPL (nREPL protocol)"
  (connect-clojure [this host port])
  (eval-clojure [this code] "Evaluate Clojure code")
  (disconnect-clojure [this] "Disconnect from REPL"))

(defprotocol CommonLispREPL
  "Protocol for Common Lisp REPL (SLIME protocol)"
  (connect-lisp [this host port])
  (eval-lisp [this code] "Evaluate Common Lisp code")
  (disconnect-lisp [this] "Disconnect from REPL"))

;; ============================================================================
;; Scheme REPL Connector (Geiser Protocol)
;; ============================================================================

(defrecord GeiserSchemeREPL [host port socket writer reader timeout-ms]
  SchemeREPL
  (connect-scheme [this h p]
    (try
      (let [sock (Socket. h p)
            out (PrintWriter. (.getOutputStream sock) true)
            in (BufferedReader. (InputStreamReader. (.getInputStream sock)))]
        (println (format "🔗 Connected to Scheme REPL at %s:%d" h p))
        (assoc this
          :host h
          :port p
          :socket sock
          :writer out
          :reader in
          :timeout-ms 5000))
      (catch Exception e
        (throw (Exception. (format "Failed to connect to Scheme REPL: %s" (.getMessage e)))))))

  (eval-scheme [this code]
    (if (and socket reader writer)
      (try
        ;; Send code using Geiser protocol
        ;; Geiser expects: (:eval code :rep-id N)
        (let [geiser-msg (format "(:eval \"%s\" :rep-id 1)" (escape-string code))
              response (atom nil)]

          ;; Write to REPL
          (.println writer geiser-msg)
          (.flush writer)

          ;; Read response with timeout
          (let [start-time (System/currentTimeMillis)
                read-fn (fn []
                  (when (.ready reader)
                    (try
                      (.readLine reader)
                      (catch Exception e nil))))]

            (loop []
              (if-let [line (read-fn)]
                (do
                  (reset! response line)
                  (parse-geiser-response line))

                (if (< (- (System/currentTimeMillis) start-time) timeout-ms)
                  (do
                    (Thread/sleep 10)
                    (recur))
                  (throw (Exception. "Scheme REPL timeout"))))))

          (or @response {:error "No response from Scheme REPL"}))

        (catch Exception e
          {:error (format "Scheme eval error: %s" (.getMessage e))}))

      {:error "Scheme REPL not connected"}))

  (disconnect-scheme [this]
    (when writer (.close writer))
    (when reader (.close reader))
    (when socket (.close socket))
    (println "Disconnected from Scheme REPL")
    (assoc this :socket nil :reader nil :writer nil)))

;; ============================================================================
;; Clojure REPL Connector (nREPL Protocol)
;; ============================================================================

(defrecord NREPLClojureREPL [host port socket writer reader message-id]
  ClojureREPL
  (connect-clojure [this h p]
    (try
      (let [sock (Socket. h p)
            out (PrintWriter. (.getOutputStream sock) true)
            in (BufferedReader. (InputStreamReader. (.getInputStream sock)))]
        (println (format "🔗 Connected to Clojure REPL at %s:%d" h p))
        (assoc this
          :host h
          :port p
          :socket sock
          :writer out
          :reader in
          :message-id (atom 1)))
      (catch Exception e
        (throw (Exception. (format "Failed to connect to Clojure REPL: %s" (.getMessage e)))))))

  (eval-clojure [this code]
    (if (and socket reader writer message-id)
      (try
        ;; nREPL uses bencode protocol; simplified version sends code as-is
        (let [msg-num (swap! message-id inc)
              nrepl-msg (format "(eval \"%s\" :msg-id %d)" (escape-string code) msg-num)
              response (atom nil)]

          ;; Send code
          (.println writer nrepl-msg)
          (.flush writer)

          ;; Read response
          (loop [attempts 0]
            (if (< attempts 50)  ; 50 * 100ms = 5 second timeout
              (if-let [line (try
                            (when (.ready reader)
                              (.readLine reader))
                            (catch Exception _ nil))]
                (do
                  (reset! response line)
                  (parse-nrepl-response line))

                (do
                  (Thread/sleep 100)
                  (recur (inc attempts))))

              (throw (Exception. "Clojure REPL timeout"))))

          (or @response {:error "No response from Clojure REPL"}))

        (catch Exception e
          {:error (format "Clojure eval error: %s" (.getMessage e))}))

      {:error "Clojure REPL not connected"}))

  (disconnect-clojure [this]
    (when writer (.close writer))
    (when reader (.close reader))
    (when socket (.close socket))
    (println "Disconnected from Clojure REPL")
    (assoc this :socket nil :reader nil :writer nil)))

;; ============================================================================
;; Common Lisp REPL Connector (SLIME Protocol)
;; ============================================================================

(defrecord SLIMECommonLispREPL [host port socket writer reader counter]
  CommonLispREPL
  (connect-lisp [this h p]
    (try
      (let [sock (Socket. h p)
            out (PrintWriter. (.getOutputStream sock) true)
            in (BufferedReader. (InputStreamReader. (.getInputStream sock)))]
        (println (format "🔗 Connected to Common Lisp REPL at %s:%d" h p))
        (assoc this
          :host h
          :port p
          :socket sock
          :writer out
          :reader in
          :counter (atom 1)))
      (catch Exception e
        (throw (Exception. (format "Failed to connect to Common Lisp REPL: %s" (.getMessage e)))))))

  (eval-lisp [this code]
    (if (and socket reader writer counter)
      (try
        ;; SLIME protocol uses S-expression format
        (let [counter-val (swap! counter inc)
              slime-msg (format "(:emacs-rex (swank:eval-and-grab-output \"%s\") nil %d)"
                               (escape-string code) counter-val)
              response (atom nil)]

          ;; Send code
          (.println writer slime-msg)
          (.flush writer)

          ;; Read response
          (loop [attempts 0]
            (if (< attempts 50)
              (if-let [line (try
                            (when (.ready reader)
                              (.readLine reader))
                            (catch Exception _ nil))]
                (do
                  (reset! response line)
                  (parse-slime-response line))

                (do
                  (Thread/sleep 100)
                  (recur (inc attempts))))

              (throw (Exception. "Common Lisp REPL timeout"))))

          (or @response {:error "No response from Common Lisp REPL"}))

        (catch Exception e
          {:error (format "Common Lisp eval error: %s" (.getMessage e))}))

      {:error "Common Lisp REPL not connected"}))

  (disconnect-lisp [this]
    (when writer (.close writer))
    (when reader (.close reader))
    (when socket (.close socket))
    (println "Disconnected from Common Lisp REPL")
    (assoc this :socket nil :reader nil :writer nil)))

;; ============================================================================
;; Response Parsers
;; ============================================================================

(defn parse-geiser-response [response-text]
  "Parse Geiser protocol response"
  (try
    (if (str/starts-with? response-text "(:return")
      {:success true
       :value (second (read-string response-text))}
      {:success false
       :error response-text})
    (catch Exception e
      {:success false
       :error (str "Parse error: " (.getMessage e))})))

(defn parse-nrepl-response [response-text]
  "Parse nREPL protocol response"
  (try
    (if (str/includes? response-text ":value")
      {:success true
       :value (extract-nrepl-value response-text)}
      {:success false
       :error response-text})
    (catch Exception e
      {:success false
       :error (str "Parse error: " (.getMessage e))})))

(defn parse-slime-response [response-text]
  "Parse SLIME protocol response"
  (try
    (if (str/starts-with? response-text "(:return")
      {:success true
       :value (second (read-string response-text))}
      {:success false
       :error response-text})
    (catch Exception e
      {:success false
       :error (str "Parse error: " (.getMessage e))})))

;; ============================================================================
;; Utility Functions
;; ============================================================================

(defn escape-string [s]
  "Escape special characters in strings for REPL protocols"
  (-> s
      (str/replace "\\" "\\\\")
      (str/replace "\"" "\\\"")))

(defn extract-nrepl-value [response-text]
  "Extract value from nREPL response"
  (try
    (let [lines (str/split-lines response-text)
          value-line (some #(when (str/includes? % ":value") %) lines)]
      (if value-line
        (second (str/split value-line #":value\s+"))
        nil))
    (catch Exception _ nil)))

;; ============================================================================
;; Global REPL Instances
;; ============================================================================

(def scheme-repl
  "Global Scheme REPL connection"
  (atom (GeiserSchemeREPL. nil nil nil nil nil 5000)))

(def clojure-repl
  "Global Clojure REPL connection"
  (atom (NREPLClojureREPL. nil nil nil nil nil (atom 1))))

(def lisp-repl
  "Global Common Lisp REPL connection"
  (atom (SLIMECommonLispREPL. nil nil nil nil nil (atom 1))))

;; ============================================================================
;; Initialization
;; ============================================================================

(defn init-scheme-repl
  "Initialize Scheme REPL connection (optional)"
  [& {:keys [host port] :or {host "localhost" port 4005}}]
  (try
    (swap! scheme-repl #(connect-scheme % host port))
    {:success true :repl :scheme :host host :port port}
    (catch Exception e
      (println (format "⚠️  Scheme REPL unavailable: %s" (.getMessage e)))
      {:success false :error (.getMessage e)})))

(defn init-clojure-repl
  "Initialize Clojure REPL connection (optional)"
  [& {:keys [host port] :or {host "localhost" port 7888}}]
  (try
    (swap! clojure-repl #(connect-clojure % host port))
    {:success true :repl :clojure :host host :port port}
    (catch Exception e
      (println (format "⚠️  Clojure REPL unavailable: %s" (.getMessage e)))
      {:success false :error (.getMessage e)})))

(defn init-lisp-repl
  "Initialize Common Lisp REPL connection (optional)"
  [& {:keys [host port] :or {host "localhost" port 4005}}]
  (try
    (swap! lisp-repl #(connect-lisp % host port))
    {:success true :repl :lisp :host host :port port}
    (catch Exception e
      (println (format "⚠️  Common Lisp REPL unavailable: %s" (.getMessage e)))
      {:success false :error (.getMessage e)})))

(defn init-all-repls
  "Initialize all three REPL connections (graceful degradation)"
  []
  (println "Attempting to connect to live REPLs...")
  (let [results [
    (init-scheme-repl)
    (init-clojure-repl)
    (init-lisp-repl)]]
    (println (format "Connected: %d/3 REPLs available"
      (count (filter :success results))))
    results))

(defn get-repl-status
  "Get status of all REPL connections"
  []
  {:scheme (if (:socket @scheme-repl) :connected :disconnected)
   :clojure (if (:socket @clojure-repl) :connected :disconnected)
   :lisp (if (:socket @lisp-repl) :connected :disconnected)})

;; ============================================================================
;; Evaluation Entry Points
;; ============================================================================

(defn eval-scheme-code
  "Evaluate code in Scheme REPL"
  [code]
  (eval-scheme @scheme-repl code))

(defn eval-clojure-code
  "Evaluate code in Clojure REPL"
  [code]
  (eval-clojure @clojure-repl code))

(defn eval-lisp-code
  "Evaluate code in Common Lisp REPL"
  [code]
  (eval-lisp @lisp-repl code))

(defn eval-cross-dialect
  "Evaluate code across all available REPLs"
  [code]
  {:scheme (eval-scheme-code code)
   :clojure (eval-clojure-code code)
   :lisp (eval-lisp-code code)})

;; ============================================================================
;; Development and Testing
;; ============================================================================

(comment
  ;; Connect to Scheme REPL
  (init-scheme-repl :host "localhost" :port 4005)
  (eval-scheme-code "(+ 1 2 3)")

  ;; Connect to Clojure REPL
  (init-clojure-repl :host "localhost" :port 7888)
  (eval-clojure-code "(+ 1 2 3)")

  ;; Connect to Common Lisp REPL
  (init-lisp-repl :host "localhost" :port 4005)
  (eval-lisp-code "(+ 1 2 3)")

  ;; Check all statuses
  (get-repl-status)

  ;; Disconnect all
  (swap! scheme-repl disconnect-scheme)
  (swap! clojure-repl disconnect-clojure)
  (swap! lisp-repl disconnect-lisp)
)
