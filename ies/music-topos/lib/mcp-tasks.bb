#!/usr/bin/env bb
;; ╔══════════════════════════════════════════════════════════════════════════════╗
;; ║                                                                              ║
;; ║  MCP-TASKS.BB - Durable State Machines for Cognitive Continuity             ║
;; ║                                                                              ║
;; ║  Implements MCP Tasks specification for self-rewriting capabilities:        ║
;; ║  https://modelcontextprotocol.io/specification/draft/basic/utilities/tasks  ║
;; ║                                                                              ║
;; ╚══════════════════════════════════════════════════════════════════════════════╝

(ns mcp-tasks
  (:require [babashka.json :as json]
            [clojure.string :as str]))

;; ═══════════════════════════════════════════════════════════════════════════════
;; SplitMix64 (matches Gay.jl exactly)
;; ═══════════════════════════════════════════════════════════════════════════════

(def ^:const GOLDEN 0x9e3779b97f4a7c15)
(def ^:const MIX1 0xbf58476d1ce4e5b9)
(def ^:const MIX2 0x94d049bb133111eb)
(def ^:const MASK64 0xFFFFFFFFFFFFFFFF)

(defn u64 [x] (bit-and x MASK64))

(defn splitmix64 [state]
  (let [s (u64 (+ state GOLDEN))
        z (u64 (* (bit-xor s (unsigned-bit-shift-right s 30)) MIX1))
        z (u64 (* (bit-xor z (unsigned-bit-shift-right z 27)) MIX2))
        z (bit-xor z (unsigned-bit-shift-right z 31))]
    [s z]))

;; ═══════════════════════════════════════════════════════════════════════════════
;; TAP States (Balanced Ternary)
;; ═══════════════════════════════════════════════════════════════════════════════

(def TAP-STATES
  {:BACKFILL -1   ; Historical, archived
   :VERIFY    0   ; Verification, neutral
   :LIVE      1}) ; Forward, active

(def TAP-COLORS
  {:BACKFILL {:r 0   :g 0   :b 255}   ; Blue
   :VERIFY   {:r 0   :g 255 :b 0}     ; Green
   :LIVE     {:r 255 :g 0   :b 0}})   ; Red

;; ═══════════════════════════════════════════════════════════════════════════════
;; Task State Machine
;; ═══════════════════════════════════════════════════════════════════════════════

(def TASK-STATES #{:working :input_required :completed :failed :cancelled})
(def TERMINAL-STATES #{:completed :failed :cancelled})

(defn task-to-tap [status]
  (case status
    :working :LIVE
    :input_required :VERIFY
    :completed :BACKFILL
    :failed :BACKFILL
    :cancelled :VERIFY))

(def tasks (atom {}))
(def task-counter (atom 0))

(defn generate-task-id [seed]
  (let [counter (swap! task-counter inc)
        [_ rand-val] (splitmix64 (bit-xor seed counter))]
    (format "%016x-%04d" rand-val counter)))

(defn create-task [seed ttl]
  (let [task-id (generate-task-id seed)
        now (java.time.Instant/now)
        task {:taskId task-id
              :status :working
              :createdAt (.toString now)
              :lastUpdatedAt (.toString now)
              :ttl (or ttl 60000)
              :pollInterval 5000
              :tapState :LIVE
              :color (TAP-COLORS :LIVE)}]
    (swap! tasks assoc task-id task)
    task))

(defn get-task [task-id]
  (get @tasks task-id))

(defn update-task-status! [task-id new-status & [message]]
  (when-let [task (get-task task-id)]
    (when-not (TERMINAL-STATES (:status task))
      (let [now (java.time.Instant/now)
            tap-state (task-to-tap new-status)
            updated (assoc task
                           :status new-status
                           :lastUpdatedAt (.toString now)
                           :tapState tap-state
                           :color (TAP-COLORS tap-state)
                           :statusMessage message)]
        (swap! tasks assoc task-id updated)
        updated))))

(defn cancel-task! [task-id]
  (when-let [task (get-task task-id)]
    (if (TERMINAL-STATES (:status task))
      {:error {:code -32602
               :message (format "Cannot cancel task: already in terminal status '%s'"
                                (name (:status task)))}}
      (update-task-status! task-id :cancelled "Cancelled by request"))))

(defn list-tasks []
  {:tasks (vals @tasks)})

;; ═══════════════════════════════════════════════════════════════════════════════
;; JSON-RPC Handler
;; ═══════════════════════════════════════════════════════════════════════════════

(defn handle-request [{:keys [method params id]}]
  (let [result
        (case method
          ;; Task creation via tools/call with task field
          "tools/call"
          (if-let [task-params (:task params)]
            (let [task (create-task 0x42D (:ttl task-params))]
              {:task task})
            {:error {:code -32600
                     :message "Task augmentation required for tools/call requests"}})

          ;; Task operations
          "tasks/get"
          (if-let [task (get-task (:taskId params))]
            task
            {:error {:code -32602 :message "Task not found"}})

          "tasks/result"
          (if-let [task (get-task (:taskId params))]
            (if (TERMINAL-STATES (:status task))
              {:content [{:type "text"
                          :text (format "Task %s completed with status: %s"
                                        (:taskId task)
                                        (name (:status task)))}]
               :isError (= (:status task) :failed)
               :_meta {"io.modelcontextprotocol/related-task"
                       {:taskId (:taskId task)}}}
              ;; Block and wait (simplified: just return current state)
              {:_meta {"io.modelcontextprotocol/related-task"
                       {:taskId (:taskId task)}}
               :waiting true
               :currentStatus (:status task)})
            {:error {:code -32602 :message "Task not found"}})

          "tasks/list"
          (list-tasks)

          "tasks/cancel"
          (cancel-task! (:taskId params))

          ;; Unknown method
          {:error {:code -32601 :message (str "Method not found: " method)}})]

    (merge {:jsonrpc "2.0" :id id} (if (:error result) result {:result result}))))

;; ═══════════════════════════════════════════════════════════════════════════════
;; MCP Server
;; ═══════════════════════════════════════════════════════════════════════════════

(defn capabilities []
  {:capabilities
   {:tasks {:list {}
            :cancel {}
            :requests {:tools {:call {}}}}}})

(defn serve-mcp []
  (println (json/write-str
            {:jsonrpc "2.0"
             :method "initialize"
             :params (capabilities)}))
  (doseq [line (line-seq (java.io.BufferedReader. *in*))]
    (when-not (str/blank? line)
      (let [request (json/read-str line :key-fn keyword)
            response (handle-request request)]
        (println (json/write-str response))
        (flush)))))

;; ═══════════════════════════════════════════════════════════════════════════════
;; Demo / Entry Point
;; ═══════════════════════════════════════════════════════════════════════════════

(defn demo [seed]
  (println "╔══════════════════════════════════════════════════════════════╗")
  (println "║  MCP Tasks Server - Cognitive Continuity                     ║")
  (println "╚══════════════════════════════════════════════════════════════╝")
  (println)
  (println (format "Seed: 0x%X" seed))
  (println)

  ;; Create demo tasks
  (let [task1 (create-task seed 60000)
        task2 (create-task seed 30000)]
    (println "Created tasks:")
    (println (format "  %s [%s] %s"
                     (:taskId task1)
                     (name (:status task1))
                     (-> task1 :color)))
    (println (format "  %s [%s] %s"
                     (:taskId task2)
                     (name (:status task2))
                     (-> task2 :color)))
    (println)

    ;; Simulate state transitions
    (update-task-status! (:taskId task1) :input_required "Needs approval")
    (println (format "Task 1 → input_required (TAP: VERIFY)"))

    (update-task-status! (:taskId task2) :completed "Done")
    (println (format "Task 2 → completed (TAP: BACKFILL)"))
    (println)

    ;; Show final states
    (println "Final states:")
    (doseq [[id task] @tasks]
      (println (format "  %s: %s → %s"
                       id
                       (name (:status task))
                       (name (:tapState task)))))))

(defn -main [& args]
  (let [arg (first args)
        seed (if arg (parse-long arg) 0x42D)]
    (if (= arg "serve")
      (serve-mcp)
      (demo seed))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
