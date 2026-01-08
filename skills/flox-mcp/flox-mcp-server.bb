#!/usr/bin/env bb

;; flox-mcp-server.bb - MCP server for flox CLI operations
;; Trit: 0 (ERGODIC) - Coordinator role
;; Transport: JSON-RPC 2.0 over stdio

(ns flox-mcp-server
  (:require [cheshire.core :as json]
            [babashka.process :as p]
            [clojure.string :as str]))

(def server-info
  {:name "flox-mcp"
   :version "1.0.0"
   :protocolVersion "2024-11-05"})

(def tools
  [{:name "flox_activate"
    :description "Activate a flox environment"
    :inputSchema {:type "object"
                  :properties {:directory {:type "string" :description "Path to environment directory"}
                               :remote {:type "string" :description "Remote environment (user/env)"}}}}
   {:name "flox_search"
    :description "Search for packages in flox catalog"
    :inputSchema {:type "object"
                  :properties {:query {:type "string" :description "Package search query"}}
                  :required ["query"]}}
   {:name "flox_install"
    :description "Install a package into the environment"
    :inputSchema {:type "object"
                  :properties {:package {:type "string" :description "Package name or pkg-path"}}
                  :required ["package"]}}
   {:name "flox_list"
    :description "List installed packages"
    :inputSchema {:type "object"
                  :properties {:directory {:type "string" :description "Environment directory"}}}}
   {:name "flox_services"
    :description "Manage flox services (start/stop/status/restart/logs)"
    :inputSchema {:type "object"
                  :properties {:action {:type "string"
                                        :enum ["start" "stop" "restart" "status" "logs"]
                                        :description "Service action"}
                               :service {:type "string" :description "Specific service name"}}
                  :required ["action"]}}
   {:name "flox_envs"
    :description "List available flox environments"
    :inputSchema {:type "object" :properties {}}}
   {:name "flox_push"
    :description "Push environment to FloxHub"
    :inputSchema {:type "object"
                  :properties {:force {:type "boolean" :description "Force overwrite remote"}}}}
   {:name "flox_pull"
    :description "Pull environment from FloxHub"
    :inputSchema {:type "object"
                  :properties {:remote {:type "string" :description "Remote environment (user/env)"}
                               :force {:type "boolean" :description "Force overwrite local"}
                               :copy {:type "boolean" :description "Copy without remote link"}}}}])

(defn run-flox [& args]
  (let [result (p/shell {:out :string :err :string :continue true}
                        (str/join " " (cons "flox" args)))]
    {:exit (:exit result)
     :stdout (str/trim (:out result))
     :stderr (str/trim (:err result))}))

(defn handle-tool-call [{:keys [name arguments]}]
  (case name
    "flox_activate"
    (let [{:keys [directory remote]} arguments
          args (cond-> ["activate"]
                 directory (conj "-d" directory)
                 remote (conj "-r" remote))]
      (let [result (apply run-flox args)]
        {:content [{:type "text"
                    :text (if (zero? (:exit result))
                            (str "Activated environment\n" (:stdout result))
                            (str "Error: " (:stderr result)))}]}))

    "flox_search"
    (let [{:keys [query]} arguments
          result (run-flox "search" query)]
      {:content [{:type "text"
                  :text (if (zero? (:exit result))
                          (:stdout result)
                          (str "Search error: " (:stderr result)))}]})

    "flox_install"
    (let [{:keys [package]} arguments
          result (run-flox "install" package)]
      {:content [{:type "text"
                  :text (if (zero? (:exit result))
                          (str "Installed: " package "\n" (:stdout result))
                          (str "Install error: " (:stderr result)))}]})

    "flox_list"
    (let [{:keys [directory]} arguments
          args (cond-> ["list"]
                 directory (conj "-d" directory))
          result (apply run-flox args)]
      {:content [{:type "text"
                  :text (if (zero? (:exit result))
                          (:stdout result)
                          (str "List error: " (:stderr result)))}]})

    "flox_services"
    (let [{:keys [action service]} arguments
          args (cond-> ["services" action]
                 service (conj service))
          result (apply run-flox args)]
      {:content [{:type "text"
                  :text (if (zero? (:exit result))
                          (:stdout result)
                          (str "Services error: " (:stderr result)))}]})

    "flox_envs"
    (let [result (run-flox "envs")]
      {:content [{:type "text"
                  :text (if (zero? (:exit result))
                          (:stdout result)
                          (str "Envs error: " (:stderr result)))}]})

    "flox_push"
    (let [{:keys [force]} arguments
          args (cond-> ["push"]
                 force (conj "--force"))
          result (apply run-flox args)]
      {:content [{:type "text"
                  :text (if (zero? (:exit result))
                          (str "Pushed to FloxHub\n" (:stdout result))
                          (str "Push error: " (:stderr result)))}]})

    "flox_pull"
    (let [{:keys [remote force copy]} arguments
          args (cond-> ["pull"]
                 remote (conj remote)
                 force (conj "--force")
                 copy (conj "--copy"))
          result (apply run-flox args)]
      {:content [{:type "text"
                  :text (if (zero? (:exit result))
                          (str "Pulled from FloxHub\n" (:stdout result))
                          (str "Pull error: " (:stderr result)))}]})

    {:content [{:type "text" :text (str "Unknown tool: " name)}]
     :isError true}))

(defn handle-request [{:keys [method params id]}]
  (case method
    "initialize"
    {:jsonrpc "2.0"
     :id id
     :result {:protocolVersion (:protocolVersion server-info)
              :capabilities {:tools {}}
              :serverInfo {:name (:name server-info)
                           :version (:version server-info)}}}

    "notifications/initialized"
    nil

    "tools/list"
    {:jsonrpc "2.0"
     :id id
     :result {:tools tools}}

    "tools/call"
    {:jsonrpc "2.0"
     :id id
     :result (handle-tool-call params)}

    "ping"
    {:jsonrpc "2.0"
     :id id
     :result {}}

    {:jsonrpc "2.0"
     :id id
     :error {:code -32601 :message (str "Method not found: " method)}}))

(defn send-response [response]
  (when response
    (println (json/generate-string response))
    (flush)))

(defn -main []
  (binding [*in* (java.io.BufferedReader. (java.io.InputStreamReader. System/in))]
    (loop []
      (when-let [line (read-line)]
        (when-not (str/blank? line)
          (try
            (let [request (json/parse-string line true)
                  response (handle-request request)]
              (send-response response))
            (catch Exception e
              (send-response {:jsonrpc "2.0"
                              :id nil
                              :error {:code -32700
                                      :message (str "Parse error: " (.getMessage e))}}))))
        (recur)))))

(-main)
