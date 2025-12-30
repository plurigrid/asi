#!/usr/bin/env bb
;; Generate MCP server entries for Aptos wallets
;; Reads from ~/.aptos/worlds/manifest.json or scans for .key files
;; Merges with existing ~/.mcp.json

(ns generate-mcp-config
  (:require [babashka.fs :as fs]
            [cheshire.core :as json]
            [clojure.string :as str]))

(def home (System/getProperty "user.home"))
(def worlds-dir (str home "/.aptos/worlds"))
(def manifest-path (str worlds-dir "/manifest.json"))
(def mcp-json-path (str home "/.mcp.json"))

;; Find aptos-claude-agent installation
(def aptos-agent-path
  (let [candidates [(str home "/aptos-claude-agent")
                    (str home "/repos/aptos-claude-agent")]]
    (first (filter #(fs/exists? (str % "/dist/mcp/server.js")) candidates))))

(def server-js-path
  (when aptos-agent-path
    (str aptos-agent-path "/dist/mcp/server.js")))

(defn world-letter->name
  "Convert world letter (a-z) to world_X_aptos format"
  [letter]
  (str "world_" letter "_aptos"))

(defn wallet-name->mcp-name
  "Convert wallet name to MCP server name"
  [name]
  (cond
    ;; world_a through world_z
    (re-matches #"world_[a-z]" name)
    (str name "_aptos")
    
    ;; alice, bob, etc -> alice_aptos, bob_aptos
    :else
    (str (str/lower-case name) "_aptos")))

(defn create-mcp-entry
  "Create an MCP server entry for a wallet"
  [{:keys [name key-file private-key network]
    :or {network "mainnet"}}]
  (let [env (cond
              key-file
              {"APTOS_NETWORK" network
               "APTOS_PRIVATE_KEY_FILE" (str "~/.aptos/worlds/" key-file)}
              
              private-key
              {"APTOS_NETWORK" network
               "APTOS_PRIVATE_KEY" private-key}
              
              :else
              {"APTOS_NETWORK" network})]
    {"command" "node"
     "args" [server-js-path]
     "env" env}))

(defn load-manifest
  "Load manifest.json if it exists"
  []
  (when (fs/exists? manifest-path)
    (json/parse-string (slurp manifest-path) true)))

(defn scan-key-files
  "Scan worlds directory for .key files"
  []
  (when (fs/exists? worlds-dir)
    (->> (fs/list-dir worlds-dir)
         (filter #(str/ends-with? (str %) ".key"))
         (map (fn [path]
                (let [filename (fs/file-name path)
                      name (str/replace filename #"\.key$" "")]
                  {:name name
                   :key-file filename})))
         (into []))))

(defn generate-world-entries
  "Generate entries for world_a through world_z"
  [manifest]
  (let [worlds (or (:worlds manifest) [])]
    (for [w worlds
          :let [letter (or (:letter w) 
                          (second (re-find #"world_([a-z])" (:name w ""))))
                mcp-name (if letter
                          (world-letter->name letter)
                          (wallet-name->mcp-name (:name w)))]]
      [mcp-name (create-mcp-entry w)])))

(defn generate-wallet-entries
  "Generate entries for individual wallets (alice, bob, etc)"
  [manifest]
  (let [wallets (or (:wallets manifest) [])]
    (for [w wallets
          :let [mcp-name (wallet-name->mcp-name (:name w))]]
      [mcp-name (create-mcp-entry w)])))

(defn generate-entries-from-key-files
  "Generate entries by scanning .key files"
  []
  (let [key-files (scan-key-files)]
    (for [{:keys [name key-file]} key-files
          :let [mcp-name (wallet-name->mcp-name name)]]
      [mcp-name (create-mcp-entry {:name name :key-file key-file})])))

(defn load-existing-mcp-json
  "Load existing ~/.mcp.json"
  []
  (if (fs/exists? mcp-json-path)
    (json/parse-string (slurp mcp-json-path) true)
    {:mcpServers {}}))

(defn merge-mcp-config
  "Merge new aptos entries with existing config"
  [existing-config new-entries]
  (let [existing-servers (or (:mcpServers existing-config) {})
        new-servers (into {} new-entries)
        merged-servers (merge existing-servers new-servers)]
    {"mcpServers" merged-servers}))

(defn -main
  [& args]
  (when-not server-js-path
    (println "ERROR: aptos-claude-agent not found at:")
    (println "  ~/aptos-claude-agent")
    (println "  ~/repos/aptos-claude-agent")
    (System/exit 1))
  
  (println "Using aptos-claude-agent at:" aptos-agent-path)
  
  (let [manifest (load-manifest)
        entries (if manifest
                  (concat (generate-world-entries manifest)
                          (generate-wallet-entries manifest))
                  (generate-entries-from-key-files))
        entries-vec (vec entries)]
    
    (if (empty? entries-vec)
      (do
        (println "No wallets found in manifest or as .key files")
        (println "Expected manifest at:" manifest-path)
        (println "Or .key files in:" worlds-dir)
        (println "\nTo add wallets, create manifest.json like:")
        (println (json/generate-string
                  {:worlds [{:name "world_a" :letter "a" :key-file "world_a.key"}]
                   :wallets [{:name "alice" :key-file "alice.key"}]}
                  {:pretty true})))
      (let [existing-config (load-existing-mcp-json)
            merged-config (merge-mcp-config existing-config entries-vec)
            output (json/generate-string merged-config {:pretty true})]
        
        (println "\nGenerated" (count entries-vec) "MCP entries:")
        (doseq [[name _] entries-vec]
          (println "  -" name))
        
        (if (some #{"--dry-run" "-n"} args)
          (do
            (println "\n[DRY RUN] Would write to:" mcp-json-path)
            (println output))
          (do
            (spit mcp-json-path output)
            (println "\nUpdated:" mcp-json-path)))))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
