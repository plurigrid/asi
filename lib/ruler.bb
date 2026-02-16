#!/usr/bin/env bb
;; ruler.bb — Babashka implementation of Ruler skill/MCP propagation
;;
;; Propagates skills and MCP configurations to 30+ coding assistants
;; Based on: intellectronica/ruler + skillcreatorai/Ai-Agent-Skills
;;
;; Commands:
;;   ruler sync           Sync all skills and MCP configs to agents
;;   ruler mcp-list       List MCP servers from ruler.toml
;;   ruler skills-list    List available skills
;;   ruler agent-configs  Show generated agent configs
;;   ruler claude-json    Generate claude mcp-config.json
;;   ruler codex-json     Generate codex mcp.json

(ns ruler
  (:require [babashka.fs :as fs]
            [babashka.process :as p]
            [cheshire.core :as json]
            [clojure.string :as str]
            [clojure.edn :as edn]))

;; ═══════════════════════════════════════════════════════════════════════════
;; TOML Parser (minimal, sufficient for ruler.toml)
;; ═══════════════════════════════════════════════════════════════════════════

(defn parse-toml-value [v]
  (let [v (str/trim v)]
    (cond
      ;; Boolean
      (= v "true") true
      (= v "false") false
      ;; Quoted string
      (and (str/starts-with? v "\"") (str/ends-with? v "\""))
      (subs v 1 (dec (count v)))
      ;; Array
      (str/starts-with? v "[")
      (let [inner (-> v (subs 1) (str/replace #"\]$" "") str/trim)]
        (if (str/blank? inner)
          []
          (mapv #(parse-toml-value (str/trim %))
                (str/split inner #","))))
      ;; Inline table { k = v, ... }
      (str/starts-with? v "{")
      (let [inner (-> v (subs 1) (str/replace #"\}$" "") str/trim)]
        (if (str/blank? inner)
          {}
          (into {}
            (for [pair (str/split inner #",")]
              (let [[k val] (str/split pair #"=" 2)]
                [(str/trim k) (parse-toml-value (str/trim val))])))))
      ;; Environment variable reference
      (str/starts-with? v "${")
      (let [env-var (-> v (subs 2) (str/replace #"\}$" ""))]
        (or (System/getenv env-var) v))
      ;; Number
      (re-matches #"-?\d+\.?\d*" v)
      (if (str/includes? v ".")
        (Double/parseDouble v)
        (Long/parseLong v))
      ;; Default string
      :else v)))

(defn parse-toml [content]
  "Parse TOML content into nested map."
  (let [lines (str/split-lines content)
        result (atom {})
        current-section (atom [])]
    (doseq [line lines]
      (let [trimmed (str/trim line)]
        (cond
          ;; Comment or empty
          (or (str/blank? trimmed) (str/starts-with? trimmed "#"))
          nil

          ;; Section header [foo.bar.baz]
          (and (str/starts-with? trimmed "[") (str/ends-with? trimmed "]"))
          (let [section (-> trimmed (subs 1) (subs 0 (dec (count (subs trimmed 1)))))
                parts (str/split section #"\.")]
            (reset! current-section (vec parts)))

          ;; Key = value
          (str/includes? trimmed "=")
          (let [[k v] (str/split trimmed #"=" 2)
                k (str/trim k)
                v (parse-toml-value (str/trim v))
                path (conj @current-section k)]
            (swap! result assoc-in path v)))))
    @result))

(defn load-ruler-toml [dir]
  "Load .ruler/ruler.toml from directory."
  (let [toml-path (fs/path dir ".ruler" "ruler.toml")]
    (when (fs/exists? toml-path)
      (parse-toml (slurp (str toml-path))))))

;; ═══════════════════════════════════════════════════════════════════════════
;; MCP Config Generation
;; ═══════════════════════════════════════════════════════════════════════════

(defn mcp-server->claude-format [name server]
  "Convert ruler MCP server config to Claude format."
  {:command (get server "command")
   :args (get server "args" [])
   :env (get server "env" {})})

(defn mcp-server->codex-format [name server]
  "Convert ruler MCP server config to Codex format."
  (let [env (get server "env" {})]
    (cond-> {:command (get server "command")
             :args (get server "args" [])}
      (seq env) (assoc :env env))))

(defn generate-claude-mcp-config [ruler-config]
  "Generate Claude MCP config JSON."
  (let [mcp-servers (get ruler-config "mcp_servers" {})]
    {:mcpServers
     (into {}
       (for [[name server] mcp-servers]
         [(keyword name) (mcp-server->claude-format name server)]))}))

(defn generate-codex-mcp-config [ruler-config]
  "Generate Codex MCP config JSON."
  (let [mcp-servers (get ruler-config "mcp_servers" {})]
    {:mcpServers
     (into {}
       (for [[name server] mcp-servers]
         [(keyword name) (mcp-server->codex-format name server)]))}))

;; ═══════════════════════════════════════════════════════════════════════════
;; Skills Discovery
;; ═══════════════════════════════════════════════════════════════════════════

(defn find-skills [ruler-dir]
  "Find all skills in .ruler/skills/."
  (let [skills-dir (fs/path ruler-dir ".ruler" "skills")]
    (when (fs/directory? skills-dir)
      (->> (fs/list-dir skills-dir)
           (filter fs/directory?)
           (map (fn [d]
                  (let [skill-md (fs/path d "SKILL.md")]
                    (when (fs/exists? skill-md)
                      {:name (str (fs/file-name d))
                       :path (str d)
                       :skill-md (str skill-md)}))))
           (filter some?)
           vec))))

(defn parse-skill-frontmatter [skill-md-path]
  "Parse SKILL.md frontmatter."
  (let [content (slurp skill-md-path)]
    (when (str/starts-with? content "---")
      (let [parts (str/split content #"---" 3)]
        (when (>= (count parts) 3)
          (let [yaml-str (second parts)
                lines (str/split-lines yaml-str)]
            (into {}
              (for [line lines
                    :let [trimmed (str/trim line)]
                    :when (and (not (str/blank? trimmed))
                               (str/includes? trimmed ":"))]
                (let [[k v] (str/split trimmed #":" 2)]
                  [(str/trim k) (str/trim v)])))))))))

;; ═══════════════════════════════════════════════════════════════════════════
;; Agent Config Generation
;; ═══════════════════════════════════════════════════════════════════════════

(defn generate-claude-md [ruler-config skills]
  "Generate CLAUDE.md content."
  (str "# CLAUDE.md\n\n"
       "Auto-generated by Ruler\n\n"
       "## Available Skills\n\n"
       (str/join "\n"
         (for [skill skills]
           (str "- **" (:name skill) "**: " (fs/path (:path skill) "SKILL.md"))))
       "\n\n"
       "## MCP Servers\n\n"
       (str/join "\n"
         (for [[name server] (get ruler-config "mcp_servers" {})]
           (str "- **" name "**: " (get server "description" "No description"))))))

(defn generate-agents-md [ruler-config skills]
  "Generate AGENTS.md content (for Amp, Cursor, Copilot)."
  (str "# AGENTS.md\n\n"
       "Multi-agent configuration generated by Ruler\n\n"
       "## Skills\n\n"
       (str/join "\n"
         (for [skill skills]
           (str "- " (:name skill))))
       "\n"))

;; ═══════════════════════════════════════════════════════════════════════════
;; Claude CLI Integration
;; ═══════════════════════════════════════════════════════════════════════════

(defn claude-mcp-add [name server]
  "Add MCP server via claude mcp add command."
  (let [cmd (get server "command")
        args (get server "args" [])
        env (get server "env" {})
        env-flags (mapcat (fn [[k v]] ["-e" (str k "=" v)]) env)
        full-cmd (concat ["claude" "mcp" "add" name]
                         env-flags
                         ["--"]
                         [cmd]
                         args)]
    (println (format "  Adding: %s" name))
    (try
      (let [result (p/shell {:out :string :err :string} (str/join " " full-cmd))]
        (when (zero? (:exit result))
          (println (format "    ✓ Added %s" name))))
      (catch Exception e
        (println (format "    ✗ Failed: %s" (.getMessage e)))))))

(defn codex-mcp-add [name server]
  "Add MCP server via codex mcp add command."
  (let [cmd (get server "command")
        args (get server "args" [])
        env (get server "env" {})
        env-flags (mapcat (fn [[k v]] ["--env" (str k "=" v)]) env)
        full-cmd (concat ["codex" "mcp" "add" name]
                         env-flags
                         ["--"]
                         [cmd]
                         args)]
    (println (format "  Adding to Codex: %s" name))
    (try
      (let [result (p/shell {:out :string :err :string} (str/join " " full-cmd))]
        (when (zero? (:exit result))
          (println (format "    ✓ Added %s to Codex" name))))
      (catch Exception e
        (println (format "    ✗ Failed: %s" (.getMessage e)))))))

;; ═══════════════════════════════════════════════════════════════════════════
;; GF(3) Bisimulation
;; ═══════════════════════════════════════════════════════════════════════════

(def GF3-POLARITIES
  {"PLUS" 1
   "ERGODIC" 0
   "MINUS" -1})

(defn agent-polarity [ruler-config agent-name]
  "Get GF(3) polarity for an agent."
  (let [polarity-str (get-in ruler-config ["bisimulation" "agents" agent-name] "ERGODIC")]
    (get GF3-POLARITIES polarity-str 0)))

(defn bisimulation-balance [ruler-config]
  "Check if agent polarities are balanced (∑ ≡ 0 mod 3)."
  (let [agents (get-in ruler-config ["bisimulation" "agents"] {})
        sum (reduce + (map #(get GF3-POLARITIES % 0) (vals agents)))]
    {:sum sum
     :balanced (zero? (mod sum 3))
     :agents (into {} (for [[k v] agents] [k (get GF3-POLARITIES v 0)]))}))

;; ═══════════════════════════════════════════════════════════════════════════
;; Sync Command
;; ═══════════════════════════════════════════════════════════════════════════

(defn sync-to-agents [ruler-dir]
  "Sync ruler config to all enabled agents."
  (let [config (load-ruler-toml ruler-dir)
        skills (find-skills ruler-dir)
        agents (get config "agents" {})]
    (println "=== Ruler Sync ===\n")
    (println (format "Found %d skills" (count skills)))
    (println (format "Found %d MCP servers" (count (get config "mcp_servers" {}))))
    (println)

    ;; Generate agent configs
    (doseq [[agent-name agent-config] agents]
      (when (get agent-config "enabled" false)
        (println (format "Syncing to: %s" agent-name))
        (let [output-path (get agent-config "output_path")]
          (when output-path
            (case agent-name
              "claude" (spit (fs/path ruler-dir output-path)
                             (generate-claude-md config skills))
              "amp" (spit (fs/path ruler-dir output-path)
                          (generate-agents-md config skills))
              "cursor" (spit (fs/path ruler-dir output-path)
                             (generate-agents-md config skills))
              "copilot" (spit (fs/path ruler-dir output-path)
                              (generate-agents-md config skills))
              "codex" (spit (fs/path ruler-dir output-path)
                            (generate-claude-md config skills))
              nil)
            (println (format "  ✓ Generated %s" output-path))))))

    ;; MCP sync
    (when (get-in config ["mcp" "enabled"])
      (println "\nSyncing MCP servers...")
      (let [mcp-servers (get config "mcp_servers" {})]
        (doseq [[name server] mcp-servers]
          (println (format "  %s: %s" name (get server "description" "-"))))))

    ;; Bisimulation check
    (when (get-in config ["bisimulation" "enabled"])
      (println "\n=== GF(3) Bisimulation ===")
      (let [balance (bisimulation-balance config)]
        (println (format "Agent polarities: %s" (:agents balance)))
        (println (format "Sum: %d" (:sum balance)))
        (println (format "Balanced: %s" (:balanced balance)))))))

;; ═══════════════════════════════════════════════════════════════════════════
;; NBB Interface Capture (for Node Babashka interop)
;; ═══════════════════════════════════════════════════════════════════════════

(defn nbb-interface-schema []
  "Return schema for NBB operation interfaces."
  {:tools {:sync {:description "Sync ruler config to agents"
                  :input-schema {:type "object"
                                 :properties {:dir {:type "string"}}}}
           :mcp-list {:description "List MCP servers"
                      :input-schema {:type "object"}}
           :skills-list {:description "List available skills"
                         :input-schema {:type "object"}}
           :claude-json {:description "Generate Claude MCP config"
                         :input-schema {:type "object"}}
           :codex-json {:description "Generate Codex MCP config"
                        :input-schema {:type "object"}}}
   :resources [{:uri "ruler://config"
                :name "Ruler Configuration"
                :mimeType "application/toml"}
               {:uri "ruler://skills"
                :name "Available Skills"
                :mimeType "application/json"}
               {:uri "ruler://mcp-servers"
                :name "MCP Servers"
                :mimeType "application/json"}]})

(defn nbb-handle-tool [tool-name args dir]
  "Handle NBB tool invocation."
  (let [config (load-ruler-toml dir)]
    (case tool-name
      "sync" (do (sync-to-agents dir) {:status "ok"})
      "mcp-list" {:servers (get config "mcp_servers" {})}
      "skills-list" {:skills (find-skills dir)}
      "claude-json" (generate-claude-mcp-config config)
      "codex-json" (generate-codex-mcp-config config)
      {:error (str "Unknown tool: " tool-name)})))

;; ═══════════════════════════════════════════════════════════════════════════
;; CLI
;; ═══════════════════════════════════════════════════════════════════════════

(defn -main [& args]
  (let [cmd (first args)
        dir (or (second args) ".")]
    (case cmd
      "sync" (sync-to-agents dir)

      "mcp-list" (let [config (load-ruler-toml dir)]
                   (println "=== MCP Servers ===\n")
                   (doseq [[name server] (get config "mcp_servers" {})]
                     (println (format "  %s:" name))
                     (println (format "    command: %s %s"
                                      (get server "command")
                                      (str/join " " (get server "args" []))))
                     (println (format "    description: %s" (get server "description" "-")))
                     (println)))

      "skills-list" (let [skills (find-skills dir)]
                      (println "=== Skills ===\n")
                      (doseq [skill skills]
                        (println (format "  %s: %s" (:name skill) (:path skill)))))

      "claude-json" (let [config (load-ruler-toml dir)]
                      (println (json/generate-string
                                 (generate-claude-mcp-config config)
                                 {:pretty true})))

      "codex-json" (let [config (load-ruler-toml dir)]
                     (println (json/generate-string
                                (generate-codex-mcp-config config)
                                {:pretty true})))

      "bisim" (let [config (load-ruler-toml dir)
                    balance (bisimulation-balance config)]
                (println "=== GF(3) Bisimulation ===\n")
                (println (format "Agents: %s" (:agents balance)))
                (println (format "Sum: %d" (:sum balance)))
                (println (format "Balanced: %s" (:balanced balance))))

      "nbb-schema" (println (json/generate-string (nbb-interface-schema) {:pretty true}))

      "claude-add" (let [config (load-ruler-toml dir)]
                     (println "=== Adding MCP servers to Claude ===\n")
                     (doseq [[name server] (get config "mcp_servers" {})]
                       (claude-mcp-add name server)))

      "codex-add" (let [config (load-ruler-toml dir)]
                    (println "=== Adding MCP servers to Codex ===\n")
                    (doseq [[name server] (get config "mcp_servers" {})]
                      (codex-mcp-add name server)))

      (do
        (println "ruler.bb — Ruler skill/MCP propagation for Babashka")
        (println "")
        (println "Commands:")
        (println "  sync [dir]        Sync ruler config to all agents")
        (println "  mcp-list [dir]    List MCP servers from ruler.toml")
        (println "  skills-list [dir] List available skills")
        (println "  claude-json [dir] Generate Claude MCP config JSON")
        (println "  codex-json [dir]  Generate Codex MCP config JSON")
        (println "  bisim [dir]       Show GF(3) bisimulation balance")
        (println "  nbb-schema        Output NBB interface schema")
        (println "  claude-add [dir]  Add all MCP servers via claude mcp add")
        (println "  codex-add [dir]   Add all MCP servers via codex mcp add")
        (println "")
        (println "Example:")
        (println "  bb ruler.bb sync /path/to/project")
        (println "  bb ruler.bb claude-json . | jq .")))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
