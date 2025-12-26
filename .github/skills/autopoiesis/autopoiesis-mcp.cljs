#!/usr/bin/env nbb
;; autopoiesis-mcp.cljs - Configure MCP servers across agents
;; Usage: npx nbb autopoiesis-mcp.cljs add <agent> <name> <command> [args...]
;;        npx nbb autopoiesis-mcp.cljs remove <agent> <name>
;;        npx nbb autopoiesis-mcp.cljs list [agent]
;;        npx nbb autopoiesis-mcp.cljs presets

(ns autopoiesis.mcp
  (:require ["fs" :as fs]
            ["path" :as path]
            [clojure.string :as str]))

;;; ============================================================
;;; Agent MCP Config Paths
;;; ============================================================

(def HOME (.-HOME (.-env js/process)))

(def MCP-CONFIG-PATHS
  {:claude (str HOME "/.claude/mcp_servers.json")
   :amp (str HOME "/.config/amp/mcp.json")
   :cursor (str HOME "/.cursor/mcp.json")
   :codex (str HOME "/.codex/mcp.json")
   :vscode ".vscode/mcp.json"})

;;; ============================================================
;;; Preset MCP Servers
;;; ============================================================

(def PRESETS
  {:gay
   {:type "stdio"
    :command "julia"
    :args ["--project=~/.julia/packages/Gay" "-e" "using Gay; Gay.serve_mcp()"]}
   
   :firecrawl
   {:type "stdio"
    :command "npx"
    :args ["-y" "firecrawl-mcp"]}
   
   :duckdb
   {:type "stdio"
    :command "npx"
    :args ["-y" "@anthropic/mcp-server-duckdb"]}
   
   :filesystem
   {:type "stdio"
    :command "npx"
    :args ["-y" "@anthropic/mcp-server-filesystem" "~"]}
   
   :github
   {:type "stdio"
    :command "npx"
    :args ["-y" "@anthropic/mcp-server-github"]}
   
   :memory
   {:type "stdio"
    :command "npx"
    :args ["-y" "@anthropic/mcp-server-memory"]}
   
   :exa
   {:type "stdio"
    :command "npx"
    :args ["-y" "exa-mcp-server"]}
   
   :marginalia
   {:type "stdio"
    :command "npx"
    :args ["-y" "marginalia-mcp"]}
   
   :tree-sitter
   {:type "stdio"
    :command "uvx"
    :args ["mcp-server-tree-sitter"]}
   
   :radare2
   {:type "stdio"
    :command "r2mcp"
    :args []}
   
   :localsend
   {:type "stdio"
    :command "npx"
    :args ["-y" "localsend-mcp"]}})

;;; ============================================================
;;; JSON Helpers
;;; ============================================================

(defn read-json [path]
  (try
    (js->clj (js/JSON.parse (.readFileSync fs path "utf8")) :keywordize-keys true)
    (catch :default _e {})))

(defn write-json [path data]
  (let [dir (.dirname path path)]
    (when-not (.existsSync fs dir)
      (.mkdirSync fs dir #js {:recursive true}))
    (.writeFileSync fs path (js/JSON.stringify (clj->js data) nil 2) "utf8")))

;;; ============================================================
;;; MCP Configuration
;;; ============================================================

(defn add-server! [agent name config]
  (let [path (get MCP-CONFIG-PATHS (keyword agent))]
    (if-not path
      (println (str "❌ Unknown agent: " agent))
      (let [existing (read-json path)
            updated (assoc existing (keyword name) config)]
        (write-json path updated)
        (println (str "✅ Added '" name "' to " agent))
        (println (str "   Path: " path))
        (println (str "   Command: " (:command config) " " (str/join " " (:args config))))))))

(defn add-preset! [agent preset-name]
  (if-let [config (get PRESETS (keyword preset-name))]
    (add-server! agent preset-name config)
    (println (str "❌ Unknown preset: " preset-name "\nUse --presets to list available presets"))))

(defn add-preset-all! [preset-name]
  (println (str "\n🚀 Adding '" preset-name "' to all agents..."))
  (doseq [agent (keys MCP-CONFIG-PATHS)]
    (add-preset! (name agent) preset-name))
  (println "\n✅ Done!"))

(defn remove-server! [agent name]
  (let [path (get MCP-CONFIG-PATHS (keyword agent))]
    (when path
      (let [existing (read-json path)
            updated (dissoc existing (keyword name))]
        (write-json path updated)
        (println (str "✅ Removed '" name "' from " agent))))))

(defn list-servers [agent]
  (let [path (get MCP-CONFIG-PATHS (keyword agent))]
    (when path
      (let [config (read-json path)]
        (println (str "\n📦 " agent " MCP servers (" path ")"))
        (if (empty? config)
          (println "   (none)")
          (doseq [[name cfg] config]
            (println (str "   • " (clojure.core/name name) " → " (:command cfg)))))))))

(defn list-all []
  (println "\n╔═══════════════════════════════════════════════════════════════╗")
  (println "║  AUTOPOIESIS: MCP Server Configuration                        ║")
  (println "╚═══════════════════════════════════════════════════════════════╝")
  (doseq [agent (keys MCP-CONFIG-PATHS)]
    (list-servers (name agent))))

(defn show-presets []
  (println "\n╔═══════════════════════════════════════════════════════════════╗")
  (println "║  Available MCP Presets                                         ║")
  (println "╚═══════════════════════════════════════════════════════════════╝")
  (println)
  (doseq [[name cfg] PRESETS]
    (println (str "  " (clojure.core/name name)))
    (println (str "    " (:command cfg) " " (str/join " " (:args cfg))))
    (println)))

;;; ============================================================
;;; CLI
;;; ============================================================

(defn print-help []
  (println "
autopoiesis-mcp.cljs - Configure MCP servers across agents

Usage:
  npx nbb autopoiesis-mcp.cljs add <agent> <name> <command> [args...]
  npx nbb autopoiesis-mcp.cljs preset <agent> <preset-name>
  npx nbb autopoiesis-mcp.cljs preset-all <preset-name>
  npx nbb autopoiesis-mcp.cljs remove <agent> <name>
  npx nbb autopoiesis-mcp.cljs list [agent]
  npx nbb autopoiesis-mcp.cljs presets

Agents: claude, amp, cursor, codex, vscode

Presets: gay, firecrawl, duckdb, filesystem, github, memory, exa, 
         marginalia, tree-sitter, radare2, localsend

Examples:
  # Add gay-mcp to Claude
  npx nbb autopoiesis-mcp.cljs preset claude gay
  
  # Add firecrawl to all agents
  npx nbb autopoiesis-mcp.cljs preset-all firecrawl
  
  # Add custom server
  npx nbb autopoiesis-mcp.cljs add claude myserver npx -y my-mcp-server
  
  # List all configured servers
  npx nbb autopoiesis-mcp.cljs list
  
  # Show available presets
  npx nbb autopoiesis-mcp.cljs presets
"))

(defn -main [& args]
  (let [[cmd arg1 arg2 & rest] args]
    (cond
      (or (nil? cmd) (= cmd "--help") (= cmd "-h"))
      (print-help)
      
      (= cmd "add")
      (if (and arg1 arg2 (first rest))
        (add-server! arg1 arg2 {:type "stdio" :command (first rest) :args (vec (next rest))})
        (println "Usage: add <agent> <name> <command> [args...]"))
      
      (= cmd "preset")
      (if (and arg1 arg2)
        (add-preset! arg1 arg2)
        (println "Usage: preset <agent> <preset-name>"))
      
      (= cmd "preset-all")
      (if arg1
        (add-preset-all! arg1)
        (println "Usage: preset-all <preset-name>"))
      
      (= cmd "remove")
      (if (and arg1 arg2)
        (remove-server! arg1 arg2)
        (println "Usage: remove <agent> <name>"))
      
      (= cmd "list")
      (if arg1
        (list-servers arg1)
        (list-all))
      
      (= cmd "presets")
      (show-presets)
      
      :else
      (do
        (println (str "❌ Unknown command: " cmd))
        (print-help)))))

(apply -main *command-line-args*)
