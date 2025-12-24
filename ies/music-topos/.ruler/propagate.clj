#!/usr/bin/env bb
;; .ruler/propagate.clj
;;
;; Propagate skills from .ruler/skills/ to all configured agents
;; Maintains GF(3) conservation across agent triplets

(ns ruler.propagate
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [babashka.fs :as fs]))

;; ═══════════════════════════════════════════════════════════════════════════════
;; AGENT CONFIGURATIONS
;; ═══════════════════════════════════════════════════════════════════════════════

(def AGENTS
  {:codex   {:trit 0   :skills-path ".codex/skills"   :mcp-path ".codex/mcp.json"}
   :claude  {:trit -1  :skills-path ".claude/skills"  :mcp-path ".claude/mcp.json"}
   :amp     {:trit 0   :skills-path ".ruler/skills"   :mcp-path ".mcp.json"}
   :cursor  {:trit -1  :skills-path ".cursor/skills"  :mcp-path ".cursor/mcp.json"}
   :copilot {:trit 1   :skills-path ".vscode/skills"  :mcp-path ".vscode/mcp.json"}
   :aider   {:trit 1   :skills-path ".skillz"         :mcp-path ".aider/mcp.json"}})

(def SKILLS-TO-PROPAGATE
  ["unworld" "three-match" "borkdude" "gay-mcp"])

;; ═══════════════════════════════════════════════════════════════════════════════
;; SKILL PROPAGATION
;; ═══════════════════════════════════════════════════════════════════════════════

(defn ensure-dir! [path]
  (when-not (fs/exists? path)
    (fs/create-dirs path)))

(defn read-skill [skill-name]
  (let [skill-path (str ".ruler/skills/" skill-name "/SKILL.md")]
    (when (fs/exists? skill-path)
      (slurp skill-path))))

(defn write-skill! [agent-key skill-name content]
  (let [{:keys [skills-path trit]} (get AGENTS agent-key)
        target-dir (str skills-path "/" skill-name)
        target-file (str target-dir "/SKILL.md")]
    (ensure-dir! target-dir)
    ;; Add agent-specific header
    (let [header (str "<!-- Propagated to " (name agent-key) 
                      " | Trit: " trit 
                      " | Source: .ruler/skills/" skill-name " -->\n\n")
          full-content (str header content)]
      (spit target-file full-content)
      {:agent agent-key :skill skill-name :path target-file :trit trit})))

(defn propagate-skill! [skill-name]
  (println (str "  Propagating: " skill-name))
  (if-let [content (read-skill skill-name)]
    (doall
     (for [[agent-key _] AGENTS]
       (write-skill! agent-key skill-name content)))
    (println (str "    ⚠ Skill not found: " skill-name))))

(defn propagate-all! []
  (println "╔═══════════════════════════════════════════════════════════════════╗")
  (println "║  RULER SKILL PROPAGATION                                          ║")
  (println "╚═══════════════════════════════════════════════════════════════════╝")
  (println)
  
  (doseq [skill SKILLS-TO-PROPAGATE]
    (propagate-skill! skill))
  
  (println)
  (println "─── GF(3) Verification ───")
  (let [trits (map (fn [[_ v]] (:trit v)) AGENTS)
        sum (reduce + trits)]
    (println (str "  Agent trits: " (vec trits)))
    (println (str "  Sum: " sum " mod 3 = " (mod sum 3)))
    (println (str "  Conservation: " (if (zero? (mod sum 3)) "✓" "✗"))))
  
  (println)
  (println "═══════════════════════════════════════════════════════════════════")
  (println "Propagation complete. Skills available in all agent directories."))

;; ═══════════════════════════════════════════════════════════════════════════════
;; MCP CONFIGURATION GENERATION
;; ═══════════════════════════════════════════════════════════════════════════════

(def BASE-MCP-SERVERS
  {"gay" {"command" "julia"
          "args" ["--project=@gay" "-e" "using Gay; Gay.serve_mcp()"]
          "env" {"GAY_SEED" "1069"}}
   "unworld" {"command" "ruby"
              "args" ["-I" "lib" "-r" "unworld" "-e" "Unworld.serve_mcp"]
              "env" {"GENESIS_SEED" "0x42D"}}
   "synadia" {"command" "ruby"
              "args" ["-I" "lib" "-r" "synadia_broadcast" "-e" "SynadiaBroadcast.serve_mcp"]
              "env" {"NATS_URL" "nats://127.0.0.1:4222"}}
   "propagator" {"command" "lein"
                 "args" ["run" "-m" "music-topos.propagator-mcp"]
                 "env" {"DUCKDB_PATH" "/tmp/propagator-state.duckdb"}}})

(defn generate-mcp-config! [agent-key]
  (let [{:keys [mcp-path]} (get AGENTS agent-key)
        parent-dir (fs/parent mcp-path)]
    (when parent-dir
      (ensure-dir! parent-dir))
    (let [config {"mcpServers" BASE-MCP-SERVERS}
          json-str (str "{\n  \"mcpServers\": "
                       (pr-str BASE-MCP-SERVERS)
                       "\n}")]
      (spit mcp-path json-str)
      {:agent agent-key :path mcp-path})))

(defn generate-all-mcp-configs! []
  (println "─── Generating MCP Configs ───")
  (doseq [[agent-key _] AGENTS]
    (let [result (generate-mcp-config! agent-key)]
      (println (str "  " (name agent-key) " → " (:path result))))))

;; ═══════════════════════════════════════════════════════════════════════════════
;; MAIN
;; ═══════════════════════════════════════════════════════════════════════════════

(when (= *file* (System/getProperty "babashka.file"))
  (propagate-all!)
  (generate-all-mcp-configs!))
