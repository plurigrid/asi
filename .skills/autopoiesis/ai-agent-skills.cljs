#!/usr/bin/env nbb
;; ai-agent-skills.cljs - Enhanced ai-agent-skills wrapper with batch operations
;; Usage: npx nbb ai-agent-skills.cljs <command> [args...]
;;
;; This provides batch operations and automation beyond the base CLI

(ns autopoiesis.ai-agent-skills
  (:require ["child_process" :as cp]
            ["fs" :as fs]
            [clojure.string :as str]))

;;; ============================================================
;;; Configuration
;;; ============================================================

(def AGENTS
  ["claude" "cursor" "amp" "codex" "vscode" "goose" "letta" "project"])

(def CATEGORIES
  ["development" "document" "creative" "business" "productivity" "meta"])

(def SKILL-BUNDLES
  {:docs ["pdf" "xlsx" "docx" "pptx"]
   :dev ["frontend-design" "mcp-builder" "skill-creator" "webapp-testing" "code-review"]
   :creative ["canvas-design" "algorithmic-art" "image-enhancer" "slack-gif-creator"]
   :productivity ["doc-coauthoring" "internal-comms" "qa-regression"]
   :tripartite ["gay-mcp" "bisimulation-game" "autopoiesis" "duckdb-temporal-versioning"]
   :core ["gay-mcp" "autopoiesis" "bisimulation-game" "triad-interleave"]
   :all-anthropics ["pdf" "xlsx" "docx" "pptx" "frontend-design" "mcp-builder" 
                    "skill-creator" "code-review" "doc-coauthoring"]})

;;; ============================================================
;;; Shell Execution
;;; ============================================================

(defn exec-sync [cmd]
  (try
    (let [result (.execSync cp cmd #js {:encoding "utf8" :stdio "pipe"})]
      {:success true :output (str/trim result)})
    (catch :default e
      {:success false :error (.-message e)})))

(defn npx-skills [& args]
  (let [cmd (str "npx ai-agent-skills " (str/join " " args))]
    (exec-sync cmd)))

;;; ============================================================
;;; Core Operations
;;; ============================================================

(defn install-skill! [skill agent]
  (println (str "  Installing " skill " → " agent "..."))
  (let [result (npx-skills "install" skill "--agent" agent)]
    (if (:success result)
      (do (println (str "    ✓ " skill)) true)
      (do (println (str "    ✗ " skill " - " (:error result))) false))))

(defn uninstall-skill! [skill agent]
  (let [result (npx-skills "uninstall" skill "--agent" agent)]
    (if (:success result)
      (println (str "  ✓ Uninstalled " skill " from " agent))
      (println (str "  ✗ Failed to uninstall " skill)))))

(defn update-skill! [skill agent]
  (let [result (npx-skills "update" skill "--agent" agent)]
    (if (:success result)
      (println (str "  ✓ Updated " skill " for " agent))
      (println (str "  ✗ Failed to update " skill)))))

;;; ============================================================
;;; Batch Operations
;;; ============================================================

(defn install-to-all! [skill]
  "Install a skill to ALL agents"
  (println (str "\n🚀 Installing '" skill "' to all agents..."))
  (let [results (for [agent AGENTS]
                  {:agent agent :success (install-skill! skill agent)})]
    (let [successes (count (filter :success results))]
      (println (str "\n✅ Installed to " successes "/" (count AGENTS) " agents"))
      results)))

(defn install-bundle! [bundle-name agent]
  "Install a bundle of skills to an agent"
  (if-let [skills (get SKILL-BUNDLES (keyword bundle-name))]
    (do
      (println (str "\n📦 Installing bundle '" bundle-name "' to " agent "..."))
      (println (str "   Skills: " (str/join ", " skills)))
      (doseq [skill skills]
        (install-skill! skill agent))
      (println (str "\n✅ Bundle '" bundle-name "' installed to " agent)))
    (println (str "❌ Unknown bundle: " bundle-name 
                 "\n   Available: " (str/join ", " (map name (keys SKILL-BUNDLES)))))))

(defn install-bundle-all! [bundle-name]
  "Install a bundle to ALL agents"
  (if-let [skills (get SKILL-BUNDLES (keyword bundle-name))]
    (do
      (println (str "\n📦 Installing bundle '" bundle-name "' to ALL agents..."))
      (doseq [agent AGENTS]
        (println (str "\n→ " agent))
        (doseq [skill skills]
          (install-skill! skill agent)))
      (println (str "\n✅ Bundle '" bundle-name "' installed to all agents")))
    (println (str "❌ Unknown bundle: " bundle-name))))

(defn sync-agents! [source-agent]
  "Sync installed skills from source agent to all other agents"
  (println (str "\n🔄 Syncing from " source-agent " to all other agents..."))
  (let [result (npx-skills "list" "--installed" "--agent" source-agent)
        ;; Parse installed skills from output (simplified)
        output (:output result)]
    (println "   (Note: This requires parsing installed skills list)")
    (println "   Run: just list-installed " source-agent " to see skills")))

(defn diff-agents! [agent1 agent2]
  "Show skills difference between two agents"
  (println (str "\n📊 Comparing " agent1 " vs " agent2 "..."))
  (let [r1 (npx-skills "list" "--installed" "--agent" agent1)
        r2 (npx-skills "list" "--installed" "--agent" agent2)]
    (println (str "\n" agent1 " skills:"))
    (println (:output r1))
    (println (str "\n" agent2 " skills:"))
    (println (:output r2))))

;;; ============================================================
;;; Matrix Operations
;;; ============================================================

(defn install-matrix! [skills agents]
  "Install multiple skills to multiple agents (matrix install)"
  (println "\n╔═══════════════════════════════════════════════════════════════╗")
  (println "║  Matrix Install                                                ║")
  (println "╚═══════════════════════════════════════════════════════════════╝")
  (println (str "  Skills: " (str/join ", " skills)))
  (println (str "  Agents: " (str/join ", " agents)))
  (println)
  (let [total (* (count skills) (count agents))
        results (atom [])]
    (doseq [skill skills]
      (println (str "\n→ " skill))
      (doseq [agent agents]
        (let [success (install-skill! skill agent)]
          (swap! results conj {:skill skill :agent agent :success success}))))
    (let [successes (count (filter :success @results))]
      (println (str "\n═══════════════════════════════════════════════════════════════"))
      (println (str "  Total: " successes "/" total " successful"))
      (println "═══════════════════════════════════════════════════════════════")
      @results)))

;;; ============================================================
;;; Status & Reporting
;;; ============================================================

(defn show-status []
  "Show status of all agents"
  (println "\n╔═══════════════════════════════════════════════════════════════╗")
  (println "║  Agent Status                                                  ║")
  (println "╚═══════════════════════════════════════════════════════════════╝")
  (println)
  (doseq [agent AGENTS]
    (let [result (npx-skills "list" "--installed" "--agent" agent)]
      (if (:success result)
        (let [lines (str/split-lines (:output result))
              count (max 0 (- (count lines) 2))]  ; Rough estimate
          (println (str "  " agent 
                       (str/join "" (repeat (- 12 (count agent)) " "))
                       " │ ~" count " skills")))
        (println (str "  " agent " │ (error)"))))))

(defn show-bundles []
  "Show available skill bundles"
  (println "\n╔═══════════════════════════════════════════════════════════════╗")
  (println "║  Available Skill Bundles                                       ║")
  (println "╚═══════════════════════════════════════════════════════════════╝")
  (println)
  (doseq [[name skills] SKILL-BUNDLES]
    (println (str "  " (clojure.core/name name)))
    (println (str "    " (str/join ", " skills)))
    (println)))

;;; ============================================================
;;; CLI
;;; ============================================================

(defn print-help []
  (println "
ai-agent-skills.cljs - Enhanced batch operations for ai-agent-skills

Usage:
  npx nbb ai-agent-skills.cljs <command> [args...]

Commands:
  install-all <skill>              Install skill to ALL agents
  bundle <name> <agent>            Install skill bundle to agent
  bundle-all <name>                Install bundle to ALL agents
  matrix <skills> <agents>         Matrix install (comma-separated)
  sync <source-agent>              Sync skills from source to all
  diff <agent1> <agent2>           Compare installed skills
  status                           Show all agents status
  bundles                          List available bundles

Bundles:
  docs        pdf, xlsx, docx, pptx
  dev         frontend-design, mcp-builder, skill-creator, webapp-testing, code-review
  creative    canvas-design, algorithmic-art, image-enhancer, slack-gif-creator
  productivity doc-coauthoring, internal-comms, qa-regression
  tripartite  gay-mcp, bisimulation-game, autopoiesis, duckdb-temporal-versioning
  core        gay-mcp, autopoiesis, bisimulation-game, triad-interleave

Examples:
  # Install gay-mcp to all agents
  npx nbb ai-agent-skills.cljs install-all gay-mcp
  
  # Install docs bundle to Claude
  npx nbb ai-agent-skills.cljs bundle docs claude
  
  # Install core bundle to all agents
  npx nbb ai-agent-skills.cljs bundle-all core
  
  # Matrix install: 3 skills × 3 agents = 9 installs
  npx nbb ai-agent-skills.cljs matrix 'gay-mcp,autopoiesis' 'claude,codex,cursor'
  
  # Show agent status
  npx nbb ai-agent-skills.cljs status
"))

(defn -main [& args]
  (let [[cmd arg1 arg2 & rest] args]
    (cond
      (or (nil? cmd) (= cmd "--help") (= cmd "-h"))
      (print-help)
      
      (= cmd "install-all")
      (if arg1
        (install-to-all! arg1)
        (println "Usage: install-all <skill>"))
      
      (= cmd "bundle")
      (if (and arg1 arg2)
        (install-bundle! arg1 arg2)
        (println "Usage: bundle <name> <agent>"))
      
      (= cmd "bundle-all")
      (if arg1
        (install-bundle-all! arg1)
        (println "Usage: bundle-all <name>"))
      
      (= cmd "matrix")
      (if (and arg1 arg2)
        (let [skills (str/split arg1 #",")
              agents (str/split arg2 #",")]
          (install-matrix! skills agents))
        (println "Usage: matrix <skills,comma,sep> <agents,comma,sep>"))
      
      (= cmd "sync")
      (if arg1
        (sync-agents! arg1)
        (println "Usage: sync <source-agent>"))
      
      (= cmd "diff")
      (if (and arg1 arg2)
        (diff-agents! arg1 arg2)
        (println "Usage: diff <agent1> <agent2>"))
      
      (= cmd "status")
      (show-status)
      
      (= cmd "bundles")
      (show-bundles)
      
      :else
      (do
        (println (str "❌ Unknown command: " cmd))
        (print-help)))))

(apply -main *command-line-args*)
