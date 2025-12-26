#!/usr/bin/env nbb
;; propagate-skills.cljs - Propagate skills to all agents with GF(3) conservation
;; Usage: npx nbb propagate-skills.cljs <skill> [skill2 skill3 ...]
;;        npx nbb propagate-skills.cljs --all
;;        npx nbb propagate-skills.cljs --tripartite

(ns autopoiesis.propagate
  (:require ["child_process" :as cp]
            [clojure.string :as str]))

;;; ============================================================
;;; Agent Definitions with GF(3) Trit Assignments
;;; ============================================================

(def AGENTS
  [{:name "claude"  :trit -1 :role "MINUS (backward/utility)"}
   {:name "cursor"  :trit 1  :role "PLUS (forward/state)"}
   {:name "amp"     :trit 0  :role "ERGODIC (neutral/transport)"}
   {:name "codex"   :trit 0  :role "ERGODIC (neutral/transport)"}
   {:name "vscode"  :trit 1  :role "PLUS (forward/state)"}
   {:name "goose"   :trit -1 :role "MINUS (backward/utility)"}
   {:name "letta"   :trit 0  :role "ERGODIC (neutral/transport)"}])

(def TRIPARTITE-AGENTS
  ;; Sum of trits = -1 + 0 + 1 = 0 (mod 3) ✓
  [{:name "claude" :trit -1}
   {:name "codex"  :trit 0}
   {:name "cursor" :trit 1}])

(def CORE-SKILLS
  ["gay-mcp" "bisimulation-game" "duckdb-temporal-versioning" 
   "autopoiesis" "triad-interleave"])

;;; ============================================================
;;; Shell Execution
;;; ============================================================

(defn exec-sync [cmd]
  (try
    (let [result (.execSync cp cmd #js {:encoding "utf8" :stdio "pipe"})]
      {:success true :output result})
    (catch :default e
      {:success false :error (.-message e)})))

(defn install-skill! [skill agent]
  (let [cmd (str "npx ai-agent-skills install " skill " --agent " agent)
        result (exec-sync cmd)]
    (if (:success result)
      (do (println (str "  ✓ " agent)) true)
      (do (println (str "  ✗ " agent " - " (:error result))) false))))

;;; ============================================================
;;; Propagation Logic
;;; ============================================================

(defn propagate-to-agents! [skill agents]
  (println (str "\n→ Propagating: " skill))
  (let [results (for [agent agents]
                  {:agent (:name agent)
                   :trit (:trit agent)
                   :success (install-skill! skill (:name agent))})]
    (let [trits (map :trit results)
          sum (reduce + trits)
          gf3 (mod sum 3)]
      {:skill skill
       :agents (map :agent results)
       :successes (count (filter :success results))
       :total (count results)
       :gf3-sum gf3
       :gf3-conserved? (zero? gf3)})))

(defn propagate-skill! [skill]
  (propagate-to-agents! skill AGENTS))

(defn propagate-tripartite! [skill]
  (propagate-to-agents! skill TRIPARTITE-AGENTS))

(defn propagate-all-skills! []
  (println "\n╔═══════════════════════════════════════════════════════════════╗")
  (println "║  AUTOPOIESIS: Full Skill Propagation                          ║")
  (println "╚═══════════════════════════════════════════════════════════════╝")
  (let [results (for [skill CORE-SKILLS]
                  (propagate-skill! skill))]
    (println "\n═══════════════════════════════════════════════════════════════")
    (println "  Results:")
    (doseq [r results]
      (println (str "  " (:skill r) ": " (:successes r) "/" (:total r) 
                   " | GF(3)=" (:gf3-sum r) 
                   (if (:gf3-conserved? r) " ✓" " ✗"))))
    (println "═══════════════════════════════════════════════════════════════")
    results))

(defn propagate-tripartite-all! []
  (println "\n╔═══════════════════════════════════════════════════════════════╗")
  (println "║  TRIPARTITE: Claude + Codex + Cursor (GF(3) = 0)              ║")
  (println "╚═══════════════════════════════════════════════════════════════╝")
  (println "\nTrits: Claude(-1) + Codex(0) + Cursor(+1) = 0 mod 3 ✓")
  (let [results (for [skill CORE-SKILLS]
                  (propagate-tripartite! skill))]
    (println "\n═══════════════════════════════════════════════════════════════")
    (println "  Tripartite Results:")
    (doseq [r results]
      (println (str "  " (:skill r) ": " (:successes r) "/" (:total r))))
    (println "═══════════════════════════════════════════════════════════════")
    results))

;;; ============================================================
;;; CLI
;;; ============================================================

(defn print-help []
  (println "
propagate-skills.cljs - Propagate skills with GF(3) conservation

Usage:
  npx nbb propagate-skills.cljs <skill> [skill2 skill3 ...]
  npx nbb propagate-skills.cljs --all
  npx nbb propagate-skills.cljs --tripartite
  npx nbb propagate-skills.cljs --agents

GF(3) Conservation:
  Sum of agent trits ≡ 0 (mod 3)
  
  Tripartite: Claude(-1) + Codex(0) + Cursor(+1) = 0 ✓
  Full: Claude(-1) + Cursor(1) + Amp(0) + Codex(0) + VSCode(1) + Goose(-1) + Letta(0) = 0 ✓

Examples:
  # Propagate single skill
  npx nbb propagate-skills.cljs gay-mcp
  
  # Propagate multiple skills
  npx nbb propagate-skills.cljs gay-mcp bisimulation-game autopoiesis
  
  # Propagate all core skills to all agents
  npx nbb propagate-skills.cljs --all
  
  # Propagate to tripartite agents only (Claude + Codex + Cursor)
  npx nbb propagate-skills.cljs --tripartite
"))

(defn show-agents []
  (println "\n╔═══════════════════════════════════════════════════════════════╗")
  (println "║  Agent Trit Assignments                                        ║")
  (println "╚═══════════════════════════════════════════════════════════════╝")
  (println)
  (doseq [agent AGENTS]
    (println (str "  " (:name agent) 
                 (str/join "" (repeat (- 10 (count (:name agent))) " "))
                 " │ trit=" (if (neg? (:trit agent)) "" " ") (:trit agent) 
                 " │ " (:role agent))))
  (println)
  (let [sum (reduce + (map :trit AGENTS))]
    (println (str "  Total: " sum " ≡ " (mod sum 3) " (mod 3) " 
                 (if (zero? (mod sum 3)) "✓ conserved" "✗ NOT conserved")))))

(defn -main [& args]
  (let [[cmd & rest] args]
    (cond
      (or (nil? cmd) (= cmd "--help") (= cmd "-h"))
      (print-help)
      
      (= cmd "--all")
      (propagate-all-skills!)
      
      (= cmd "--tripartite")
      (propagate-tripartite-all!)
      
      (= cmd "--agents")
      (show-agents)
      
      :else
      ;; Propagate specified skills
      (do
        (println "\n╔═══════════════════════════════════════════════════════════════╗")
        (println "║  AUTOPOIESIS: Skill Propagation                               ║")
        (println "╚═══════════════════════════════════════════════════════════════╝")
        (doseq [skill args]
          (propagate-skill! skill))
        (println "\n✅ Propagation complete")))))

(apply -main *command-line-args*)
