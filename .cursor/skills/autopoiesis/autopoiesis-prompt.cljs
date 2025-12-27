#!/usr/bin/env nbb
;; autopoiesis-prompt.cljs - Modify agent system prompts
;; Usage: npx nbb autopoiesis-prompt.cljs <agent> <section> <content>
;;    or: npx nbb autopoiesis-prompt.cljs --list
;;    or: npx nbb autopoiesis-prompt.cljs --show <agent>

(ns autopoiesis.prompt
  (:require ["fs" :as fs]
            ["path" :as path]
            ["os" :as os]
            [clojure.string :as str]))

;;; ============================================================
;;; Agent Prompt Paths
;;; ============================================================

(def HOME (.-HOME (.-env js/process)))

(def PROMPT-PATHS
  {:claude (str HOME "/.claude/CLAUDE.md")
   :codex (str HOME "/.codex/instructions.md")
   :amp (str HOME "/.amp/AGENTS.md")
   :cursor ".cursorrules"
   :vscode ".github/copilot-instructions.md"
   :goose (str HOME "/.config/goose/system.md")})

(def TRIT-ASSIGNMENTS
  {:claude -1   ; MINUS (backward/utility)
   :codex 0     ; ERGODIC (neutral/transport)
   :cursor 1    ; PLUS (forward/state)
   :amp 0       ; ERGODIC
   :vscode 1    ; PLUS
   :goose -1})  ; MINUS

;;; ============================================================
;;; Prompt Modification
;;; ============================================================

(defn read-file [path]
  (try
    (.readFileSync fs path "utf8")
    (catch :default _e "")))

(defn write-file [path content]
  (let [dir (.dirname path path)]
    (when-not (.existsSync fs dir)
      (.mkdirSync fs dir #js {:recursive true}))
    (.writeFileSync fs path content "utf8")))

(defn make-section [section content trit]
  (let [marker (str "<!-- autopoiesis:" section " -->")
        end-marker (str "<!-- /autopoiesis:" section " -->")
        trit-marker (str "<!-- trit:" trit " -->")]
    (str marker "\n" trit-marker "\n" content "\n" end-marker)))

(defn modify-prompt! [agent section content]
  (let [path (get PROMPT-PATHS (keyword agent))
        trit (get TRIT-ASSIGNMENTS (keyword agent) 0)]
    (if-not path
      (do (println (str "❌ Unknown agent: " agent))
          (println "Available agents:" (str/join ", " (map name (keys PROMPT-PATHS)))))
      (let [existing (read-file path)
            marker (str "<!-- autopoiesis:" section " -->")
            end-marker (str "<!-- /autopoiesis:" section " -->")
            new-section (make-section section content trit)
            regex (js/RegExp. (str marker "[\\s\\S]*?" end-marker) "g")
            updated (if (str/includes? existing marker)
                      (.replace existing regex new-section)
                      (str existing "\n\n" new-section))]
        (write-file path updated)
        (println (str "✅ Updated " path))
        (println (str "   Section: " section))
        (println (str "   Trit: " trit " (" 
                     (case trit -1 "MINUS" 0 "ERGODIC" 1 "PLUS" "?") ")"))
        {:agent agent :section section :path path :trit trit}))))

(defn remove-section! [agent section]
  (let [path (get PROMPT-PATHS (keyword agent))]
    (when path
      (let [existing (read-file path)
            marker (str "<!-- autopoiesis:" section " -->")
            end-marker (str "<!-- /autopoiesis:" section " -->")
            regex (js/RegExp. (str marker "[\\s\\S]*?" end-marker "\n*") "g")
            updated (.replace existing regex "")]
        (write-file path updated)
        (println (str "✅ Removed section '" section "' from " path))))))

(defn list-sections [agent]
  (let [path (get PROMPT-PATHS (keyword agent))]
    (when path
      (let [existing (read-file path)
            regex (js/RegExp. "<!-- autopoiesis:([^>]+) -->" "g")
            matches (.-length (.match existing regex))]
        (println (str "\n📄 " path))
        (println (str "   Sections found: " (or matches 0)))
        (when-let [m (.match existing regex)]
          (doseq [match m]
            (let [section (second (re-find #"autopoiesis:(\S+)" match))]
              (println (str "   • " section)))))))))

(defn show-prompt [agent]
  (let [path (get PROMPT-PATHS (keyword agent))]
    (if path
      (do
        (println (str "\n📄 " agent " prompt: " path))
        (println (str/join "" (repeat 60 "─")))
        (println (read-file path))
        (println (str/join "" (repeat 60 "─"))))
      (println (str "❌ Unknown agent: " agent)))))

(defn show-all-agents []
  (println "\n╔═══════════════════════════════════════════════════════════════╗")
  (println "║  AUTOPOIESIS: Agent Prompt Paths                              ║")
  (println "╚═══════════════════════════════════════════════════════════════╝")
  (println)
  (doseq [[agent path] PROMPT-PATHS]
    (let [exists? (.existsSync fs path)
          trit (get TRIT-ASSIGNMENTS agent)]
      (println (str "  " (name agent) 
                   (str/join "" (repeat (- 10 (count (name agent))) " "))
                   " │ " (if exists? "✓" "○") " │ "
                   "trit=" trit " │ " path))))
  (println)
  (println "Legend: ✓ exists, ○ not created yet"))

;;; ============================================================
;;; CLI
;;; ============================================================

(defn print-help []
  (println "
autopoiesis-prompt.cljs - Modify agent system prompts

Usage:
  npx nbb autopoiesis-prompt.cljs <agent> <section> <content>
  npx nbb autopoiesis-prompt.cljs --remove <agent> <section>
  npx nbb autopoiesis-prompt.cljs --list [agent]
  npx nbb autopoiesis-prompt.cljs --show <agent>
  npx nbb autopoiesis-prompt.cljs --agents

Agents: claude, codex, amp, cursor, vscode, goose

Examples:
  # Add tool preferences to Claude
  npx nbb autopoiesis-prompt.cljs claude tool-preferences 'Prefer finder over grep'
  
  # Add context to Codex
  npx nbb autopoiesis-prompt.cljs codex context 'This project uses Julia and Clojure'
  
  # Show all agents
  npx nbb autopoiesis-prompt.cljs --agents
  
  # List sections in Claude prompt
  npx nbb autopoiesis-prompt.cljs --list claude
"))

(defn -main [& args]
  (let [[cmd arg1 arg2 & rest] args
        content (when rest (str/join " " (cons arg2 rest)))]
    (cond
      (or (nil? cmd) (= cmd "--help") (= cmd "-h"))
      (print-help)
      
      (= cmd "--agents")
      (show-all-agents)
      
      (= cmd "--list")
      (if arg1
        (list-sections arg1)
        (doseq [agent (keys PROMPT-PATHS)]
          (list-sections (name agent))))
      
      (= cmd "--show")
      (if arg1
        (show-prompt arg1)
        (println "Usage: --show <agent>"))
      
      (= cmd "--remove")
      (if (and arg1 arg2)
        (remove-section! arg1 arg2)
        (println "Usage: --remove <agent> <section>"))
      
      ;; Default: modify prompt
      (and cmd arg1 arg2)
      (modify-prompt! cmd arg1 (str arg2 (when rest (str " " (str/join " " rest)))))
      
      :else
      (do
        (println "❌ Invalid arguments")
        (print-help)))))

(apply -main *command-line-args*)
