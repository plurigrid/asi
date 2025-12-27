;; borkdude/propagate.clj
;; Invariant skill propagation to AI agents via ruler

(ns borkdude.propagate
  "Propagate skills to all AI agents with GF(3) conservation.
   
   Integrates with intellectronica/ruler for centralized skill management."
  (:require [clojure.java.io :as io]
            [clojure.string :as str]))

;; ═══════════════════════════════════════════════════════════════════════════════
;; AGENT CONFIGURATIONS
;; ═══════════════════════════════════════════════════════════════════════════════

(def AGENT-CONFIGS
  "AI agent skill paths and GF(3) trit assignments"
  {:claude
   {:path ".claude/skills/"
    :trit -1  ; MINUS (backward/utility)
    :format :markdown
    :native-skills true}
   
   :codex
   {:path ".codex/skills/"
    :trit 0   ; ERGODIC (neutral/transport)
    :format :markdown
    :native-skills true}
   
   :copilot
   {:path ".vscode/skills/"  ; Via AGENTS.md convention
    :trit 1   ; PLUS (forward/state)
    :format :markdown
    :native-skills false}
   
   :cursor
   {:path ".cursor/skills/"  ; Via skillz MCP
    :trit -1
    :format :markdown
    :native-skills false}
   
   :amp
   {:path ".ruler/skills/"   ; Source of truth
    :trit 0
    :format :markdown
    :native-skills true}
   
   :aider
   {:path ".skillz/"         ; Via skillz MCP
    :trit 1
    :format :markdown
    :native-skills false}})

;; ═══════════════════════════════════════════════════════════════════════════════
;; SKILL TEMPLATE
;; ═══════════════════════════════════════════════════════════════════════════════

(defn skill-markdown
  "Generate SKILL.md content for a skill"
  [{:keys [name description version trit color features]}]
  (str
   "---\n"
   "name: " name "\n"
   "description: \"" description "\"\n"
   "version: " version "\n"
   "trit: " trit "\n"
   "color: \"" color "\"\n"
   "source: borkdude-propagated\n"
   "invariant: true\n"
   "---\n\n"
   "# " name "\n\n"
   description "\n\n"
   "## Features\n\n"
   (str/join "\n" (map #(str "- " %) features)) "\n\n"
   "## Invariant Guarantee\n\n"
   "This skill is propagated via borkdude/propagate with GF(3) conservation.\n"
   "Same seed → same behavior across all agents.\n"))

;; ═══════════════════════════════════════════════════════════════════════════════
;; PROPAGATION LOGIC
;; ═══════════════════════════════════════════════════════════════════════════════

(defn ensure-path!
  "Ensure directory path exists"
  [path]
  (let [dir (io/file path)]
    (when-not (.exists dir)
      (.mkdirs dir))
    path))

(defn propagate-to-agent!
  "Propagate a skill to a specific agent"
  [agent-key skill-manifest]
  (let [{:keys [path trit format native-skills]} (get AGENT-CONFIGS agent-key)
        skill-name (:name skill-manifest)
        skill-path (str path skill-name "/")
        skill-file (str skill-path "SKILL.md")]
    (when path
      (ensure-path! skill-path)
      (spit skill-file (skill-markdown (assoc skill-manifest :trit trit)))
      {:agent agent-key
       :path skill-file
       :trit trit
       :success true})))

(defn propagate-skill!
  "Propagate a skill to all configured agents"
  [skill-manifest]
  (let [results (for [[agent-key _] AGENT-CONFIGS]
                  (propagate-to-agent! agent-key skill-manifest))
        trits (map :trit results)
        sum (reduce + trits)]
    {:skill (:name skill-manifest)
     :agents (map :agent results)
     :trits trits
     :gf3-sum sum
     :gf3-conserved? (zero? (mod sum 3))
     :results results}))

;; ═══════════════════════════════════════════════════════════════════════════════
;; BORKDUDE SKILLS
;; ═══════════════════════════════════════════════════════════════════════════════

(def BORKDUDE-SKILLS
  "Skills from borkdude ecosystem to propagate"
  [{:name "cherry-runtime"
    :description "Cherry 🍒 ClojureScript to ES6 compiler for browser"
    :version "0.5.34"
    :color "#FF6B6B"
    :features ["CLJS→ES6 compilation"
               "JSX support via #jsx"
               "async/await"
               "npm publishing"
               "Source maps"]}
   
   {:name "squint-runtime"
    :description "Squint: lightweight CLJS syntax to JS compiler"
    :version "0.8.x"
    :color "#7CB518"
    :features ["Minimal runtime"
               "JS interop"
               "Small bundle size"
               "Fast compilation"]}
   
   {:name "sci-interpreter"
    :description "SCI: Small Clojure Interpreter for sandboxed evaluation"
    :version "0.10.49"
    :color "#00CCCC"
    :features ["Sandboxed evaluation"
               "Configurable namespaces"
               "DSL support"
               "GraalVM compatible"]}
   
   {:name "babashka-scripting"
    :description "Babashka: fast native Clojure scripting"
    :version "1.12.x"
    :color "#9933FF"
    :features ["5ms startup"
               "GraalVM native image"
               "Pods ecosystem"
               "nREPL support"]}])

(defn propagate-all!
  "Propagate all borkdude skills to all agents"
  []
  (println "╔═══════════════════════════════════════════════════════════════════╗")
  (println "║  BORKDUDE SKILL PROPAGATION                                       ║")
  (println "╚═══════════════════════════════════════════════════════════════════╝")
  (println)
  
  (let [results (for [skill BORKDUDE-SKILLS]
                  (do
                    (println (str "  Propagating: " (:name skill)))
                    (propagate-skill! skill)))]
    
    (println)
    (println "─── Results ───")
    (doseq [r results]
      (println (format "  %s: %d agents, GF(3)=%s"
                       (:skill r)
                       (count (:agents r))
                       (if (:gf3-conserved? r) "✓" "✗"))))
    
    (println)
    (println "═══════════════════════════════════════════════════════════════════")
    (println "Propagation complete. Skills available in all agent directories.")
    
    results))

(when (= *file* (System/getProperty "babashka.file"))
  (propagate-all!))
