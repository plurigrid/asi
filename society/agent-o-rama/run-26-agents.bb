#!/usr/bin/env bb
;; Run 26 Agent-O-Rama agents in parallel, each with its own wallet
;; Connected to OpenRouter Devstral

(require '[babashka.http-client :as http]
         '[cheshire.core :as json]
         '[babashka.process :as p]
         '[clojure.java.io :as io])

(def openrouter-api-key (System/getenv "OPENROUTER_API_KEY"))
(def openrouter-url "https://openrouter.ai/api/v1/chat/completions")
(def model "mistralai/devstral-small:free")

(def worlds 
  ["world_a" "world_b" "world_c" "world_d" "world_e" "world_f" 
   "world_g" "world_h" "world_i" "world_j" "world_k" "world_l"
   "world_m" "world_n" "world_o" "world_p" "world_q" "world_r"
   "world_s" "world_t" "world_u" "world_v" "world_w" "world_x"
   "world_y" "world_z"])

(def trits
  ;; GF(3) assignments: -1, 0, +1 cycling
  (mapv #(case (mod % 3) 0 -1, 1 0, 2 1) (range 26)))

(defn call-devstral [system-prompt user-prompt]
  (let [resp (http/post openrouter-url
               {:headers {"Authorization" (str "Bearer " openrouter-api-key)
                          "Content-Type" "application/json"}
                :body (json/encode 
                        {:model model
                         :messages [{:role "system" :content system-prompt}
                                    {:role "user" :content user-prompt}]})})]
    (-> resp :body (json/decode true) :choices first :message :content)))

(defn agent-system-prompt [world-name trit]
  (format "You are %s, a GF(3) agent with trit=%d.
Your wallet MCP tools: mcp__%s_aptos__aptos_balance, mcp__%s_aptos__aptos_transfer, etc.
You participate in Aptos Society multiverse finance.
Contract: 0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b
Operations: SPLIT (create bifurcation), MERGE (combine claims), MAINTAIN (reset decay), CLAIM (settle).
Coordinate with other agents. Your trit role: %s"
    world-name trit world-name world-name
    (case trit -1 "MINUS (validator)" 0 "ERGODIC (coordinator)" 1 "PLUS (executor)")))

(defn run-agent [world-name trit idx]
  (println (format "[%02d] Starting %s (trit=%+d)..." idx world-name trit))
  (let [prompt (agent-system-prompt world-name trit)
        response (call-devstral prompt "Report your status and check your wallet balance.")]
    (println (format "[%02d] %s: %s" idx world-name (subs response 0 (min 200 (count response)))))
    {:world world-name :trit trit :response response}))

(defn run-all-agents []
  (println "🌐 Launching 26 Agent-O-Rama agents on OpenRouter Devstral...")
  (println (format "   Model: %s" model))
  (println "")
  
  ;; Run in parallel (26 futures)
  (let [futures (mapv (fn [idx]
                        (future (run-agent (nth worlds idx) (nth trits idx) idx)))
                      (range 26))
        results (mapv deref futures)]
    
    (println "")
    (println "═══════════════════════════════════════════════════════════════")
    (println "✅ All 26 agents initialized")
    (println (format "   GF(3) sum: %d (should be 0)" (reduce + trits)))
    results))

(when (= *file* (System/getProperty "babashka.file"))
  (if openrouter-api-key
    (run-all-agents)
    (println "❌ Set OPENROUTER_API_KEY environment variable")))
