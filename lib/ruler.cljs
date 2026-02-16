;; ruler.cljs - NBB (Node Babashka) Ruler for skill/MCP propagation
;; Runs in Node.js via nbb, communicates via S-expressions
;;
;; HARNESS PROPERTIES (GF(3) flows):
;; 1. INJECT (+1): Sync skills/MCP configs to agents
;; 2. EMIT (-1): Query configs, export JSON
;; 3. BRIDGE (0): Transform between formats

(ns ruler.nbb
  (:require [clojure.edn :as edn]
            [clojure.string :as str]
            ["fs" :as fs]
            ["path" :as path]
            ["os" :as os]))

;;; ============================================================
;;; State
;;; ============================================================

(def ruler-state
  (atom {:trit 0
         :ops []
         :config nil
         :skills []
         :mcp-servers {}
         :started (js/Date.now)}))

(defn update-trit! [delta]
  (swap! ruler-state update :trit #(mod (+ % delta) 3)))

;;; ============================================================
;;; TOML Parser (minimal)
;;; ============================================================

(defn parse-toml-value [v]
  (let [v (str/trim v)]
    (cond
      (= v "true") true
      (= v "false") false
      (and (str/starts-with? v "\"") (str/ends-with? v "\""))
      (subs v 1 (dec (count v)))
      (str/starts-with? v "[")
      (let [inner (-> v (subs 1) (str/replace #"\]$" "") str/trim)]
        (if (str/blank? inner) []
            (mapv #(parse-toml-value (str/trim %))
                  (str/split inner #","))))
      (str/starts-with? v "{")
      (let [inner (-> v (subs 1) (str/replace #"\}$" "") str/trim)]
        (if (str/blank? inner) {}
            (into {}
              (for [pair (str/split inner #",")]
                (let [[k val] (str/split pair #"=" 2)]
                  [(str/trim k) (parse-toml-value (str/trim val))])))))
      (str/starts-with? v "${")
      (let [env-var (-> v (subs 2) (str/replace #"\}$" ""))]
        (or (aget js/process.env env-var) v))
      (re-matches #"-?\d+\.?\d*" v)
      (js/parseFloat v)
      :else v)))

(defn parse-toml [content]
  (let [lines (str/split-lines content)
        result (atom {})
        current-section (atom [])]
    (doseq [line lines]
      (let [trimmed (str/trim line)]
        (cond
          (or (str/blank? trimmed) (str/starts-with? trimmed "#"))
          nil

          (and (str/starts-with? trimmed "[") (str/ends-with? trimmed "]"))
          (let [section (subs trimmed 1 (dec (count trimmed)))
                parts (str/split section #"\.")]
            (reset! current-section (vec parts)))

          (str/includes? trimmed "=")
          (let [[k v] (str/split trimmed #"=" 2)
                k (str/trim k)
                v (parse-toml-value (str/trim v))
                path* (conj @current-section k)]
            (swap! result assoc-in path* v)))))
    @result))

;;; ============================================================
;;; Filesystem Operations
;;; ============================================================

(defn home-dir []
  (.homedir os))

(defn read-file [p]
  (when (fs/existsSync p)
    (fs/readFileSync p "utf8")))

(defn write-file [p content]
  (fs/writeFileSync p content "utf8"))

(defn list-dir [p]
  (when (fs/existsSync p)
    (js->clj (fs/readdirSync p))))

(defn is-dir? [p]
  (and (fs/existsSync p)
       (.isDirectory (fs/statSync p))))

;;; ============================================================
;;; Claude Directory Discovery (lazy)
;;; ============================================================

(defn find-claude-dirs []
  "Lazily find all claude-related directories in home."
  (let [home (home-dir)]
    (->> (list-dir home)
         (filter #(or (str/starts-with? % ".claude")
                      (str/includes? % "claude")
                      (str/starts-with? % ".codex")
                      (str/includes? % "codex")))
         (map #(path/join home %))
         (filter is-dir?))))

(defn find-thread-files []
  "Find all JSONL thread files."
  (->> (find-claude-dirs)
       (mapcat (fn [dir]
                 (let [walk (fn walk [d]
                              (when (is-dir? d)
                                (let [entries (list-dir d)]
                                  (mapcat (fn [e]
                                            (let [full (path/join d e)]
                                              (if (is-dir? full)
                                                (walk full)
                                                (when (str/ends-with? e ".jsonl")
                                                  [full]))))
                                          entries))))]
                   (walk dir))))))

(defn lazy-claude-snapshot []
  "Create lazy snapshot of all claude directories."
  {:dirs (find-claude-dirs)
   :threads (find-thread-files)
   :captured-at (js/Date.now)})

;;; ============================================================
;;; Ruler Config Loading
;;; ============================================================

(defn load-ruler-config [dir]
  "Load .ruler/ruler.toml from directory."
  (let [toml-path (path/join dir ".ruler" "ruler.toml")
        content (read-file toml-path)]
    (when content
      (parse-toml content))))

(defn find-skills [dir]
  "Find all skills in .ruler/skills/."
  (let [skills-dir (path/join dir ".ruler" "skills")]
    (when (is-dir? skills-dir)
      (->> (list-dir skills-dir)
           (map #(path/join skills-dir %))
           (filter is-dir?)
           (map (fn [d]
                  (let [skill-md (path/join d "SKILL.md")]
                    (when (fs/existsSync skill-md)
                      {:name (path/basename d)
                       :path d
                       :skill-md skill-md}))))
           (filter some?)))))

;;; ============================================================
;;; MCP Config Generation
;;; ============================================================

(defn generate-claude-mcp-config [config]
  (let [servers (get config "mcp_servers" {})]
    {:mcpServers
     (into {}
       (for [[name server] servers]
         [name {:command (get server "command")
                :args (get server "args" [])
                :env (get server "env" {})}]))}))

(defn generate-codex-mcp-config [config]
  (let [servers (get config "mcp_servers" {})]
    {:mcpServers
     (into {}
       (for [[name server] servers]
         [name {:command (get server "command")
                :args (get server "args" [])}]))}))

;;; ============================================================
;;; GF(3) Bisimulation
;;; ============================================================

(def GF3-POLARITIES
  {"PLUS" 1 "ERGODIC" 0 "MINUS" -1})

(defn bisimulation-balance [config]
  (let [agents (get-in config ["bisimulation" "agents"] {})
        sum (reduce + (map #(get GF3-POLARITIES % 0) (vals agents)))]
    {:sum sum
     :balanced (zero? (mod sum 3))
     :agents (into {} (for [[k v] agents] [k (get GF3-POLARITIES v 0)]))}))

;;; ============================================================
;;; Flow Handlers (GF(3))
;;; ============================================================

(defmulti handle-flow :direction)

(defmethod handle-flow :inject
  [{:keys [op payload]}]
  (update-trit! +1)
  (swap! ruler-state update :ops conj {:op op :trit +1 :ts (js/Date.now)})
  (case op
    :load-config (let [config (load-ruler-config (or (:dir payload) "."))]
                   (swap! ruler-state assoc :config config)
                   {:status :loaded :mcp-count (count (get config "mcp_servers" {}))})
    :load-skills (let [skills (find-skills (or (:dir payload) "."))]
                   (swap! ruler-state assoc :skills skills)
                   {:status :loaded :skill-count (count skills)})
    :sync        (let [dir (or (:dir payload) ".")
                       config (load-ruler-config dir)
                       skills (find-skills dir)]
                   (swap! ruler-state merge {:config config :skills skills})
                   {:status :synced
                    :skills (count skills)
                    :mcp-servers (count (get config "mcp_servers" {}))})
    :claude-snapshot (lazy-claude-snapshot)
    {:status :injected :op op}))

(defmethod handle-flow :emit
  [{:keys [op payload]}]
  (update-trit! -1)
  (case op
    :state        @ruler-state
    :config       (:config @ruler-state)
    :skills       (:skills @ruler-state)
    :mcp-servers  (get-in @ruler-state [:config "mcp_servers"] {})
    :claude-json  (generate-claude-mcp-config (:config @ruler-state))
    :codex-json   (generate-codex-mcp-config (:config @ruler-state))
    :trit         {:trit (:trit @ruler-state) :balanced (zero? (:trit @ruler-state))}
    :bisim        (bisimulation-balance (:config @ruler-state))
    :claude-dirs  (find-claude-dirs)
    {:emitted op}))

(defmethod handle-flow :bridge
  [{:keys [op payload]}]
  (update-trit! 0)
  (case op
    :toml->edn   (parse-toml payload)
    :config->json (js/JSON.stringify (clj->js (:config @ruler-state)) nil 2)
    :skills->xml  (str "<available_skills>\n"
                       (str/join "\n"
                         (for [s (:skills @ruler-state)]
                           (str "  <skill><name>" (:name s) "</name></skill>")))
                       "\n</available_skills>")
    {:bridged payload}))

(defmethod handle-flow :default
  [flow]
  {:error :unknown-direction :flow flow})

;;; ============================================================
;;; S-expression Protocol
;;; ============================================================

(defn parse-flow-sexp [sexp]
  (let [[tag direction op payload] sexp]
    (when (= tag :flow)
      {:direction direction :op op :payload payload})))

(defn process-sexp [sexp]
  (try
    (if-let [flow (parse-flow-sexp sexp)]
      (handle-flow flow)
      ;; Direct command
      (case (first sexp)
        :sync (handle-flow {:direction :inject :op :sync :payload {:dir (second sexp)}})
        :config (handle-flow {:direction :emit :op :config :payload nil})
        :skills (handle-flow {:direction :emit :op :skills :payload nil})
        :mcp (handle-flow {:direction :emit :op :mcp-servers :payload nil})
        :claude-json (handle-flow {:direction :emit :op :claude-json :payload nil})
        :codex-json (handle-flow {:direction :emit :op :codex-json :payload nil})
        :claude-dirs (handle-flow {:direction :emit :op :claude-dirs :payload nil})
        :trit (handle-flow {:direction :emit :op :trit :payload nil})
        {:unknown-command (first sexp)}))
    (catch :default e
      {:error (.-message e)})))

;;; ============================================================
;;; ACP/MCP Protocol
;;; ============================================================

(def mcp-tools
  {"ruler.sync"        {:description "Sync ruler config to agents"
                        :handler (fn [args] (handle-flow {:direction :inject :op :sync :payload args}))}
   "ruler.config"      {:description "Get ruler config"
                        :handler (fn [_] (handle-flow {:direction :emit :op :config :payload nil}))}
   "ruler.skills"      {:description "List available skills"
                        :handler (fn [_] (handle-flow {:direction :emit :op :skills :payload nil}))}
   "ruler.mcp-servers" {:description "List MCP servers"
                        :handler (fn [_] (handle-flow {:direction :emit :op :mcp-servers :payload nil}))}
   "ruler.claude-json" {:description "Generate Claude MCP config"
                        :handler (fn [_] (handle-flow {:direction :emit :op :claude-json :payload nil}))}
   "ruler.codex-json"  {:description "Generate Codex MCP config"
                        :handler (fn [_] (handle-flow {:direction :emit :op :codex-json :payload nil}))}
   "ruler.bisim"       {:description "Check GF(3) bisimulation balance"
                        :handler (fn [_] (handle-flow {:direction :emit :op :bisim :payload nil}))}
   "ruler.claude-dirs" {:description "Find all claude directories"
                        :handler (fn [_] (handle-flow {:direction :emit :op :claude-dirs :payload nil}))}})

(defn handle-mcp-request [{:keys [method params id]}]
  {:jsonrpc "2.0"
   :id id
   :result
   (case method
     "tools/list" {:tools (mapv (fn [[name {:keys [description]}]]
                                  {:name name :description description})
                                mcp-tools)}
     "tools/call" (let [{:keys [name arguments]} params
                        tool (get mcp-tools name)]
                    (if tool
                      ((:handler tool) arguments)
                      {:error {:code -32601 :message (str "Unknown tool: " name)}}))
     "resources/list" {:resources [{:uri "ruler://config" :name "Ruler Config"}
                                   {:uri "ruler://skills" :name "Skills"}
                                   {:uri "ruler://mcp-servers" :name "MCP Servers"}]}
     {:error {:code -32601 :message "Method not found"}})})

;;; ============================================================
;;; Communication Modes
;;; ============================================================

(defn stdin-loop []
  "Read S-expressions from stdin, write results to stdout"
  (let [rl (js/require "readline")
        interface (.createInterface rl #js {:input js/process.stdin
                                            :output js/process.stdout
                                            :terminal false})]
    (.on interface "line"
         (fn [line]
           (when (seq (str/trim line))
             (try
               (let [input (edn/read-string line)
                     result (process-sexp input)]
                 (println (pr-str result)))
               (catch :default e
                 (println (pr-str {:error (.-message e)})))))))))

(defn mcp-stdio-loop []
  "Run as MCP server on stdio (JSON-RPC)"
  (let [rl (js/require "readline")
        interface (.createInterface rl #js {:input js/process.stdin
                                            :output js/process.stdout
                                            :terminal false})]
    (.on interface "line"
         (fn [line]
           (when (seq (str/trim line))
             (try
               (let [request (js->clj (js/JSON.parse line) :keywordize-keys true)
                     response (handle-mcp-request request)]
                 (println (js/JSON.stringify (clj->js response))))
               (catch :default e
                 (println (js/JSON.stringify #js {:error (.-message e)})))))))))

;;; ============================================================
;;; CLI
;;; ============================================================

(defn -main [& args]
  (let [mode (first args)]
    (case mode
      "--mcp"   (mcp-stdio-loop)
      "--stdin" (stdin-loop)
      "--sync"  (let [dir (or (second args) ".")]
                  (println (pr-str (process-sexp [:sync dir]))))
      "--claude-json" (do
                        (process-sexp [:sync (or (second args) ".")])
                        (println (js/JSON.stringify
                                   (clj->js (process-sexp [:claude-json]))
                                   nil 2)))
      "--codex-json"  (do
                        (process-sexp [:sync (or (second args) ".")])
                        (println (js/JSON.stringify
                                   (clj->js (process-sexp [:codex-json]))
                                   nil 2)))
      "--claude-dirs" (println (pr-str (process-sexp [:claude-dirs])))
      "--test"  (do
                  (println "Testing Ruler NBB:")
                  (println "INJECT sync:" (pr-str (process-sexp [:sync "."])))
                  (println "EMIT config:" (pr-str (process-sexp [:config])))
                  (println "EMIT trit:" (pr-str (process-sexp [:trit])))
                  (println "BRIDGE config->json:" (handle-flow {:direction :bridge :op :config->json :payload nil})))
      ;; Default: stdin mode for S-expression protocol
      (stdin-loop))))

;; Auto-start
(apply -main (js->clj (vec (.slice js/process.argv 2))))
