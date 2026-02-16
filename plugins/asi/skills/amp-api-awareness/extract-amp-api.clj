#!/usr/bin/env bb
;; Amp API Awareness - Thread Extraction Script
;; Usage: bb extract-amp-api.clj [--export-db] [--stats] [--tools]

(require '[babashka.fs :as fs]
         '[cheshire.core :as json]
         '[clojure.string :as str])

(def threads-dir (fs/expand-home "~/.local/share/amp/threads"))
(def history-file (fs/expand-home "~/.claude/history.jsonl"))

(defn load-threads [limit]
  (let [files (take (or limit 999999) (fs/glob threads-dir "T-*.json"))]
    (->> files
         (pmap (fn [f]
                 (try
                   (json/parse-string (slurp (str f)) true)
                   (catch Exception _ nil))))
         (filter some?))))

(defn extract-tools [threads]
  (->> threads
       (mapcat :messages)
       (mapcat :content)
       (filter #(= (:type %) "tool_use"))
       (map :name)
       frequencies
       (sort-by val >)))

(defn extract-mcp-servers [tool-counts]
  (->> tool-counts
       (filter #(str/starts-with? (first %) "mcp__"))
       (map (fn [[tool cnt]]
              [(second (re-find #"^mcp__([^_]+)__" tool)) cnt]))
       (group-by first)
       (map (fn [[server pairs]] [server (reduce + (map second pairs))]))
       (sort-by second >)))

(defn thread-stats [threads]
  {:total (count threads)
   :with-title (count (filter :title threads))
   :total-msgs (reduce + (map #(count (:messages %)) threads))
   :agent-modes (frequencies (map :agentMode threads))
   :users (frequencies (map :creatorUserID threads))
   :visibilities (frequencies (map #(get-in % [:env :initial :visibility]) threads))})

(defn print-stats [threads]
  (let [stats (thread-stats threads)
        tools (extract-tools threads)
        mcps (extract-mcp-servers tools)]
    
    (println "╔══════════════════════════════════════════════════════════╗")
    (println "║              AMP API AWARENESS REPORT                    ║")
    (println "╚══════════════════════════════════════════════════════════╝")
    
    (println "\n📊 THREAD STATISTICS")
    (println (format "   Total threads:    %,d" (:total stats)))
    (println (format "   With titles:      %,d" (:with-title stats)))
    (println (format "   Total messages:   %,d" (:total-msgs stats)))
    (println (format "   Avg msgs/thread:  %.1f" (double (/ (:total-msgs stats) (:total stats)))))
    
    (println "\n🤖 AGENT MODES")
    (doseq [[mode cnt] (sort-by val > (:agent-modes stats))]
      (println (format "   %-15s %,d" (or mode "nil") cnt)))
    
    (println "\n👥 USERS (by creatorUserID)")
    (doseq [[user cnt] (sort-by val > (:users stats))]
      (println (format "   %-35s %,d threads" (or user "nil") cnt)))
    
    (println "\n👁️ VISIBILITY")
    (doseq [[vis cnt] (sort-by val > (:visibilities stats))]
      (println (format "   %-15s %,d" (or vis "nil") cnt)))
    
    (println "\n🔧 CORE TOOLS (top 15)")
    (doseq [[tool cnt] (take 15 (filter #(not (str/starts-with? (first %) "mcp__")) tools))]
      (println (format "   %-25s %,d" tool cnt)))
    
    (println "\n🔌 MCP SERVERS")
    (doseq [[server cnt] (take 12 mcps)]
      (println (format "   %-20s %,d invocations" (or server "unknown") cnt)))
    
    (println "\n🎯 TOP MCP FUNCTIONS")
    (doseq [[tool cnt] (take 15 (filter #(str/starts-with? (first %) "mcp__") tools))]
      (println (format "   %-45s %,d" tool cnt)))))

(defn export-to-duckdb [threads output-path]
  (let [rows (map (fn [t]
                    {:id (:id t)
                     :title (:title t)
                     :created (:created t)
                     :msg_count (count (:messages t))
                     :agent_mode (:agentMode t)
                     :trit (- (mod (Math/abs (hash (:id t))) 3) 1)})
                  threads)]
    (spit output-path (str/join "\n" (map json/generate-string rows)))
    (println (format "Exported %d threads to %s" (count rows) output-path))))

;; Main
(let [args (set *command-line-args*)
      threads (load-threads (when (args "--limit") 500))]
  
  (cond
    (args "--export-db")
    (export-to-duckdb threads "amp-threads-export.jsonl")
    
    (args "--tools")
    (doseq [[tool cnt] (extract-tools threads)]
      (println (format "%s\t%d" tool cnt)))
    
    :else
    (print-stats threads)))
