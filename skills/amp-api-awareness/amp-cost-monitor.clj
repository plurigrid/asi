#!/usr/bin/env bb
;; amp-cost-monitor.clj - Track and alert on Amp usage costs

(require '[babashka.fs :as fs]
         '[cheshire.core :as json])

(def threads-dir (str (System/getProperty "user.home") "/.local/share/amp/threads"))
(def daily-grant 10.0)
(def opus-rate 15.0)  ;; blended $/M tokens

(defn estimate-thread-cost [thread-file]
  (try
    (let [data (json/parse-string (slurp thread-file) true)
          messages (:messages data [])
          msg-count (count messages)
          tokens (* msg-count 800)
          cost (* (/ tokens 1e6) opus-rate)]
      {:id (:id data)
       :title (subs (or (:title data) "untitled") 0 (min 40 (count (or (:title data) ""))))
       :messages msg-count
       :tokens tokens
       :cost cost
       :created (:created data)})
    (catch Exception _ nil)))

(defn today-threads []
  (let [today-start (- (System/currentTimeMillis) (* 24 60 60 1000))
        files (fs/glob threads-dir "*.json")]
    (->> files
         (map str)
         (map estimate-thread-cost)
         (filter some?)
         (filter #(> (:created % 0) today-start))
         (sort-by :created >))))

(defn all-threads []
  (let [files (fs/glob threads-dir "*.json")]
    (->> files
         (map str)
         (map estimate-thread-cost)
         (filter some?)
         (sort-by :created >))))

(defn print-summary [threads label daily?]
  (let [total-cost (reduce + 0 (map :cost threads))
        total-tokens (reduce + 0 (map :tokens threads))
        remaining (when daily? (- daily-grant total-cost))
        pct-used (when daily? (* 100 (/ total-cost daily-grant)))]
    
    (println (str "=== " label " ==="))
    (println (format "Threads: %d" (count threads)))
    (println (format "Tokens: %.1fM" (/ total-tokens 1e6)))
    (if daily?
      (do
        (println (format "Spend: $%.2f / $%.2f (%.0f%%)" total-cost daily-grant pct-used))
        (println (format "Remaining: $%.2f" remaining))
        (when (> pct-used 80)
          (println "\n⚠️  WARNING: Over 80% of daily grant used!")))
      (println (format "Total cost: $%.2f" total-cost)))
    (println)
    
    (when (seq threads)
      (println "Top threads by cost:")
      (doseq [t (take 10 (reverse (sort-by :cost threads)))]
        (println (format "  $%.2f | %4d msgs | %s" 
                         (:cost t) (:messages t) (:title t)))))))

(defn main [& args]
  (let [mode (first args)]
    (case mode
      "all" (print-summary (all-threads) "All Time Costs" false)
      "today" (print-summary (today-threads) "Today's Costs" true)
      (do
        (print-summary (today-threads) "Today's Costs" true)
        (println "\nUsage: bb amp-cost-monitor.clj [today|all]")))))

(apply main *command-line-args*)
