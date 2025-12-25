#!/usr/bin/env bb
;; SCUM - System Consumption Utilization Monitor
;; Libkind-style compositional resource management with GF(3) classification

(require '[clojure.string :as str]
         '[babashka.process :refer [shell process]])

(def ^:dynamic *alpha* 0.4)  ; MEM weight
(def ^:dynamic *beta*  0.2)  ; CPU weight  
(def ^:dynamic *gamma* 0.2)  ; TIME weight
(def ^:dynamic *delta* 0.2)  ; STALE weight

(defn parse-mem [s]
  "Parse memory string like '5361M' or '2G' to MB"
  (try
    (let [s (str/trim (str s))]
      (cond
        (str/ends-with? s "G") (* 1024 (or (parse-double (subs s 0 (dec (count s)))) 0))
        (str/ends-with? s "M") (or (parse-double (subs s 0 (dec (count s)))) 0)
        (str/ends-with? s "K") (/ (or (parse-double (subs s 0 (dec (count s)))) 0) 1024)
        (str/ends-with? s "+") (or (parse-double (subs s 0 (dec (count s)))) 0)
        :else (or (parse-double s) 0)))
    (catch Exception _ 0)))

(defn parse-time [s]
  "Parse time string like '02:49:16' to seconds"
  (try
    (let [parts (str/split (str s) #":")]
      (case (count parts)
        3 (+ (* 3600 (or (parse-long (first parts)) 0))
             (* 60 (or (parse-long (second parts)) 0))
             (or (parse-long (last parts)) 0))
        2 (+ (* 60 (or (parse-long (first parts)) 0))
             (or (parse-long (last parts)) 0))
        1 (or (parse-long (first parts)) 0)
        0))
    (catch Exception _ 0)))

(defn get-total-mem []
  "Get total system memory in MB"
  (-> (shell {:out :string} "sysctl" "-n" "hw.memsize")
      :out
      str/trim
      parse-long
      (/ 1024 1024)))

(defn get-processes []
  "Get process list from top"
  (let [output (-> (shell {:out :string} "top" "-l" "1" "-stats" "pid,command,cpu,mem,time" "-o" "mem" "-n" "50")
                   :out
                   str/split-lines)]
    (->> output
         (drop-while #(not (str/starts-with? % "PID")))
         (drop 1)
         (take 40)
         (map str/trim)
         (filter #(> (count %) 5))
         (map #(str/split % #"\s+"))
         (filter #(>= (count %) 5))
         (map (fn [[pid cmd cpu mem time & _]]
                {:pid pid
                 :cmd cmd
                 :cpu (try (parse-double cpu) (catch Exception _ 0))
                 :mem-str mem
                 :mem (parse-mem mem)
                 :time-str (or time "0")
                 :time (parse-time (or time "0"))})))))

(defn calc-scum [{:keys [mem cpu time]} total-mem]
  "Calculate SCUM score 0-100"
  (let [mem-norm (/ (or mem 0) total-mem)
        cpu-norm (/ (or cpu 0) 100)
        time-norm (min 1.0 (/ (or time 0) 7200))  ; 2 hour baseline
        stale-norm 0.0]
    (int (min 100 (* 100 (+ (* *alpha* mem-norm)
                            (* *beta* cpu-norm)
                            (* *gamma* time-norm)
                            (* *delta* stale-norm)))))))

(defn scum-trit [score]
  "Map SCUM score to GF(3) trit"
  (cond
    (< score 34) {:trit +1 :label "HEALTHY" :color "\u001b[32m"}   ; Green
    (< score 67) {:trit 0  :label "MONITOR" :color "\u001b[33m"}   ; Yellow
    :else        {:trit -1 :label "TERMINATE" :color "\u001b[31m"})) ; Red

(defn report []
  "Print SCUM report"
  (let [total-mem (get-total-mem)
        procs (get-processes)]
    (println "\n\u001b[1m=== SCUM REPORT ===\u001b[0m")
    (printf "Total Memory: %d MB\n\n" (long total-mem))
    (println "PID\tSCUM\tSTATUS\t\tMEM\tCPU%\tCOMMAND")
    (println "---\t----\t------\t\t---\t----\t-------")
    (doseq [p (sort-by :mem > procs)]
      (let [scum (calc-scum p total-mem)
            {:keys [color label]} (scum-trit scum)]
        (printf "%s\t%d\t%s%s\u001b[0m\t%s\t%.1f\t%s%n"
                (:pid p) scum color label (:mem-str p) (:cpu p) (:cmd p))))
    (println)))

(defn kill-scum [threshold & {:keys [dry-run pattern]}]
  "Kill processes above SCUM threshold"
  (let [total-mem (get-total-mem)
        procs (get-processes)
        targets (->> procs
                     (filter #(>= (calc-scum % total-mem) threshold))
                     (filter #(if pattern 
                                (re-find (re-pattern pattern) (:cmd %))
                                true))
                     (filter #(not (#{"WindowServer" "kernel_task" "launchd" "Finder"} (:cmd %)))))]
    (if (empty? targets)
      (println (format "No processes above SCUM threshold %d" threshold))
      (doseq [p targets]
        (let [scum (calc-scum p total-mem)]
          (if dry-run
            (printf "[DRY RUN] Would kill PID %s (%s) SCUM=%d MEM=%s%n"
                    (:pid p) (:cmd p) scum (:mem-str p))
            (do
              (printf "Killing PID %s (%s) SCUM=%d MEM=%s%n"
                      (:pid p) (:cmd p) scum (:mem-str p))
              (shell "kill" "-9" (:pid p)))))))))

(defn usage []
  (println "
SCUM - System Consumption Utilization Monitor

Usage:
  scum             Show SCUM report
  scum kill N      Kill processes with SCUM >= N
  scum kill N -n   Dry run (show what would be killed)
  scum kill N -p P Kill matching pattern P above threshold

Options:
  -n, --dry-run    Don't actually kill, just show
  -p, --pattern P  Only kill processes matching regex P
"))

;; Main dispatch
(let [args *command-line-args*]
  (case (first args)
    nil     (report)
    "report" (report)
    "kill"  (let [threshold (parse-long (second args))
                  dry-run (some #{"-n" "--dry-run"} args)
                  pattern-idx (.indexOf (vec args) "-p")
                  pattern (when (pos? pattern-idx) (nth args (inc pattern-idx) nil))]
              (kill-scum threshold :dry-run dry-run :pattern pattern))
    "help"  (usage)
    "-h"    (usage)
    "--help" (usage)
    (do (println "Unknown command:" (first args))
        (usage))))
