#!/usr/bin/env bb
;; src/apt_detector/clerk_reactive_watcher.clj
;;
;; CLERK-STYLE REACTIVE FILE WATCHER
;; 
;; Semantic differences between observation methods:
;;
;; ┌─────────────────┬─────────────────────────────────────────────────────────┐
;; │ Method          │ Semantic Meaning                                        │
;; ├─────────────────┼─────────────────────────────────────────────────────────┤
;; │ babashka.fs     │ Java NIO → JVM abstraction → kernel syscalls            │
;; │ stat(1)         │ libc stat() → direct syscall → kernel VFS               │
;; │ ls(1)           │ readdir() + stat() → different syscall path             │
;; │ find(1)         │ nftw() → recursive traversal → different caching        │
;; │ GetFileInfo     │ macOS Carbon API → deprecated but different path        │
;; │ mdls            │ Spotlight metadata → async index, may lag               │
;; └─────────────────┴─────────────────────────────────────────────────────────┘
;;
;; A rootkit that hooks stat() might not hook nftw().
;; A rootkit that hooks VFS might not hook Spotlight.
;; SEMANTIC DIFFERENCING detects these gaps.

(ns apt-detector.clerk-reactive-watcher
  (:require [babashka.fs :as fs]
            [babashka.process :as proc]
            [clojure.string :as str]
            [clojure.edn :as edn]
            [clojure.java.io :as io]))

;; ═══════════════════════════════════════════════════════════════════════════
;; OBSERVATION METHODS (Each uses different syscall paths)
;; ═══════════════════════════════════════════════════════════════════════════

(def observation-methods
  {:nio       {:trit 0  :syscall "stat64/getattrlist" :layer "JVM NIO"}
   :stat-cmd  {:trit -1 :syscall "stat64"             :layer "libc"}
   :ls-cmd    {:trit 1  :syscall "readdir+stat"       :layer "libc"}
   :find-cmd  {:trit 0  :syscall "nftw"               :layer "libc"}
   :mdls-cmd  {:trit -1 :syscall "spotlight"          :layer "launchd"}
   :xattr-cmd {:trit 1  :syscall "listxattr"          :layer "VFS"}})

(defn observe-nio [path]
  (when (fs/exists? path)
    (let [attrs (fs/read-attributes path "*")
          unix (try (fs/read-attributes path "unix:*") (catch Exception _ {}))]
      {:method :nio
       :exists true
       :size (get attrs :size)
       :mtime-raw (get attrs :lastModifiedTime)
       :mtime (str (get attrs :lastModifiedTime))
       :inode (get unix :ino)
       :mode (get unix :mode)
       :uid (get unix :uid)
       :gid (get unix :gid)})))

(defn observe-stat-cmd [path]
  (try
    (let [r (proc/shell {:out :string} "stat" "-f" "%i|%z|%m|%a|%c|%p|%u|%g" (str path))
          [inode size mtime atime ctime mode uid gid] (str/split (str/trim (:out r)) #"\|")]
      {:method :stat-cmd
       :exists true
       :inode (parse-long inode)
       :size (parse-long size)
       :mtime mtime
       :atime atime
       :ctime ctime
       :mode mode
       :uid (parse-long uid)
       :gid (parse-long gid)})
    (catch Exception _ {:method :stat-cmd :exists false})))

(defn observe-ls-cmd [path]
  (try
    (let [r (proc/shell {:out :string} "ls" "-lid" (str path))
          parts (str/split (str/trim (:out r)) #"\s+" 9)]
      {:method :ls-cmd
       :exists true
       :inode (parse-long (nth parts 0))
       :mode-str (nth parts 1)
       :nlink (parse-long (nth parts 2))
       :owner (nth parts 3)
       :group (nth parts 4)
       :size (parse-long (nth parts 5))})
    (catch Exception _ {:method :ls-cmd :exists false})))

(defn observe-mdls [path]
  (try
    (let [r (proc/shell {:out :string} "mdls" "-name" "kMDItemFSSize" 
                        "-name" "kMDItemFSCreationDate"
                        "-name" "kMDItemContentModificationDate" (str path))
          lines (str/split-lines (:out r))
          parse-val (fn [l] (when-let [m (re-find #"=\s*(.+)$" l)]
                              (str/trim (second m))))]
      {:method :mdls
       :exists true
       :spotlight-size (parse-val (first (filter #(str/includes? % "FSSize") lines)))
       :spotlight-created (parse-val (first (filter #(str/includes? % "Creation") lines)))
       :spotlight-modified (parse-val (first (filter #(str/includes? % "Modification") lines)))})
    (catch Exception _ {:method :mdls :exists false})))

(defn observe-xattr [path]
  (try
    (let [r (proc/shell {:out :string} "xattr" "-l" (str path))
          attrs (str/split-lines (:out r))]
      {:method :xattr
       :exists true
       :xattr-count (count (filter #(str/starts-with? % "com.") attrs))
       :has-provenance (some #(str/includes? % "provenance") attrs)
       :has-quarantine (some #(str/includes? % "quarantine") attrs)})
    (catch Exception _ {:method :xattr :exists false :xattr-count 0})))

(defn observe-getfileinfo [path]
  (try
    (let [r (proc/shell {:out :string} "GetFileInfo" (str path))
          lines (str/split-lines (:out r))
          extract (fn [k] (some #(when (str/starts-with? % k)
                                   (str/trim (subs % (count k)))) lines))]
      {:method :getfileinfo
       :exists true
       :type (extract "type:")
       :creator (extract "creator:")
       :attributes (extract "attributes:")
       :created (extract "created:")
       :modified (extract "modified:")})
    (catch Exception _ {:method :getfileinfo :exists false})))

;; ═══════════════════════════════════════════════════════════════════════════
;; PARALLEL OBSERVATION ENGINE
;; ═══════════════════════════════════════════════════════════════════════════

(defn observe-all-parallel [path]
  (let [start (System/nanoTime)
        futures [(future (observe-nio path))
                 (future (observe-stat-cmd path))
                 (future (observe-ls-cmd path))
                 (future (observe-mdls path))
                 (future (observe-xattr path))
                 (future (observe-getfileinfo path))]
        results (mapv deref futures)
        elapsed-ns (- (System/nanoTime) start)]
    {:path (str path)
     :observations (into {} (map (juxt :method identity) results))
     :elapsed-us (quot elapsed-ns 1000)
     :timestamp (System/currentTimeMillis)
     :observation-count (count (filter :exists results))}))

;; ═══════════════════════════════════════════════════════════════════════════
;; SEMANTIC DIFFERENCING
;; ═══════════════════════════════════════════════════════════════════════════

(defn semantic-diff
  "Find semantic differences between observations"
  [obs-result]
  (let [obs (:observations obs-result)
        
        ;; Size comparison (most critical for integrity)
        sizes (->> [:nio :stat-cmd :ls-cmd]
                   (map #(get-in obs [% :size]))
                   (remove nil?)
                   distinct)
        size-diff? (> (count sizes) 1)
        
        ;; Inode comparison (different = possible hardlink shenanigans)
        inodes (->> [:nio :stat-cmd :ls-cmd]
                    (map #(get-in obs [% :inode]))
                    (remove nil?)
                    distinct)
        inode-diff? (> (count inodes) 1)
        
        ;; Existence discrepancy (some methods see it, others don't)
        exists-map (->> (keys obs)
                        (map (fn [k] [k (get-in obs [k :exists])]))
                        (into {}))
        existence-diff? (> (count (distinct (vals exists-map))) 1)
        
        ;; Spotlight lag detection (metadata index behind filesystem)
        spotlight-size (get-in obs [:mdls :spotlight-size])
        real-size (get-in obs [:stat-cmd :size])
        spotlight-stale? (and spotlight-size real-size
                              (not= spotlight-size (str real-size))
                              (not= spotlight-size "(null)"))
        
        ;; Provenance/quarantine (Gatekeeper tracking)
        has-provenance? (get-in obs [:xattr :has-provenance])
        has-quarantine? (get-in obs [:xattr :has-quarantine])]
    
    {:path (:path obs-result)
     :checks {:size-consistent? (not size-diff?)
              :inode-consistent? (not inode-diff?)
              :existence-consistent? (not existence-diff?)
              :spotlight-current? (not spotlight-stale?)
              :gatekeeper-tracked? (or has-provenance? has-quarantine?)}
     :anomalies (cond-> []
                  size-diff? (conj {:type :size-mismatch :values sizes})
                  inode-diff? (conj {:type :inode-mismatch :values inodes})
                  existence-diff? (conj {:type :existence-mismatch :values exists-map})
                  spotlight-stale? (conj {:type :spotlight-stale 
                                          :spotlight spotlight-size 
                                          :actual real-size}))
     :clean? (and (not size-diff?) (not inode-diff?) (not existence-diff?))
     :observations obs}))

;; ═══════════════════════════════════════════════════════════════════════════
;; CONTINUOUS MONITORING (Clerk-style reactive)
;; ═══════════════════════════════════════════════════════════════════════════

(defn monitor-loop
  "Continuously monitor files, detecting changes between polls"
  [paths {:keys [interval-ms max-iterations] :or {interval-ms 2000 max-iterations 10}}]
  (loop [iteration 0
         prev-state {}
         anomalies []]
    (when (< iteration max-iterations)
      (let [current-results (pmap (fn [p]
                                    (-> (observe-all-parallel p)
                                        semantic-diff))
                                  paths)
            current-state (into {} (map (juxt :path identity) current-results))
            
            ;; Detect changes from previous state
            changes (for [[path result] current-state
                          :let [prev (get prev-state path)]
                          :when (and prev
                                     (not= (get-in prev [:observations :stat-cmd :mtime])
                                           (get-in result [:observations :stat-cmd :mtime])))]
                      {:path path
                       :change-type :mtime-changed
                       :prev-mtime (get-in prev [:observations :stat-cmd :mtime])
                       :new-mtime (get-in result [:observations :stat-cmd :mtime])
                       :iteration iteration})
            
            new-anomalies (concat anomalies
                                  (mapcat :anomalies current-results)
                                  changes)]
        
        (println (format "[%d] Monitored %d files | Anomalies: %d | Changes: %d"
                         iteration (count paths) 
                         (count (mapcat :anomalies current-results))
                         (count changes)))
        
        (Thread/sleep interval-ms)
        (recur (inc iteration) current-state new-anomalies)))))

;; ═══════════════════════════════════════════════════════════════════════════
;; REPORT GENERATION
;; ═══════════════════════════════════════════════════════════════════════════

(defn generate-report [paths]
  (println "╔═══════════════════════════════════════════════════════════════════════════════╗")
  (println "║  SEMANTIC DIFFERENCING FILE OBSERVER                                         ║")
  (println "║  Parallel observation via 6 methods with different syscall paths             ║")
  (println "╚═══════════════════════════════════════════════════════════════════════════════╝")
  (println)
  (println "Methods: NIO(stat64) | stat(1) | ls(1) | mdls(spotlight) | xattr | GetFileInfo")
  (println)
  
  (let [results (pmap (fn [p] (-> (observe-all-parallel p) semantic-diff)) paths)
        clean (filter :clean? results)
        dirty (remove :clean? results)]
    
    (println (format "─── SCAN RESULTS: %d files ───" (count results)))
    (println (format "  ✓ Clean: %d" (count clean)))
    (println (format "  ⚠ Anomalies: %d" (count dirty)))
    (println)
    
    (when (seq dirty)
      (println "─── ANOMALIES DETECTED ───")
      (doseq [r dirty]
        (println (format "\n  %s:" (:path r)))
        (doseq [a (:anomalies r)]
          (case (:type a)
            :size-mismatch (println (format "    SIZE MISMATCH: %s" (:values a)))
            :inode-mismatch (println (format "    INODE MISMATCH: %s" (:values a)))
            :existence-mismatch (println (format "    EXISTENCE MISMATCH: %s" (:values a)))
            :spotlight-stale (println (format "    SPOTLIGHT STALE: index=%s actual=%s" 
                                              (:spotlight a) (:actual a)))
            (println (format "    %s: %s" (:type a) a))))))
    
    (println)
    (println "─── SAMPLE OBSERVATION (first file) ───")
    (when-let [sample (first results)]
      (let [obs (:observations sample)]
        (doseq [[method data] obs]
          (println (format "  %s:" (name method)))
          (println (format "    size=%s inode=%s exists=%s"
                           (or (:size data) (:spotlight-size data) "?")
                           (or (:inode data) "?")
                           (:exists data))))))
    
    {:total (count results)
     :clean (count clean)
     :anomalies (count dirty)
     :dirty-paths (map :path dirty)}))

(defn -main [& args]
  (let [paths (if (seq args)
                (if (fs/directory? (first args))
                  (take 10 (filter fs/regular-file? (fs/list-dir (first args))))
                  args)
                (take 10 (filter fs/regular-file? (fs/list-dir "lib"))))]
    (generate-report (map str paths))))

(when (= *file* (System/getProperty "babashka.file"))
  (-main))
