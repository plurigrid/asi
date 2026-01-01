#!/usr/bin/env bb
;; increment_69h_crdt_sexp.bb
;; Generate 69-hour filesystem increment as CRDT-style s-expressions
;; Inspired by crdt.el's remote-insert/remote-delete conflict resolution
;; with GF(3) coloring for trifurcation analysis

(require '[babashka.fs :as fs])
(require '[clojure.string :as str])
(require '[clojure.java.io :as io])

(def HOURS 69)
(def THRESHOLD_MS 248400000)  ;; 69 * 60 * 60 * 1000 ms
(def IES_ROOT (or (System/getenv "IES_ROOT") (str (fs/parent (fs/parent (fs/cwd))))))

;; SplitMix64-style hash for deterministic GF(3) coloring (simplified for bb)
(defn splitmix64-hash [seed]
  (let [h (bit-xor seed (bit-shift-right seed 16))]
    (bit-and h 0x7FFFFFFF)))  ;; Keep positive

(defn gf3-trit [^long hash]
  "Extract GF(3) trit: -1 (MINUS), 0 (ERGODIC), +1 (PLUS)"
  (let [r (mod (Math/abs hash) 3)]
    (case r
      0 :MINUS
      1 :ERGODIC
      2 :PLUS)))

(defn file->crdt-id [path mtime]
  "Generate CRDT-style ID from path and mtime"
  (let [seed (hash (str path ":" mtime))
        sm (splitmix64-hash seed)]
    {:id (format "%08x" sm)
     :site (mod (Math/abs (hash path)) 0xFFFF)
     :offset mtime
     :trit (gf3-trit sm)}))

(defn classify-operation [path]
  "Classify file operation type based on content/extension"
  (let [ext (fs/extension path)
        name (fs/file-name path)]
    (cond
      (str/ends-with? name ".json") :data
      (str/ends-with? name ".md") :doc
      (str/ends-with? name ".py") :code-python
      (str/ends-with? name ".jl") :code-julia
      (str/ends-with? name ".bb") :code-babashka
      (str/ends-with? name ".el") :code-elisp
      (str/ends-with? name ".txt") :text
      (str/ends-with? name ".sql") :query
      (str/ends-with? name ".hy") :code-hy
      :else :other)))

(defn detect-conflict-potential [files-in-hour]
  "Detect potential CRDT conflicts: files modified within same hour"
  (let [by-dir (group-by #(fs/parent (:path %)) files-in-hour)]
    (->> by-dir
         (filter #(> (count (val %)) 1))
         (mapcat (fn [[dir files]]
                   (when (> (count files) 2)
                     [{:type :no-longer-optimistic-wait
                       :dir (str dir)
                       :files (mapv :path files)
                       :resolution :trifurcate-by-trit}]))))))

(defn file-entry [path]
  (try
    (let [f (io/file path)
          mtime-millis (.lastModified f)
          crdt-id (file->crdt-id (str path) mtime-millis)]
      {:path (str path)
       :relative (str/replace (str path) (str IES_ROOT "/") "")
       :mtime mtime-millis
       :mtime-iso (str (java.time.Instant/ofEpochMilli mtime-millis))
       :size (.length f)
       :op-type (classify-operation path)
       :crdt-id crdt-id})
    (catch Exception e nil)))

;; Gather all modified files
(defn gather-increment []
  (let [now (System/currentTimeMillis)
        cutoff (- now THRESHOLD_MS)
        all-files (file-seq (io/file IES_ROOT))
        raw-files (->> all-files
                       (filter #(.isFile %))
                       (filter #(not (str/includes? (str %) "/.git/")))
                       (filter #(not (str/includes? (str %) "/node_modules/")))
                       (filter #(not (str/includes? (str %) "/.venv/")))
                       (filter #(not (str/includes? (str %) "/target/")))  ;; Skip Rust/cargo build dirs
                       (filter #(not (str/includes? (str %) "/.cache/")))
                       (filter #(not (str/includes? (str %) "__pycache__")))
                       (filter #(> (.lastModified %) cutoff))
                       (take 5000)
                       vec)]
    (binding [*err* *out*]
      (println ";; DEBUG: Found" (count raw-files) "raw files within 69h"))
    (->> raw-files
         (mapv #(file-entry (str %)))
         (filterv identity)
         (sort-by :mtime)
         vec)))

;; CRDT-style sexp output format
(defn entry->sexp [{:keys [path relative mtime-iso size op-type crdt-id]}]
  `(~'remote-insert
    ~(:id crdt-id)
    ~(:site crdt-id)
    ~relative
    (~'props
     ~(keyword "type") ~op-type
     ~(keyword "size") ~size
     ~(keyword "mtime") ~mtime-iso
     ~(keyword "trit") ~(:trit crdt-id))))

(defn conflict->sexp [{:keys [type dir files resolution]}]
  `(~'conflict-resolution
    ~type
    ~(keyword "dir") ~dir
    ~(keyword "strategy") ~resolution
    (~'conflicting-files ~@(map #(str/replace % (str IES_ROOT "/") "") files))))

;; Group by hour for temporal analysis
(defn group-by-hour [entries]
  (->> entries
       (group-by #(-> (:mtime %)
                      (quot 3600000)
                      (* 3600000)))
       (sort-by key)))

;; GF(3) balance analysis
(defn gf3-balance [entries]
  (let [trits (map #(get-in % [:crdt-id :trit]) entries)
        counts (frequencies trits)]
    {:MINUS (get counts :MINUS 0)
     :ERGODIC (get counts :ERGODIC 0)
     :PLUS (get counts :PLUS 0)
     :balanced? (let [vals (vals counts)]
                  (when (seq vals)
                    (<= (- (apply max vals) (apply min vals)) 
                        (max 1 (/ (count entries) 10)))))}))

(defn format-output []
  (let [entries (gather-increment)
        by-hour (group-by-hour entries)
        conflicts (->> by-hour
                       (mapcat (fn [[_ files]] (detect-conflict-potential files)))
                       (filter identity))
        gf3 (gf3-balance entries)]
    
    {:meta `(~'crdt-increment
             (~'version "0.3.5")
             (~'hours ~HOURS)
             (~'total-entries ~(count entries))
             (~'timestamp ~(str (java.time.Instant/now))))
     
     :gf3-balance `(~'gf3-conservation
                    ~(keyword "MINUS") ~(:MINUS gf3)
                    ~(keyword "ERGODIC") ~(:ERGODIC gf3)
                    ~(keyword "PLUS") ~(:PLUS gf3)
                    ~(keyword "balanced") ~(:balanced? gf3))
     
     :conflicts (mapv conflict->sexp conflicts)
     
     :entries-by-hour
     (into []
           (for [[hour-ts files] by-hour]
             `(~'hour-bucket
               ~(str (java.time.Instant/ofEpochMilli hour-ts))
               ~(keyword "count") ~(count files)
               ~(keyword "gf3") ~(gf3-balance files)
               ~@(map entry->sexp files))))}))

;; Main output
(defn -main []
  (let [output (format-output)]
    (println ";; IES 69-hour increment as CRDT sexps")
    (println ";; Generated:" (str (java.time.Instant/now)))
    (println ";; Like crdt.el conflict resolution with GF(3) trifurcation")
    (println)
    (println ";; Meta")
    (prn (:meta output))
    (println)
    (println ";; GF(3) Conservation")
    (prn (:gf3-balance output))
    (println)
    (println ";; Conflict Resolution (no-longer-optimistic-wait)")
    (doseq [c (:conflicts output)]
      (prn c))
    (println)
    (println ";; Hourly Buckets")
    (doseq [bucket (:entries-by-hour output)]
      (prn bucket)
      (println))))

(-main)
