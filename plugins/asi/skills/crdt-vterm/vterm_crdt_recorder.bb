#!/usr/bin/env bb
;; vterm_crdt_recorder.bb
;; Record terminal sessions as CRDT-style sexps for replay/sharing
;; Integrates with crdt.el remote-insert format and GF(3) coloring

(require '[babashka.process :as p])
(require '[clojure.string :as str])
(require '[clojure.java.io :as io])
(require '[clojure.edn :as edn])

(def session-id (str "T-" (java.util.UUID/randomUUID)))
(def start-time (System/currentTimeMillis))
(def site-id (rand-int 65536))

;; GF(3) trit assignment
(defn splitmix64-hash [seed]
  (let [z (bit-xor seed (bit-shift-right seed 16))]
    (bit-and z 0x7FFFFFFF)))

(defn gf3-trit [seed]
  (case (mod (abs (splitmix64-hash seed)) 3)
    0 :MINUS
    1 :ERGODIC
    2 :PLUS))

;; CRDT ID generation
(defn generate-crdt-id [content timestamp]
  (let [combined (str content ":" timestamp)
        hash (splitmix64-hash (hash combined))]
    (format "%08x" hash)))

;; Format as remote-insert sexp
(defn format-remote-insert [content op-type]
  (let [ts (System/currentTimeMillis)
        id (generate-crdt-id content ts)
        trit (gf3-trit (hash content))]
    `(~'remote-insert ~id ~site-id ~content
      (~'props 
       :type ~op-type
       :trit ~trit
       :timestamp ~ts
       :session ~session-id))))

;; Format as remote-input for user input
(defn format-remote-input [input user-id]
  (let [ts (System/currentTimeMillis)
        id (generate-crdt-id input ts)
        trit (gf3-trit (hash input))]
    `(~'remote-input ~id ~user-id ~input
      (~'props
       :trit ~trit
       :timestamp ~ts
       :session ~session-id))))

;; Conflict resolution marker
(defn format-conflict [event-a event-b resolution]
  `(~'conflict-resolution
    :type :concurrent-input
    :events [~event-a ~event-b]
    :resolution ~resolution
    :strategy :gf3-ordering))

;; Session header
(defn session-header []
  `(~'crdt-terminal-session
    (~'version "0.1.0")
    (~'session-id ~session-id)
    (~'site-id ~site-id)
    (~'start-time ~(str (java.time.Instant/ofEpochMilli start-time)))
    (~'gf3-assignment ~(gf3-trit site-id))))

;; PTY wrapper using script command
(defn start-pty-capture [cmd output-file]
  (let [script-cmd (if (= (System/getProperty "os.name") "Mac OS X")
                     ["script" "-q" output-file cmd]
                     ["script" "-q" "-c" cmd output-file])]
    (p/process script-cmd
               {:inherit true
                :shutdown p/destroy-tree})))

;; Process output chunk into CRDT sexp
(defn process-output-chunk [chunk seq-num]
  (when (and chunk (> (count chunk) 0))
    (let [lines (str/split-lines chunk)]
      (mapv (fn [line]
              (format-remote-insert line :terminal-output))
            lines))))

;; Watch file for changes and emit sexps
(defn watch-and-emit [filepath sexp-output-file]
  (let [last-size (atom 0)
        seq-num (atom 0)]
    (println ";; CRDT Terminal Session Started")
    (prn (session-header))
    (println)
    
    ;; Append to output file
    (spit sexp-output-file (str (prn-str (session-header)) "\n") :append true)
    
    (loop []
      (Thread/sleep 50)
      (when (.exists (io/file filepath))
        (let [current-size (.length (io/file filepath))]
          (when (> current-size @last-size)
            (with-open [raf (java.io.RandomAccessFile. filepath "r")]
              (.seek raf @last-size)
              (let [new-bytes (byte-array (- current-size @last-size))]
                (.readFully raf new-bytes)
                (let [chunk (String. new-bytes "UTF-8")
                      sexps (process-output-chunk chunk (swap! seq-num inc))]
                  (doseq [sexp sexps]
                    (prn sexp)
                    (spit sexp-output-file (str (prn-str sexp) "\n") :append true)))))
            (reset! last-size current-size))))
      (recur))))

;; Replay session from sexp file
(defn replay-session [sexp-file speed-factor]
  (println ";; Replaying CRDT terminal session from" sexp-file)
  (let [lines (str/split-lines (slurp sexp-file))
        sexps (keep #(try (edn/read-string %) (catch Exception _ nil)) lines)
        start-ts (atom nil)]
    (doseq [sexp sexps]
      (when (= (first sexp) 'remote-insert)
        (let [[_ id site content props] sexp
              ts (some-> props 
                         (drop-while #(not= % :timestamp))
                         second)]
          (when ts
            (when-not @start-ts (reset! start-ts ts))
            (let [delay-ms (/ (- ts @start-ts) speed-factor)]
              (Thread/sleep (max 0 (min delay-ms 1000)))))
          ;; Emit to stdout for terminal
          (println content))))))

;; GF(3) trifurcated input handler
(defn trifurcate-input [input-queue our-trit]
  "Filter input queue to only process inputs matching our GF(3) trit"
  (filter (fn [input-sexp]
            (let [[_ _ _ _ props] input-sexp
                  input-trit (some-> props
                                     (drop-while #(not= % :trit))
                                     second)]
              (= input-trit our-trit)))
          input-queue))

;; Merge multiple session logs with conflict resolution
(defn merge-sessions [session-files output-file]
  (println ";; Merging" (count session-files) "CRDT terminal sessions")
  (let [all-sexps (mapcat (fn [f]
                            (let [lines (str/split-lines (slurp f))]
                              (keep #(try (edn/read-string %) 
                                          (catch Exception _ nil)) 
                                    lines)))
                          session-files)
        ;; Sort by timestamp
        sorted (sort-by (fn [sexp]
                          (if (= (first sexp) 'crdt-terminal-session)
                            0
                            (or (some-> sexp
                                        (drop-while #(not= % :timestamp))
                                        second)
                                Long/MAX_VALUE)))
                        all-sexps)
        ;; GF(3) balance check
        trits (keep (fn [sexp]
                      (some-> sexp
                              (drop-while #(not= % :trit))
                              second))
                    sorted)
        balance (frequencies trits)]
    
    (println ";; GF(3) balance:" balance)
    (spit output-file "")
    (doseq [sexp sorted]
      (spit output-file (str (prn-str sexp) "\n") :append true))
    (println ";; Merged" (count sorted) "events to" output-file)))

;; Main
(defn -main [& args]
  (let [cmd (first args)]
    (case cmd
      "record"
      (let [shell (or (System/getenv "SHELL") "/bin/bash")
            tmp-file (str "/tmp/crdt-term-" session-id ".raw")
            sexp-file (or (second args) 
                          (str "crdt-term-" session-id ".sexp"))]
        (println ";; Recording terminal to" sexp-file)
        (println ";; Session ID:" session-id)
        (println ";; GF(3) trit:" (gf3-trit site-id))
        (println ";; Starting shell:" shell)
        (println ";; Exit shell to stop recording")
        (println)
        (future (watch-and-emit tmp-file sexp-file))
        (let [proc (start-pty-capture shell tmp-file)]
          @proc)
        (println "\n;; Session ended"))
      
      "replay"
      (let [sexp-file (second args)
            speed (Double/parseDouble (or (nth args 2 nil) "1.0"))]
        (if sexp-file
          (replay-session sexp-file speed)
          (println "Usage: vterm_crdt_recorder.bb replay <sexp-file> [speed]")))
      
      "merge"
      (let [output-file (second args)
            input-files (drop 2 args)]
        (if (and output-file (seq input-files))
          (merge-sessions input-files output-file)
          (println "Usage: vterm_crdt_recorder.bb merge <output> <input1> <input2> ...")))
      
      ;; Default: show usage
      (do
        (println "vterm_crdt_recorder.bb - CRDT terminal session recorder")
        (println)
        (println "Commands:")
        (println "  record [output.sexp]  - Record terminal session")
        (println "  replay <file> [speed] - Replay session (speed: 1.0 = realtime)")
        (println "  merge <out> <in1> ... - Merge multiple sessions")
        (println)
        (println "Output format: CRDT-style sexps compatible with crdt.el")
        (println "Uses GF(3) coloring for trifurcated conflict resolution")))))

(apply -main *command-line-args*)
