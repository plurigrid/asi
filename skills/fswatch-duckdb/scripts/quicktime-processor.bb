#!/usr/bin/env bb
;; QuickTime Auto-Processor with Skill Interleaving and DuckLake Integration
;; Watches for new recordings and processes with GF(3) triadic coloring

(require '[babashka.process :refer [shell process]]
         '[babashka.fs :as fs]
         '[clojure.string :as str]
         '[cheshire.core :as json])

;; === Configuration ===
(def db-path (str (System/getenv "HOME") "/.agents/fswatch.duckdb"))
(def ducklake-path "/tmp/ducklake")
(def watch-paths [(str (System/getenv "HOME") "/Desktop")
                  (str (System/getenv "HOME") "/Movies")
                  "/tmp"])
(def session-id (or (System/getenv "AMP_THREAD_ID") (str "qt-" (subs (str (random-uuid)) 0 8))))

;; === SplitMix64 for Color Generation ===
(def GOLDEN (unchecked-long -7046029254386353131))

(defn splitmix64 [state]
  (let [mix1 (unchecked-long -4658895280553007687)
        mix2 (unchecked-long -7723592293110705685)
        s (unchecked-add state GOLDEN)
        z1 (unchecked-multiply (bit-xor s (unsigned-bit-shift-right s 30)) mix1)
        z2 (unchecked-multiply (bit-xor z1 (unsigned-bit-shift-right z1 27)) mix2)]
    [(bit-xor z2 (unsigned-bit-shift-right z2 31)) s]))

(defn interaction-entropy [text]
  "Compute Shannon entropy of interaction text as seed"
  (let [chars (seq text)
        freqs (frequencies chars)
        total (count chars)
        h (- (reduce + (map (fn [[_ c]]
                              (let [p (/ (double c) total)]
                                (if (pos? p) (* p (Math/log p)) 0.0)))
                            freqs)))]
    (bit-and (long (* h 1000000 (hash text))) 0x7FFFFFFFFFFFFFFF)))

(defn hue-to-trit [h]
  (cond (or (< h 60) (>= h 300)) 1   ; PLUS (warm)
        (< h 180) 0                   ; ERGODIC (neutral)
        :else -1))                    ; MINUS (cold)

(defn gen-color [seed idx]
  (let [[r1 s1] (splitmix64 (unchecked-add seed idx))
        [r2 s2] (splitmix64 s1)
        [r3 _] (splitmix64 s2)
        H (* (Math/abs (/ (double r3) (double Long/MAX_VALUE))) 360.0)
        L (* (Math/abs (/ (double r1) (double Long/MAX_VALUE))) 100.0)
        C (* (Math/abs (/ (double r2) (double Long/MAX_VALUE))) 100.0)]
    {:L L :C C :H H :trit (hue-to-trit H) :seed seed :idx idx}))

;; === Voice Announcements ===
(def voices {:minus "Anna (German (Germany))"    ; Emmy Noether
             :ergodic "Amélie (French (Canada))" ; Sophie Germain
             :plus "Ava (Premium)"})             ; Generator

(defn announce [trit message]
  (let [voice (case trit
                -1 (:minus voices)
                0 (:ergodic voices)
                1 (:plus voices)
                "Samantha (Enhanced)")]
    (shell {:continue true} "say" "-v" voice message)))

;; === DuckLake Integration ===
(defn init-ducklake! []
  (fs/create-dirs ducklake-path)
  (fs/create-dirs (str ducklake-path "/recordings"))
  (fs/create-dirs (str ducklake-path "/frames"))
  (fs/create-dirs (str ducklake-path "/audio"))
  (shell {:continue true} "duckdb" db-path
         "CREATE TABLE IF NOT EXISTS recording_processing (
            id INTEGER PRIMARY KEY DEFAULT nextval('fs_events_seq'),
            input_path VARCHAR NOT NULL,
            recording_type VARCHAR,
            duration_seconds FLOAT,
            has_audio BOOLEAN,
            has_video BOOLEAN,
            frame_count INTEGER,
            interaction_entropy BIGINT,
            color_seed BIGINT,
            trit INTEGER,
            processed_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
            session_id VARCHAR,
            ducklake_path VARCHAR
          );
          CREATE TABLE IF NOT EXISTS skill_interleave (
            id INTEGER PRIMARY KEY DEFAULT nextval('fs_events_seq'),
            triplet_id INTEGER,
            stream_id INTEGER,
            trit INTEGER,
            skill_name VARCHAR,
            input_path VARCHAR,
            output_path VARCHAR,
            duration_ms BIGINT,
            created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
          );"))

;; === Video Processing ===
(defn get-media-info [path]
  (try
    (let [result (shell {:out :string :continue true}
                        "ffprobe" "-v" "quiet" "-print_format" "json"
                        "-show_format" "-show_streams" path)]
      (when (= 0 (:exit result))
        (json/parse-string (:out result) true)))
    (catch Exception _ nil)))

(defn has-audio? [info]
  (some #(= "audio" (:codec_type %)) (:streams info)))

(defn has-video? [info]
  (some #(= "video" (:codec_type %)) (:streams info)))

(defn extract-frames [input-path output-dir interval]
  (let [basename (fs/strip-ext (fs/file-name input-path))]
    (shell {:continue true}
           "ffmpeg" "-y" "-i" input-path
           "-vf" (str "fps=1/" interval)
           (str output-dir "/" basename "_frame_%04d.jpg"))))

(defn extract-audio [input-path output-path]
  (shell {:continue true}
         "ffmpeg" "-y" "-i" input-path
         "-vn" "-c:a" "libmp3lame" "-q:a" "2"
         output-path))

(defn generate-thumbnail [input-path output-path]
  (shell {:continue true}
         "ffmpeg" "-y" "-i" input-path
         "-ss" "00:00:05" "-vframes" "1" "-vf" "scale=320:-1"
         output-path))

;; === Skill Interleaving ===
(defn interleave-process! [path info]
  "Process recording with triadic skill interleaving"
  (let [entropy (interaction-entropy path)
        color (gen-color entropy 0)
        trit (:trit color)
        basename (fs/strip-ext (fs/file-name path))
        frame-dir (str ducklake-path "/frames/" basename)
        audio-dir (str ducklake-path "/audio")
        thumb-path (str ducklake-path "/recordings/" basename "_thumb.jpg")]
    
    (fs/create-dirs frame-dir)
    
    ;; Announce with appropriate voice
    (announce trit (str "Processing " (fs/file-name path)))
    
    ;; TRIADIC PARALLEL PROCESSING
    (let [start-time (System/currentTimeMillis)
          
          ;; MINUS (-1): Frame extraction (validation/decomposition)
          minus-future (future
                         (announce -1 "Extracting frames")
                         (when (has-video? info)
                           (extract-frames path frame-dir 30))
                         {:stream :minus :trit -1 :action :frames})
          
          ;; ERGODIC (0): Thumbnail generation (coordination)
          ergodic-future (future
                           (announce 0 "Generating thumbnail")
                           (when (has-video? info)
                             (generate-thumbnail path thumb-path))
                           {:stream :ergodic :trit 0 :action :thumbnail})
          
          ;; PLUS (+1): Audio extraction (generation)
          plus-future (future
                        (announce 1 "Extracting audio")
                        (when (has-audio? info)
                          (extract-audio path (str audio-dir "/" basename ".mp3")))
                        {:stream :plus :trit 1 :action :audio})
          
          ;; Wait for all
          results [@minus-future @ergodic-future @plus-future]
          duration-ms (- (System/currentTimeMillis) start-time)
          frame-count (count (fs/glob frame-dir "*.jpg"))
          
          ;; GF(3) verification
          trit-sum (reduce + (map :trit results))]
      
      ;; Verify GF(3) conservation
      (when (zero? (mod trit-sum 3))
        (announce 0 "GF 3 conserved"))
      
      ;; Record to DuckDB
      (shell {:continue true} "duckdb" db-path
             (format "INSERT INTO recording_processing 
                      (input_path, recording_type, duration_seconds, has_audio, has_video, 
                       frame_count, interaction_entropy, color_seed, trit, session_id, ducklake_path)
                      VALUES ('%s', '%s', %s, %s, %s, %d, %d, %d, %d, '%s', '%s')"
                     (str/replace path "'" "''")
                     (if (has-video? info) "screen_recording" "audio_only")
                     (get-in info [:format :duration] "0")
                     (has-audio? info)
                     (has-video? info)
                     frame-count
                     entropy
                     (:seed color)
                     trit
                     session-id
                     ducklake-path))
      
      ;; Record skill interleaving
      (doseq [[idx result] (map-indexed vector results)]
        (shell {:continue true} "duckdb" db-path
               (format "INSERT INTO skill_interleave 
                        (triplet_id, stream_id, trit, skill_name, input_path, duration_ms)
                        VALUES (0, %d, %d, '%s', '%s', %d)"
                       idx (:trit result) (name (:action result)) path duration-ms)))
      
      {:path path
       :trit trit
       :entropy entropy
       :frame-count frame-count
       :duration-ms duration-ms
       :gf3-sum trit-sum})))

;; === QuickTime Recording Detection ===
(def quicktime-extensions #{"mov" "m4v" "mp4"})
(def processed (atom #{}))

(defn quicktime-recording? [path]
  (and (contains? quicktime-extensions (some-> path fs/extension str/lower-case))
       (or (str/includes? path "Screen Recording")
           (str/includes? path "QuickTime")
           (str/includes? path "Recording"))))

(defn watch-and-process []
  (println "╔══════════════════════════════════════════════════════════════╗")
  (println "║  QUICKTIME AUTO-PROCESSOR with SKILL INTERLEAVING           ║")
  (println "╚══════════════════════════════════════════════════════════════╝")
  (println)
  (println "Watching:" (str/join ", " watch-paths))
  (println "DuckLake:" ducklake-path)
  (println "Session:" session-id)
  (println)
  
  (init-ducklake!)
  (announce 0 "QuickTime processor ready")
  
  (loop []
    (doseq [watch-path watch-paths]
      (when (fs/exists? watch-path)
        (doseq [path (fs/glob watch-path "**/*.{mov,m4v,mp4}")]
          (let [path-str (str path)]
            (when (and (not (contains? @processed path-str))
                       (fs/regular-file? path)
                       (> (fs/size path) 1000)) ; Skip tiny files
              ;; Wait for file to finish writing
              (let [size1 (fs/size path)]
                (Thread/sleep 2000)
                (when (= size1 (fs/size path))
                  (swap! processed conj path-str)
                  (println "Processing:" path-str)
                  (when-let [info (get-media-info path-str)]
                    (let [result (interleave-process! path-str info)]
                      (println "  Entropy:" (:entropy result))
                      (println "  Trit:" (:trit result))
                      (println "  Frames:" (:frame-count result))
                      (println "  Duration:" (:duration-ms result) "ms")
                      (println "  GF(3):" (:gf3-sum result)))))))))))
    (Thread/sleep 5000)
    (recur)))

;; === Main ===
(defn -main [& args]
  (if (seq args)
    ;; Process single file
    (let [path (first args)]
      (if (fs/exists? path)
        (when-let [info (get-media-info path)]
          (init-ducklake!)
          (let [result (interleave-process! path info)]
            (println (json/generate-string result {:pretty true}))))
        (println "File not found:" path)))
    ;; Watch mode
    (watch-and-process)))

(apply -main *command-line-args*)
