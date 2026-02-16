#!/usr/bin/env bb
;; Video Auto-Processor - triggered by FileSystemWatcher
;; Processes videos: extract metadata, generate thumbnails, transcode

(require '[babashka.process :refer [shell]]
         '[babashka.fs :as fs]
         '[clojure.string :as str]
         '[cheshire.core :as json])

(def db-path (str (System/getenv "HOME") "/.agents/fswatch.duckdb"))
(def output-dir (or (System/getenv "VIDEO_OUTPUT_DIR") "/tmp/processed_videos"))
(def video-extensions #{"mp4" "mov" "mkv" "webm" "avi" "m4v" "flv" "wmv" "mpg" "mpeg"})

;; Ensure output directory exists
(fs/create-dirs output-dir)

;; Check if file is a video
(defn video-file? [path]
  (let [ext (some-> path fs/extension str/lower-case)]
    (contains? video-extensions ext)))

;; Extract video metadata with ffprobe
(defn extract-metadata [path]
  (try
    (let [result (shell {:out :string :continue true}
                        "ffprobe" "-v" "quiet" 
                        "-print_format" "json"
                        "-show_format" "-show_streams"
                        path)]
      (when (= 0 (:exit result))
        (json/parse-string (:out result) true)))
    (catch Exception e
      (println "Metadata extraction failed:" (.getMessage e))
      nil)))

;; Generate thumbnail at 5 second mark
(defn generate-thumbnail [input-path output-path]
  (shell {:continue true}
         "ffmpeg" "-y" "-i" input-path
         "-ss" "00:00:05" "-vframes" "1"
         "-vf" "scale=320:-1"
         output-path))

;; Transcode to web-friendly H.264/AAC
(defn transcode-web [input-path output-path]
  (shell {:continue true}
         "ffmpeg" "-y" "-i" input-path
         "-c:v" "libx264" "-preset" "fast" "-crf" "23"
         "-c:a" "aac" "-b:a" "128k"
         "-movflags" "+faststart"
         output-path))

;; Extract audio track
(defn extract-audio [input-path output-path]
  (shell {:continue true}
         "ffmpeg" "-y" "-i" input-path
         "-vn" "-c:a" "libmp3lame" "-q:a" "2"
         output-path))

;; Record processing to DuckDB
(defn record-processing! [input-path metadata output-files]
  (let [duration (get-in metadata [:format :duration] "0")
        size (get-in metadata [:format :size] "0")
        codec (get-in metadata [:streams 0 :codec_name] "unknown")
        sql (format "INSERT INTO fs_events (path, event_type, size, checksum, session_id)
                     VALUES ('%s', 'video_processed', %s, '%s', '%s')"
                    (str/replace input-path "'" "''")
                    size
                    (str "duration:" duration "|codec:" codec)
                    (or (System/getenv "AMP_THREAD_ID") "video-processor"))]
    (shell {:continue true} "duckdb" db-path sql)))

;; Announce with say
(defn announce [message]
  (shell {:continue true} "say" "-v" "Samantha (Enhanced)" message))

;; Process a single video file
(defn process-video! [path]
  (announce (str "Processing video " (fs/file-name path)))
  (println "Processing:" path)
  
  (let [basename (fs/strip-ext (fs/file-name path))
        metadata (extract-metadata path)
        thumb-path (str output-dir "/" basename "_thumb.jpg")
        web-path (str output-dir "/" basename "_web.mp4")
        audio-path (str output-dir "/" basename "_audio.mp3")]
    
    (when metadata
      (println "  Duration:" (get-in metadata [:format :duration]) "seconds")
      (println "  Size:" (get-in metadata [:format :size]) "bytes")
      
      ;; Generate thumbnail
      (print "  Generating thumbnail... ")
      (flush)
      (generate-thumbnail path thumb-path)
      (println "done")
      
      ;; Transcode for web (if not already h264)
      (let [codec (get-in metadata [:streams 0 :codec_name])]
        (when (not= codec "h264")
          (print "  Transcoding to H.264... ")
          (flush)
          (transcode-web path web-path)
          (println "done")))
      
      ;; Extract audio
      (print "  Extracting audio... ")
      (flush)
      (extract-audio path audio-path)
      (println "done")
      
      ;; Record to database
      (record-processing! path metadata {:thumb thumb-path :audio audio-path})
      
      (announce "Video processing complete")
      (println "  Outputs in:" output-dir))))

;; Watch for new videos and process
(defn watch-and-process [watch-path]
  (println "Watching for videos in:" watch-path)
  (let [processed (atom #{})]
    (loop []
      (doseq [path (fs/glob watch-path "**")]
        (let [path-str (str path)]
          (when (and (video-file? path-str)
                     (not (contains? @processed path-str))
                     (fs/regular-file? path))
            ;; Wait for file to finish writing
            (Thread/sleep 2000)
            (let [size1 (fs/size path)]
              (Thread/sleep 1000)
              (when (= size1 (fs/size path))
                (swap! processed conj path-str)
                (process-video! path-str))))))
      (Thread/sleep 3000)
      (recur))))

;; Main: process single file or watch directory
(defn -main [& args]
  (let [target (or (first args) "/tmp")]
    (if (and (fs/exists? target) (fs/regular-file? target))
      (process-video! target)
      (watch-and-process target))))

(apply -main *command-line-args*)
