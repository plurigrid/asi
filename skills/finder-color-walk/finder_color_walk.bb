#!/usr/bin/env bb
;; finder_color_walk.bb
;; Single-stream deterministic walk; policy=raw (SPI holds, GF(3) not guaranteed)

(ns finder-color-walk
  (:require [clojure.java.io :as io]
            [clojure.string :as str]))

(def label-map {0 "None" 1 "Green" 2 "Blue"})

(defn sha256-int [^String s]
  (let [md (java.security.MessageDigest/getInstance "SHA-256")]
    (.update md (.getBytes s "UTF-8"))
    (let [b (.digest md)
          bb (java.nio.ByteBuffer/wrap b)
          x (.getLong bb)]
      (Math/abs x))))

(defn color-at [path seed]
  (mod (sha256-int (str seed "::" path)) 3))

(defn list-files [root]
  (->> (file-seq (io/file root))
       (filter #(.isFile ^java.io.File %))
       (map #(.getPath ^java.io.File %))
       (sort)))

(defn -main [& args]
  (let [m (apply hash-map args)
        root (or (get m "--root") ".")
        seed (or (get m "--seed") "seed0")
        dry? (= "true" (get m "--dry-run" "true"))
        paths (list-files root)]
    (doseq [p paths]
      (let [t (color-at p seed)]
        (println (format "%s\t%d\t%s" p t (label-map t)))
        ;; macOS application (optional): left as hook
        ;; (when-not dry? (shell "xattr" ...))
        )))
  (shutdown-agents))

(apply -main *command-line-args*)
