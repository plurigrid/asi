#!/usr/bin/env bb
;; parallel_walk.bb
;; Applies colors to three routed fibers.
;; policy=gf3_balanced ensures per-index GF(3) conservation across the three fibers.

(ns parallel-walk
  (:require [clojure.string :as str]
            [cheshire.core :as json]))

(def label-map {0 "None" 1 "Green" 2 "Blue"})

(defn sha256-int [^String s]
  (let [md (java.security.MessageDigest/getInstance "SHA-256")]
    (.update md (.getBytes s "UTF-8"))
    (let [b (.digest md)
          bb (java.nio.ByteBuffer/wrap b)
          x (.getLong bb)]
      (Math/abs x))))

(defn trit [s] (mod (sha256-int s) 3))

(defn gf3-balanced-triplet [seed p0 p1 p2]
  ;; choose t0,t1 deterministically; set t2 to conserve
  (let [t0 (trit (str seed "::0::" p0))
        t1 (trit (str seed "::1::" p1))
        t2 (mod (- 0 t0 t1) 3)]
    [t0 t1 t2]))

(defn raw-color [seed j p]
  (trit (str seed "::raw::" j "::" p)))

(defn -main [& args]
  (let [m (apply hash-map args)
        fibers-file (or (get m "--fibers") "fibers.json")
        seed (or (get m "--seed") "seed0")
        policy (or (get m "--policy") "raw")
        dry? (= "true" (get m "--dry-run" "true"))
        data (json/parse-string (slurp fibers-file) true)
        fibers (mapv (comp vec sort) (:fibers data))
        n (apply min (map count fibers))]
    (when (and (= policy "gf3_balanced")
               (not= (map count fibers) (repeat 3 n)))
      (println "warning: unequal fiber lengths; gf3_balanced will apply to first n positions only."))
    (doseq [i (range n)]
      (let [p0 (get-in fibers [0 i])
            p1 (get-in fibers [1 i])
            p2 (get-in fibers [2 i])
            [t0 t1 t2] (if (= policy "gf3_balanced")
                         (gf3-balanced-triplet seed p0 p1 p2)
                         [(raw-color seed 0 p0) (raw-color seed 1 p1) (raw-color seed 2 p2)])]
        (println (format "i=%d\t%s\t%d\t%s" i p0 t0 (label-map t0)))
        (println (format "i=%d\t%s\t%d\t%s" i p1 t1 (label-map t1)))
        (println (format "i=%d\t%s\t%d\t%s" i p2 t2 (label-map t2)))
        ;; macOS application hook omitted (dry-run default)
        ))
    (shutdown-agents)))

(apply -main *command-line-args*)
