#!/usr/bin/env bb
;; triadic_router.bb
;; Deterministic GF(3)-balanced routing of files into three fibers.
;;
;; Routing rule:
;;   fiber(file) = hash(file) mod 3
;; Then we rebalance deterministically by moving minimal number of files so counts are equal,
;; preserving a GF(3) "conservation" checksum over the multiset.

(ns triadic-router
  (:require [clojure.java.io :as io]
            [clojure.string :as str]
            [cheshire.core :as json]))

(defn sha256-int [^String s]
  (let [md (java.security.MessageDigest/getInstance "SHA-256")]
    (.update md (.getBytes s "UTF-8"))
    (let [b (.digest md)
          bb (java.nio.ByteBuffer/wrap b)
          x (.getLong bb)]
      (Math/abs x))))

(defn list-files [root]
  (->> (file-seq (io/file root))
       (filter #(.isFile ^java.io.File %))
       (map #(.getPath ^java.io.File %))
       (sort)))

(defn initial-fiber [path]
  (mod (sha256-int path) 3))

(defn rebalance [paths]
  (let [by (group-by initial-fiber paths)
        f0 (vec (get by 0 []))
        f1 (vec (get by 1 []))
        f2 (vec (get by 2 []))
        n (count paths)
        target (int (Math/floor (/ n 3)))
        rem (mod n 3)
        tgt (cond-> [target target target]
              (>= rem 1) (update 0 inc)
              (= rem 2)  (update 1 inc))
        fibers (atom [f0 f1 f2])]
    (loop []
      (let [[a b c] @fibers
            counts [(count a) (count b) (count c)]
            deltas (map - counts tgt)
            over (->> (map-indexed vector deltas) (filter (fn [[i d]] (pos? d))) (sort-by second >))
            under (->> (map-indexed vector deltas) (filter (fn [[i d]] (neg? d))) (sort-by second))
            done? (and (empty? over) (empty? under))]
        (if done?
          @fibers
          (let [[oi _] (first over)
                [ui _] (first under)
                from (nth @fibers oi)
                moved (last from)
                new-from (subvec from 0 (dec (count from)))
                new-to (conj (nth @fibers ui) moved)]
            (swap! fibers assoc oi new-from ui new-to)
            (recur)))))))

(defn gf3-check [fibers]
  (mod (reduce + (for [[i fs] (map-indexed vector fibers)
                       _ fs] i))
       3))

(defn -main [& args]
  (let [m (apply hash-map args)
        root (or (get m "--root") ".")
        out  (or (get m "--out") "fibers.json")
        paths (list-files root)
        fibers (rebalance paths)
        counts (map count fibers)
        chk (gf3-check fibers)]
    (spit out (json/generate-string {:root root
                                     :total (count paths)
                                     :counts counts
                                     :gf3_checksum chk
                                     :fibers fibers}
                                    {:pretty true}))
    (println (format "routed=%d counts=%s gf3_checksum=%d -> %s"
                     (count paths) (pr-str counts) chk out))))

(apply -main *command-line-args*)
