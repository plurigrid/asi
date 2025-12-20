#!/usr/bin/env bb
"Filesystem Tree Snapshot Tool

Usage:
  bb topos_snapshot.bb [directory] [--colors] [--sizes]

Generates deterministic, color-coded snapshots of directory structures."

(require '[babashka.fs :as fs]
         '[clojure.string :as str]
         '[clojure.java.io :as io])

(import java.io.File
        java.security.MessageDigest)

;; SPI Constants from .topos
(def ^:const GAY-SEED 0x285508656870f24a)
(def ^:const ERGODIC-TWIST 0x5f5f5f5f5f5f5f5f)

;; Simple Hash
(defn simple-hash [s]
  (reduce (fn [h c] (+ (* h 31) (int c)))
          0
          (str s)))

;; HSL to Hex
(defn hsl->hex [h s l]
  (let [c (* (- 1 (Math/abs (- (* 2 l) 1))) s)
        x (* c (- 1 (Math/abs (mod (/ h 60) 2))))
        m (- l (/ c 2))
        [r g b] (cond (< h 60) [c x 0] (< h 120) [x c 0] (< h 180) [0 c x]
                      (< h 240) [0 x c] (< h 300) [x 0 c] :else [c 0 x])
        to-int #(int (+ (* (+ % m) 255)))]
    (format "#%02X%02X%02X" (to-int r) (to-int g) (to-int b))))

;; SPI Color (Simplified)
(defn spi-color [path]
  (let [hash-val (Math/abs (simple-hash path))
        hue (mod hash-val 360)
        saturation (+ 0.5 (/ (mod hash-val 256) 512))
        lightness (+ 0.4 (/ (mod (quot hash-val 256) 256) 1024))]
    (hsl->hex (double hue) (double saturation) (double lightness))))

;; File Info
(defn file-entry [path include-colors]
  (let [file (io/file path)
        is-dir (.isDirectory file)
        info {:name (.getName file)
              :type (if is-dir "dir" "file")
              :children []}]
    (cond-> info
      (not is-dir) (assoc :size (int (/ (.length file) 1024)))
      include-colors (assoc :color (spi-color path)))))

;; Recursive Tree Builder
(defn build-tree [path depth max-depth include-colors]
  (if (>= depth max-depth)
    [(file-entry path include-colors)]
    (try
      (let [file (io/file path)
            is-dir (.isDirectory file)
            base-entry (file-entry path include-colors)]
        (if (not is-dir)
          [base-entry]
          (let [children (try (vec (fs/list-dir path)) (catch Exception _ []))
                sorted (sort-by #(.getName (io/file %)) children)]
            [(assoc base-entry
                    :children (mapcat #(build-tree (.getAbsolutePath (io/file %))
                                                    (inc depth)
                                                    max-depth
                                                    include-colors)
                                      sorted))])))
      (catch Exception e
        [(file-entry path include-colors)]))))

;; Pretty Print
(defn print-tree [entry depth]
  (let [indent (apply str (repeat depth "  "))
        icon (if (= (:type entry) "dir") "📁" "📄")
        color-str (if (:color entry) (str " " (:color entry)) "")
        size-str (if (:size entry) (format " (%dK)" (:size entry)) "")]
    (println (str indent icon " " (:name entry) size-str color-str))
    (doseq [child (:children entry)]
      (print-tree child (inc depth)))))

;; Snapshot Generator
(defn generate-snapshot [directory include-colors include-sizes max-depth]
  (println (str "📸 Snapshot of " directory))
  (let [trees (build-tree directory 0 max-depth include-colors)]
    (doseq [tree trees]
      (print-tree tree 0)))
  (println "✓ Done"))

;; CLI
(let [args *command-line-args*
      directory (or (first args) ".")
      include-colors (some #(= % "--colors") args)
      include-sizes (some #(= % "--sizes") args)
      max-depth (if include-colors 4 2)]
  (generate-snapshot directory include-colors include-sizes max-depth))
