#!/usr/bin/env bb
;; Geodesic tracker for localsend transfer causality
;; Gay.jl color seed 1069 for causal chain coloring

(require '[clojure.edn :as edn]
         '[clojure.java.io :as io])

(def verified-path "/tmp/localsend_verified.edn")
(def output-path "/tmp/geodesic_paths.edn")

;; SplitMix64 Gay.jl coloring (seed 1069)
(defn splitmix64 [seed]
  (let [z (unchecked-add seed 0x9e3779b97f4a7c15)]
    (-> z (bit-xor (unsigned-bit-shift-right z 30))
        (unchecked-multiply 0xbf58476d1ce4e5b9)
        (#(bit-xor % (unsigned-bit-shift-right % 27)))
        (unchecked-multiply 0x94d049bb133111eb)
        (#(bit-xor % (unsigned-bit-shift-right % 31))))))

(defn gay-color [chain-id]
  (let [h (mod (splitmix64 (+ 1069 chain-id)) 360)]
    (format "hsl(%d,70%%,50%%)" h)))

(defn load-verified []
  (if (.exists (io/file verified-path))
    (edn/read-string (slurp verified-path))
    []))

(defn build-dag [files]
  (reduce (fn [dag {:keys [hash parent-hash] :as node}]
            (-> dag
                (assoc-in [:nodes hash] node)
                (update :edges conj [parent-hash hash])))
          {:nodes {} :edges #{}} files))

(defn detect-conflicts [files]
  (->> files
       (group-by :path)
       (filter #(> (count (val %)) 1))
       (map (fn [[path vs]] {:path path :hashes (mapv :hash vs)}))))

(defn deconflict! [files]
  (let [conflicts (detect-conflicts files)]
    (reduce (fn [acc {:keys [path hashes]}]
              (map #(if (some #{(:hash %)} (rest hashes))
                      (update % :path str "-" (subs (:hash %) 0 8))
                      %) acc))
            files conflicts)))

(defn find-roots [dag]
  (let [children (set (map second (:edges dag)))]
    (remove children (keys (:nodes dag)))))

(defn geodesic-paths [dag]
  (let [adj (reduce (fn [m [p c]] (update m p (fnil conj #{}) c))
                    {} (:edges dag))]
    (letfn [(walk [node path visited]
              (if-let [children (seq (remove visited (get adj node)))]
                (mapcat #(walk % (conj path %) (conj visited %)) children)
                [path]))]
      (->> (find-roots dag)
           (map-indexed (fn [i root]
                          {:chain-id i
                           :color (gay-color i)
                           :paths (walk root [root] #{root})}))))))

(defn -main []
  (let [files (deconflict! (load-verified))
        dag (build-dag files)
        conflicts (detect-conflicts (load-verified))
        paths (geodesic-paths dag)
        result {:timestamp (System/currentTimeMillis)
                :conflicts conflicts
                :chains paths
                :summary {:total-files (count files)
                          :chain-count (count paths)
                          :conflict-count (count conflicts)}}]
    (spit output-path (pr-str result))
    (println "=== Geodesic Tracker Summary ===")
    (println (format "Files: %d | Chains: %d | Conflicts: %d"
                     (count files) (count paths) (count conflicts)))
    (doseq [{:keys [chain-id color paths]} paths]
      (println (format "  Chain %d [%s]: %d paths" chain-id color (count paths))))
    result))

(when (= *file* (System/getProperty "babashka.file")) (-main))
