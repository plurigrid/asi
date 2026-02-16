#!/usr/bin/env bb
;; book-to-skill.bb - Transform books into GF(3)-colored skills
;; Generates skill artifacts from book structure with unworlded chapter ordering

(require '[babashka.http-client :as http])
(require '[cheshire.core :as json])
(require '[clojure.string :as str])

(def golden-ratio 0x9E3779B97F4A7C15)

(defn splitmix64 [seed]
  (let [z (bit-and (+ seed golden-ratio) 0xFFFFFFFFFFFFFFFF)
        z (bit-and (* (bit-xor z (bit-shift-right z 30)) 0xBF58476D1CE4E5B9) 0xFFFFFFFFFFFFFFFF)
        z (bit-and (* (bit-xor z (bit-shift-right z 27)) 0x94D049BB133111EB) 0xFFFFFFFFFFFFFFFF)]
    (bit-xor z (bit-shift-right z 31))))

(defn hash-to-trit [h]
  (- (mod h 3) 1))

(defn chapter-to-color [seed chapter-num]
  (let [h (splitmix64 (+ seed chapter-num))
        hue (mod h 360)
        trit (cond
               (or (< hue 60) (>= hue 300)) 1   ; warm +1
               (< hue 180) 0                     ; neutral 0
               :else -1)]                        ; cold -1
    {:chapter chapter-num
     :hue hue
     :trit trit
     :hex (format "#%06X" (mod h 0xFFFFFF))}))

;; Data Science at the Command Line - OSEMN model chapters
(def dsatcl-chapters
  [{:num 1  :title "Introduction"                    :phase :meta}
   {:num 2  :title "Getting Started"                 :phase :obtain}
   {:num 3  :title "Obtaining Data"                  :phase :obtain}
   {:num 4  :title "Creating Command-line Tools"     :phase :scrub}
   {:num 5  :title "Scrubbing Data"                  :phase :scrub}
   {:num 6  :title "Project Management with Make"    :phase :explore}
   {:num 7  :title "Exploring Data"                  :phase :explore}
   {:num 8  :title "Parallel Pipelines"              :phase :model}
   {:num 9  :title "Modeling Data"                   :phase :model}
   {:num 10 :title "Polyglot Data Science"           :phase :interpret}])

;; OSEMN phase to trit mapping
(def phase-trits
  {:meta      0   ; Coordination
   :obtain    1   ; Generation (+1)
   :scrub     0   ; Transformation (0)
   :explore  -1   ; Validation (-1)
   :model     1   ; Generation (+1)
   :interpret 0}) ; Coordination (0)

;; Unworld: Derive chapter ordering by trit, not sequence
(defn unworld-chapters [chapters seed]
  (let [colored (map #(merge % (chapter-to-color seed (:num %))
                              {:phase-trit (get phase-trits (:phase %))})
                     chapters)]
    ;; Group by trit for parallel derivation
    {:generators  (filter #(= 1 (:phase-trit %)) colored)
     :coordinators (filter #(= 0 (:phase-trit %)) colored)
     :validators   (filter #(= -1 (:phase-trit %)) colored)
     :gf3-sum      (reduce + (map :phase-trit colored))}))

;; Generate skill from book
(defn book-to-skill [{:keys [title author chapters seed]}]
  (let [unworlded (unworld-chapters chapters seed)
        skill-name (-> title
                       str/lower-case
                       (str/replace #"\s+" "-")
                       (str/replace #"[^a-z0-9-]" ""))]
    {:skill-name skill-name
     :color (format "#%06X" (mod (splitmix64 seed) 0xFFFFFF))
     :trit (hash-to-trit (splitmix64 seed))
     :author author
     :unworlded unworlded
     :derivation-order
     ;; Parallel derivation: all triads can execute simultaneously
     {:parallel-triads
      (partition 3 (interleave
                    (:generators unworlded)
                    (:coordinators unworlded)
                    (:validators unworlded)))}}))

;; Main
(defn -main [& args]
  (let [seed (if (seq args) (parse-long (first args)) 69)
        result (book-to-skill
                {:title "Data Science at the Command Line"
                 :author "Jeroen Janssens"
                 :chapters dsatcl-chapters
                 :seed seed})]
    (println (json/generate-string result {:pretty true}))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
