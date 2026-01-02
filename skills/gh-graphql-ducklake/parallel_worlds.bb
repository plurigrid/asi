#!/usr/bin/env bb
;; GF(3) Parallel Worlds GitHub GraphQL → DuckLake Snapshots
;; MINUS: bmorphism | ERGODIC: plurigrid | PLUS: AlgebraicJulia

(require '[babashka.process :as p]
         '[cheshire.core :as json]
         '[babashka.fs :as fs])

(def worlds
  [{:trit -1 :name "bmorphism"    :type :user :color "#3B82F6"}
   {:trit  0 :name "plurigrid"    :type :org  :color "#10B981"}
   {:trit +1 :name "AlgebraicJulia" :type :org :color "#F59E0B"}])

(defn graphql-query [world]
  (let [entity (if (= :user (:type world)) "user" "organization")]
    (format "{ %s(login:\"%s\") { repositories(first:50, orderBy:{field:STARGAZERS, direction:DESC}) { nodes { name stargazerCount description updatedAt } } } }"
            entity (:name world))))

(defn fetch-world [world]
  (println (format "[trit %+d] Fetching %s..." (:trit world) (:name world)))
  (let [result (-> (p/shell {:out :string :err :string}
                    "gh" "api" "graphql" "-f" (str "query=" (graphql-query world)))
                   :out
                   (json/parse-string true))]
    (assoc world
           :repos (or (-> result :data :user :repositories :nodes)
                      (-> result :data :organization :repositories :nodes))
           :snapshot_time (java.time.Instant/now))))

(defn snapshot-to-ducklake [worlds lake-path]
  (let [all-repos (for [w worlds
                        r (:repos w)]
                    (assoc r
                           :world (:name w)
                           :trit (:trit w)
                           :color (:color w)
                           :snapshot_time (str (:snapshot_time w))))
        json-file "/tmp/gh_parallel_worlds.json"]
    (spit json-file (json/generate-string all-repos))
    (p/shell {:out :inherit :err :inherit}
      "duckdb" "-c"
      (format "LOAD ducklake;
               ATTACH 'ducklake:%s' AS lake;
               CREATE TABLE IF NOT EXISTS lake.repos (
                 name VARCHAR, stargazerCount INTEGER, description VARCHAR,
                 updatedAt TIMESTAMP, world VARCHAR, trit INTEGER,
                 color VARCHAR, snapshot_time TIMESTAMP
               );
               INSERT INTO lake.repos
               SELECT * FROM read_json_auto('%s');"
              lake-path json-file))
    (println (format "Snapshot: %d repos across %d worlds"
                     (count all-repos) (count worlds)))))

(defn verify-gf3-conservation [worlds]
  (let [trit-sum (reduce + (map :trit worlds))]
    (assert (zero? (mod trit-sum 3))
            (format "GF(3) violation! Sum=%d" trit-sum))
    (println (format "GF(3) conservation verified: %s = 0 (mod 3)"
                     (clojure.string/join " + " (map #(format "%+d" (:trit %)) worlds))))))

(defn say-announcement [worlds]
  (let [total-repos (reduce + (map #(count (:repos %)) worlds))
        total-stars (reduce + (for [w worlds r (:repos w)] (:stargazerCount r)))]
    (p/shell "say" "-v" "Samantha"
      (format "Parallel worlds snapshot complete. %d repositories, %d total stars."
              total-repos total-stars))))

;; Main
(when (= *file* (System/getProperty "babashka.file"))
  (verify-gf3-conservation worlds)
  (let [results (pmap fetch-world worlds)  ; Parallel fetch!
        lake-path (or (first *command-line-args*) "gh_parallel_worlds.ducklake")]
    (snapshot-to-ducklake results lake-path)
    (say-announcement results)
    (println "Done.")))
