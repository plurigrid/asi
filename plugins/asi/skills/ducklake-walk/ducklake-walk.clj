#!/usr/bin/env bb
;; ducklake-walk.clj - Ergodic Random Walk over DuckDB Tables
;; ERGODIC (0) Coordinator Stream - GF(3) Color: Neutral (hue 120, green)
;;
;; Implements a Markov chain random walk that:
;; 1. Starts at a random table in the schema
;; 2. Follows foreign key relationships with probability p
;; 3. Performs random jumps with probability (1-p) for ergodicity
;; 4. Samples rows and accumulates statistics
;;
;; The random restart probability ensures irreducibility (ergodicity)
;; Similar to PageRank's teleportation for guaranteeing convergence
;;
;; Usage:
;;   bb ducklake-walk.clj                  # Creates temp demo DB
;;   bb ducklake-walk.clj /path/to/db.duckdb  # Uses existing DB

(require '[babashka.process :as p]
         '[babashka.fs :as fs]
         '[clojure.string :as str]
         '[cheshire.core :as json])

;; ============================================================================
;; Configuration
;; ============================================================================

(def config
  (atom {:db-path nil
         :random-restart-prob 0.15  ; Teleportation probability for ergodicity
         :max-steps 100             ; Maximum walk steps
         :sample-size 5             ; Rows to sample per visit
         :verbose true}))

;; ============================================================================
;; DuckDB CLI Interface
;; ============================================================================

(defn duckdb-query
  "Execute SQL query using DuckDB CLI and return parsed JSON results."
  [db-path sql]
  (let [result (p/sh {:in sql}
                     "duckdb" db-path "-json")]
    (if (zero? (:exit result))
      (let [output (str/trim (:out result))]
        (if (str/blank? output)
          []
          (json/parse-string output true)))
      (do
        (when (and (:verbose @config) (not (str/blank? (:err result))))
          (binding [*out* *err*]
            (println "DuckDB Error:" (:err result))))
        []))))

(defn duckdb-exec!
  "Execute SQL statement using DuckDB CLI (no return)."
  [db-path sql]
  (let [result (p/sh {:in sql} "duckdb" db-path)]
    (when (and (not (zero? (:exit result)))
               (not (str/blank? (:err result))))
      (binding [*out* *err*]
        (println "DuckDB Error:" (:err result))))
    (:exit result)))

;; ============================================================================
;; Schema Introspection
;; ============================================================================

(defn get-all-tables
  "Retrieve all tables in the database with their schemas."
  [db-path]
  (duckdb-query db-path
    "SELECT table_schema, table_name
     FROM information_schema.tables
     WHERE table_type = 'BASE TABLE'
     ORDER BY table_schema, table_name"))

(defn get-foreign-keys
  "Get foreign key relationships for a table."
  [db-path schema table]
  (duckdb-query db-path
    (format "SELECT constraint_column_names as from_columns, constraint_text
             FROM duckdb_constraints()
             WHERE database_name = current_database()
               AND schema_name = '%s'
               AND table_name = '%s'
               AND constraint_type = 'FOREIGN KEY'"
            schema table)))

(defn get-referencing-tables
  "Find tables that reference this table (reverse FKs)."
  [db-path schema table]
  (duckdb-query db-path
    (format "SELECT DISTINCT schema_name, table_name
             FROM duckdb_constraints()
             WHERE constraint_type = 'FOREIGN KEY'
               AND constraint_text LIKE '%%REFERENCES \"%s\".\"%s\"%%'"
            schema table)))

(defn get-table-row-count
  "Get row count for a table."
  [db-path schema table]
  (let [result (duckdb-query db-path
                 (format "SELECT COUNT(*) as cnt FROM \"%s\".\"%s\"" schema table))]
    (or (-> result first :cnt) 0)))

(defn sample-rows
  "Sample random rows from a table."
  [db-path schema table n]
  (let [result (duckdb-query db-path
                 (format "SELECT * FROM \"%s\".\"%s\" USING SAMPLE %d ROWS" schema table n))]
    (if (seq result)
      result
      (duckdb-query db-path
        (format "SELECT * FROM \"%s\".\"%s\" LIMIT %d" schema table n)))))

;; ============================================================================
;; Graph Construction
;; ============================================================================

(defn build-table-graph
  "Build adjacency list representation of table relationships."
  [db-path tables]
  (reduce
   (fn [graph {:keys [table_schema table_name]}]
     (let [fks (get-foreign-keys db-path table_schema table_name)
           refs (get-referencing-tables db-path table_schema table_name)
           node-id (keyword (str table_schema "." table_name))
           ;; Outgoing edges (FK references)
           outgoing (mapv (fn [fk]
                           (when-let [match (re-find #"REFERENCES \"?(\w+)\"?\.\"?(\w+)\"?"
                                                     (str (:constraint_text fk)))]
                             (keyword (str (nth match 1) "." (nth match 2)))))
                         fks)
           ;; Incoming edges (tables referencing us)
           incoming (mapv (fn [ref]
                           (keyword (str (:schema_name ref) "." (:table_name ref))))
                         refs)
           neighbors (vec (distinct (concat (filter some? outgoing) incoming)))]
       (assoc graph node-id {:schema table_schema
                             :table table_name
                             :neighbors neighbors
                             :row-count (get-table-row-count db-path table_schema table_name)})))
   {}
   tables))

;; ============================================================================
;; Random Walk Engine
;; ============================================================================

(defn random-choice
  "Choose a random element from a collection."
  [coll]
  (when (seq coll)
    (nth coll (rand-int (count coll)))))

(defn weighted-choice
  "Choose based on weights (row counts for preferential attachment)."
  [graph candidates]
  (if (empty? candidates)
    nil
    (let [weights (mapv #(max 1 (get-in graph [% :row-count] 1)) candidates)
          total (reduce + weights)
          r (* (rand) total)]
      (loop [remaining r
             idx 0]
        (if (>= idx (count candidates))
          (last candidates)
          (let [w (nth weights idx)]
            (if (< remaining w)
              (nth candidates idx)
              (recur (- remaining w) (inc idx)))))))))

(defn walk-step
  "Perform one step of the random walk."
  [graph current-node all-nodes cfg]
  (let [{:keys [neighbors]} (get graph current-node)
        restart? (< (rand) (:random-restart-prob cfg))]
    (cond
      ;; Random restart for ergodicity (teleportation)
      restart?
      {:next-node (random-choice all-nodes)
       :transition-type :teleport
       :reason "random restart for ergodicity"}

      ;; Follow a relationship if available
      (seq neighbors)
      {:next-node (weighted-choice graph neighbors)
       :transition-type :edge
       :reason (str "followed edge from " (name current-node))}

      ;; Dead end - must teleport
      :else
      {:next-node (random-choice all-nodes)
       :transition-type :forced-teleport
       :reason "no outgoing edges"})))

(defn run-random-walk
  "Execute the random walk and collect statistics."
  [db-path cfg]
  (let [tables (get-all-tables db-path)
        _ (when (empty? tables)
            (throw (ex-info "No tables found in database" {:db-path db-path})))
        graph (build-table-graph db-path tables)
        all-nodes (vec (keys graph))
        start-node (random-choice all-nodes)]

    (when (:verbose cfg)
      (println "\n=== DuckLake Random Walk ===")
      (println "GF(3) Color: ERGODIC (0) - Neutral Coordinator")
      (println "Database:" db-path)
      (println "Tables found:" (count all-nodes))
      (println "Random restart probability:" (:random-restart-prob cfg))
      (println "Starting at:" (name start-node))
      (println ""))

    (loop [step 0
           current start-node
           visit-counts {}
           samples []
           transitions []]
      (if (>= step (:max-steps cfg))
        ;; Return walk statistics
        {:total-steps step
         :unique-tables-visited (count visit-counts)
         :total-tables (count all-nodes)
         :coverage (double (/ (count visit-counts) (count all-nodes)))
         :visit-counts (sort-by val > visit-counts)
         :samples samples
         :transitions transitions
         :graph graph}

        ;; Continue walk
        (let [node-info (get graph current)
              sampled (sample-rows db-path (:schema node-info) (:table node-info)
                                   (:sample-size cfg))
              {:keys [next-node transition-type]}
              (walk-step graph current all-nodes cfg)]

          (when (:verbose cfg)
            (println (format "Step %3d: %-30s (rows: %d) -> %s [%s]"
                           step
                           (name current)
                           (:row-count node-info)
                           (name next-node)
                           (name transition-type))))

          (recur (inc step)
                 next-node
                 (update visit-counts current (fnil inc 0))
                 (conj samples {:table current :rows sampled})
                 (conj transitions {:from current
                                   :to next-node
                                   :type transition-type
                                   :step step})))))))

;; ============================================================================
;; Ergodicity Analysis
;; ============================================================================

(defn analyze-ergodicity
  "Analyze the walk for ergodic properties."
  [results]
  (let [{:keys [visit-counts total-tables coverage transitions]} results
        teleports (count (filter #(#{:teleport :forced-teleport} (:type %)) transitions))
        edges (count (filter #(= :edge (:type %)) transitions))

        ;; Compute stationary distribution estimate
        total-visits (reduce + (vals visit-counts))
        stationary-dist (into {} (map (fn [[k v]] [k (double (/ v total-visits))])
                                      visit-counts))]

    {:coverage-ratio coverage
     :teleport-ratio (if (pos? (+ teleports edges))
                       (double (/ teleports (+ teleports edges)))
                       0.0)
     :edge-ratio (if (pos? (+ teleports edges))
                   (double (/ edges (+ teleports edges)))
                   0.0)
     :entropy (if (pos? (count stationary-dist))
                (- (reduce + (map (fn [[_ prob]]
                                   (if (pos? prob)
                                     (* prob (Math/log prob))
                                     0))
                                 stationary-dist)))
                0.0)
     :max-entropy (if (pos? total-tables)
                    (Math/log total-tables)
                    0.0)
     :stationary-distribution stationary-dist
     :is-ergodic (> coverage 0.8)}))

(defn print-analysis
  "Print ergodicity analysis results."
  [results analysis]
  (println "\n=== Ergodicity Analysis ===")
  (println "Coverage:" (format "%.1f%%" (* 100 (:coverage-ratio analysis))))
  (println "Edge transitions:" (format "%.1f%%" (* 100 (:edge-ratio analysis))))
  (println "Teleportations:" (format "%.1f%%" (* 100 (:teleport-ratio analysis))))
  (println "Entropy:" (format "%.3f / %.3f (max)"
                              (:entropy analysis)
                              (:max-entropy analysis)))
  (println "Ergodic:" (if (:is-ergodic analysis) "YES" "NO (increase steps or restart prob)"))

  (println "\n=== Visit Distribution (Top 10) ===")
  (doseq [[table cnt] (take 10 (:visit-counts results))]
    (let [freq (get (:stationary-distribution analysis) table 0.0)]
      (println (format "  %-30s: %3d visits (%.2f%%)"
                       (name table) cnt (* 100 freq))))))

;; ============================================================================
;; Demo Mode: Create Sample Schema
;; ============================================================================

(defn create-demo-schema
  "Create a demo schema with tables and relationships for testing."
  [db-path]
  (println "Creating demo DuckLake schema...")

  ;; Create tables with inline FK constraints for DuckDB compatibility
  (let [sql "
    CREATE SCHEMA IF NOT EXISTS ducklake;

    -- Base tables first (no FK dependencies)
    CREATE TABLE IF NOT EXISTS ducklake.users (
      id INTEGER PRIMARY KEY,
      name VARCHAR,
      email VARCHAR,
      created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    );

    CREATE TABLE IF NOT EXISTS ducklake.warehouses (
      id INTEGER PRIMARY KEY,
      name VARCHAR,
      location VARCHAR
    );

    -- Categories with self-reference
    CREATE TABLE IF NOT EXISTS ducklake.categories (
      id INTEGER PRIMARY KEY,
      name VARCHAR,
      parent_id INTEGER REFERENCES ducklake.categories(id)
    );

    -- Products referencing categories
    CREATE TABLE IF NOT EXISTS ducklake.products (
      id INTEGER PRIMARY KEY,
      name VARCHAR,
      price DECIMAL(10,2),
      category_id INTEGER REFERENCES ducklake.categories(id)
    );

    -- Orders referencing users
    CREATE TABLE IF NOT EXISTS ducklake.orders (
      id INTEGER PRIMARY KEY,
      user_id INTEGER REFERENCES ducklake.users(id),
      total DECIMAL(10,2),
      status VARCHAR,
      created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
    );

    -- Order items referencing orders and products
    CREATE TABLE IF NOT EXISTS ducklake.order_items (
      id INTEGER PRIMARY KEY,
      order_id INTEGER REFERENCES ducklake.orders(id),
      product_id INTEGER REFERENCES ducklake.products(id),
      quantity INTEGER,
      price DECIMAL(10,2)
    );

    -- Reviews referencing users and products
    CREATE TABLE IF NOT EXISTS ducklake.reviews (
      id INTEGER PRIMARY KEY,
      user_id INTEGER REFERENCES ducklake.users(id),
      product_id INTEGER REFERENCES ducklake.products(id),
      rating INTEGER,
      comment TEXT
    );

    -- Inventory referencing products and warehouses
    CREATE TABLE IF NOT EXISTS ducklake.inventory (
      id INTEGER PRIMARY KEY,
      product_id INTEGER REFERENCES ducklake.products(id),
      warehouse_id INTEGER REFERENCES ducklake.warehouses(id),
      quantity INTEGER
    );

    -- Insert sample data (respecting FK order)
    -- Base tables first
    INSERT INTO ducklake.users VALUES
      (1, 'Alice', 'alice@example.com', CURRENT_TIMESTAMP),
      (2, 'Bob', 'bob@example.com', CURRENT_TIMESTAMP),
      (3, 'Charlie', 'charlie@example.com', CURRENT_TIMESTAMP);

    INSERT INTO ducklake.warehouses VALUES
      (1, 'Main Warehouse', 'San Francisco'),
      (2, 'East Coast', 'New York');

    -- Categories (parent first, then children)
    INSERT INTO ducklake.categories(id, name, parent_id) VALUES (1, 'Electronics', NULL);
    INSERT INTO ducklake.categories(id, name, parent_id) VALUES (4, 'Books', NULL);
    INSERT INTO ducklake.categories(id, name, parent_id) VALUES (2, 'Phones', 1);
    INSERT INTO ducklake.categories(id, name, parent_id) VALUES (3, 'Laptops', 1);

    -- Products (after categories)
    INSERT INTO ducklake.products VALUES
      (1, 'iPhone 15', 999.99, 2),
      (2, 'MacBook Pro', 2499.99, 3),
      (3, 'Clojure Programming', 49.99, 4),
      (4, 'Galaxy S24', 899.99, 2);

    -- Orders (after users)
    INSERT INTO ducklake.orders VALUES
      (1, 1, 1049.98, 'completed', CURRENT_TIMESTAMP),
      (2, 2, 2499.99, 'pending', CURRENT_TIMESTAMP);

    -- Order items (after orders and products)
    INSERT INTO ducklake.order_items VALUES
      (1, 1, 1, 1, 999.99),
      (2, 1, 3, 1, 49.99),
      (3, 2, 2, 1, 2499.99);

    -- Reviews (after users and products)
    INSERT INTO ducklake.reviews VALUES
      (1, 1, 1, 5, 'Great phone!'),
      (2, 2, 2, 4, 'Excellent laptop'),
      (3, 1, 3, 5, 'Must read for Clojurists');

    -- Inventory (after products and warehouses)
    INSERT INTO ducklake.inventory VALUES
      (1, 1, 1, 100),
      (2, 2, 1, 50),
      (3, 3, 2, 200),
      (4, 4, 1, 75);
  "]
    (duckdb-exec! db-path sql))

  (println "Demo schema created with 8 tables and FK relationships"))

;; ============================================================================
;; Main Entry Point
;; ============================================================================

(defn -main [& args]
  (let [user-db-path (first args)
        ;; Use temp file for demo mode if no path provided
        demo-mode? (nil? user-db-path)
        db-path (if demo-mode?
                  (str (fs/path (fs/temp-dir) (str "ducklake-" (System/currentTimeMillis) ".duckdb")))
                  user-db-path)]

    (swap! config assoc :db-path db-path)

    (try
      ;; Create demo schema if in demo mode
      (when demo-mode?
        (create-demo-schema db-path))

      ;; Run the random walk
      (let [results (run-random-walk db-path @config)
            analysis (analyze-ergodicity results)]

        (print-analysis results analysis)

        ;; Return results for programmatic use
        {:results results
         :analysis analysis})

      (finally
        ;; Clean up temp file in demo mode
        (when demo-mode?
          (fs/delete-if-exists db-path)
          (fs/delete-if-exists (str db-path ".wal")))))))

;; Run main
(-main (first *command-line-args*))
