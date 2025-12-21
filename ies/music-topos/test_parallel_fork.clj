(require 'music-topos.parallel-color-fork)
(require 'clojure.pprint)

(println "════════════════════════════════════════════════════════════════")
(println "PARALLEL COLOR FORK SYSTEM TEST")
(println "════════════════════════════════════════════════════════════════")
(println "")

(println "Test 1: Generate 1069 parallel deterministic colors")
(println "─────────────────────────────────────────────────────")
(time
  (let [colors (music-topos.parallel-color-fork/fork-into-colors 1069)]
    (println (str "Generated " (count colors) " colors"))
    (println "First 3 colors:")
    (clojure.pprint/pprint (take 3 colors))))

(println "")
(println "Test 2: Verify SPI (reproducibility)")
(println "─────────────────────────────────────────────────────")
(time
  (let [run1 (music-topos.parallel-color-fork/fork-into-colors 1069)
        run2 (music-topos.parallel-color-fork/fork-into-colors 1069)
        identical? (= run1 run2)]
    (println (if identical?
               "✓ SPI VERIFIED: Both runs produced identical results"
               "✗ SPI FAILED: Results differ between runs"))))

(println "")
(println "Test 3: Fork into binary tree (depth 4, branching 2)")
(println "─────────────────────────────────────────────────────")
(time
  (let [tree (music-topos.parallel-color-fork/fork-into-tree 4 2)]
    (println (str "Generated tree with " (count tree) " leaf nodes"))
    (println "Expected: 2^4 = 16 nodes")))

(println "")
(println "Test 4: Ternary negotiation")
(println "─────────────────────────────────────────────────────")
(time
  (let [result (music-topos.parallel-color-fork/fork-with-ternary-negotiation 100 "/tmp/test-ternary.duckdb")]
    (println "Ternary negotiation complete")
    (println (str "Colors-by-fork: " (count (:colors-by-fork result)) " fork streams"))
    (println (str "Ternary ACSet: " (if (:ternary-acset (:ternary-negotiation result)) "✓ Created" "✗ Failed")))))

(println "")
(println "Test 5: Full plurigrid loop (3 iterations)")
(println "─────────────────────────────────────────────────────")
(time
  (let [result (music-topos.parallel-color-fork/enact-full-plurigrid-loop 50 "/tmp/test-plurigrid.duckdb" 3)]
    (println (str "Completed " (count result) " iterations"))
    (println "Each iteration includes: compose → negotiate → freeze → propagate")))

(println "")
(println "════════════════════════════════════════════════════════════════")
(println "All tests complete!")
(println "════════════════════════════════════════════════════════════════")
