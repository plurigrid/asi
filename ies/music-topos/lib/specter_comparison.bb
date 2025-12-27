#!/usr/bin/env bb
;; specter_comparison.bb
;; 
;; Babashka Specter examples for comparison with Julia SpecterACSet
;; Run: bb lib/specter_comparison.bb

(require '[babashka.deps :as deps])

;; Specter not available in bb by default, so we show equivalent patterns
;; using core Clojure functions

(println "╔═══════════════════════════════════════════════════════════════════════════╗")
(println "║  SPECTER WORLD: Clojure/Babashka Equivalent Patterns                     ║")
(println "║  Compare with: julia lib/specter_acset.jl                                ║")
(println "╚═══════════════════════════════════════════════════════════════════════════╝")
(println)

;; ============================================================================
;; COMPARISON 1: Basic Navigation (without Specter)
;; ============================================================================
(println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
(println "COMPARISON 1: Basic Navigation")
(println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
(println)

(println "┌─────────────────────────────────────┬─────────────────────────────────────┐")
(println "│ Clojure (with Specter)              │ Clojure (core functions)            │")
(println "├─────────────────────────────────────┼─────────────────────────────────────┤")
(println "│ (select [ALL even?] data)           │ (filter even? data)                 │")
(println "│ (transform [ALL even?] #(* % 10))   │ (map #(if (even? %) (* % 10) %) ..) │")
(println "└─────────────────────────────────────┴─────────────────────────────────────┘")
(println)

(def data [1 2 3 4 5 6 7 8 9 10])

(println "Babashka execution (core functions):")
(println "  data =" data)
(println "  (filter even? data)")
(println "  →" (vec (filter even? data)))
(println "  (mapv #(if (even? %) (* % 10) %) data)")
(println "  →" (mapv #(if (even? %) (* % 10) %) data))
(println)

;; ============================================================================
;; COMPARISON 2: Nested Map Navigation
;; ============================================================================
(println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
(println "COMPARISON 2: Nested Map Navigation")
(println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
(println)

(println "┌─────────────────────────────────────┬─────────────────────────────────────┐")
(println "│ Clojure (with Specter)              │ Clojure (core functions)            │")
(println "├─────────────────────────────────────┼─────────────────────────────────────┤")
(println "│ (select [:users ALL :name] data)    │ (map :name (:users data))           │")
(println "│ (transform [:users ALL :age] inc)   │ (update data :users                 │")
(println "│                                     │   #(mapv (fn [u] (update u :age inc)│")
(println "│                                     │          ) %))                      │")
(println "└─────────────────────────────────────┴─────────────────────────────────────┘")
(println)

(def nested {:users [{:name "Alice" :age 30}
                     {:name "Bob" :age 25}]})

(println "Babashka execution:")
(println "  (map :name (:users nested))")
(println "  →" (vec (map :name (:users nested))))
(println)

;; ============================================================================
;; COMPARISON 3: What Specter provides that core doesn't
;; ============================================================================
(println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
(println "KEY INSIGHT: Specter's Advantage (Bidirectionality)")
(println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
(println)
(println "With Specter, the SAME path works for both select AND transform:")
(println)
(println "  path = [ALL even?]")
(println)
(println "  (select path data)      → selects even numbers")
(println "  (transform path f data) → transforms even numbers in-place")
(println)
(println "Without Specter, you need different code for selection vs transformation.")
(println)

;; ============================================================================
;; S-expression manipulation (Clojure's strength)
;; ============================================================================
(println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
(println "S-EXPRESSION MANIPULATION: Clojure's Native Strength")
(println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
(println)

(def sexp '(define (square x) (* x x)))

(println "  sexp =" sexp)
(println)
(println "  Clojure: Code IS data, so sexp manipulation is native:")
(println)
(println "  (first sexp)           →" (first sexp))
(println "  (second sexp)          →" (second sexp))
(println "  (first (second sexp))  →" (first (second sexp)))
(println)

;; Transform sexp
(defn rename-fn [sexp old-name new-name]
  (clojure.walk/postwalk 
    #(if (= % old-name) new-name %)
    sexp))

(println "  (rename-fn sexp 'square 'cube)")
(println "  →" (rename-fn sexp 'square 'cube))
(println)

;; ============================================================================
;; What Julia SpecterACSet adds
;; ============================================================================
(println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
(println "JULIA SPECTERACSET UNIQUE FEATURES")
(println "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━")
(println)
(println "Features Julia SpecterACSet provides that Clojure Specter doesn't:")
(println)
(println "  1. ACSet Navigation")
(println "     - acset_field(:E, :src)  → navigate schema morphisms")
(println "     - acset_where(:E, :src, ==(1))  → filter by predicate")
(println "     - Works with Catlab.jl algebraic databases")
(println)
(println "  2. Typed S-expression Nodes")
(println "     - SEXP_HEAD, SEXP_WALK, sexp_nth(n), ATOM_VALUE")
(println "     - Atom vs SList type discrimination")
(println "     - (Clojure uses untyped lists/symbols)")
(println)
(println "  3. Cross-Domain Bridge")
(println "     - sexp_of_acset(graph) → serialize to sexp")
(println "     - Navigate the sexp, then deserialize back")
(println "     - acset_of_sexp(GraphType, sexp) → reconstruct")
(println)
(println "  4. Gay.jl Colored Sexps")
(println "     - Deterministic LCH colors via SplitMix64")
(println "     - Each node carries color for visualization")
(println)
(println "  5. Category-Theoretic Integration")
(println "     - Navigate ∫G (category of elements)")
(println "     - Work with schema objects, morphisms, attributes")
(println)

;; ============================================================================
;; Summary
;; ============================================================================
(println "╔═══════════════════════════════════════════════════════════════════════════╗")
(println "║  SUMMARY: Clojure vs Julia                                               ║")
(println "╠═══════════════════════════════════════════════════════════════════════════╣")
(println "║  Clojure Specter:                                                        ║")
(println "║    ✓ Elegant bidirectional paths                                         ║")
(println "║    ✓ Inline caching for performance                                      ║")
(println "║    ✓ Native code-as-data (sexp is first-class)                           ║")
(println "║    ✗ No ACSet/categorical database support                               ║")
(println "║                                                                          ║")
(println "║  Julia SpecterACSet:                                                     ║")
(println "║    ✓ Same bidirectional patterns                                         ║")
(println "║    ✓ ACSet navigation (Catlab integration)                               ║")
(println "║    ✓ Typed sexp nodes (Atom/SList discrimination)                        ║")
(println "║    ✓ Cross-domain: ACSet ↔ Sexp ↔ String                                 ║")
(println "║    ✓ Gay.jl deterministic coloring                                       ║")
(println "╚═══════════════════════════════════════════════════════════════════════════╝")
