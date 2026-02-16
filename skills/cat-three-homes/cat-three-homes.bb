#!/usr/bin/env bb
;; Cat# Three Homes - Global Access Script
;; Maps concepts to the three homes for categories in Cat#

(require '[clojure.string :as str]
         '[babashka.process :refer [shell]])

;; ═══════════════════════════════════════════════════════════════════
;; THE THREE HOMES
;; ═══════════════════════════════════════════════════════════════════

(def homes
  {1 {:name "Polynomial Comonads"
      :structure "Comod(Poly, y, ◁)"
      :description "Categories ARE objects of Cat#"
      :skill :gay-mcp
      :trit 1
      :color "#E67F86"
      :formula "Σ_{A:Ob(C)} y^{C[A]}"}
   
   2 {:name "Monads in Span"
      :structure "Mod(Span) ≅ Prof"
      :description "Categories = monads in linear restriction"
      :skill :acsets
      :trit 0
      :color "#49EE54"
      :formula "Comod(Set, 1, ×) ≅ Span"}
   
   3 {:name "Path Algebras"
      :structure "path-complete graphs"
      :description "Categories = graphs with path composition"
      :skill :bisimulation-game
      :trit -1
      :color "#1316BB"
      :formula "g = y³ + y, path: g◁ → ◁g"}})

;; ═══════════════════════════════════════════════════════════════════
;; CONCEPT → HOME MAPPING
;; ═══════════════════════════════════════════════════════════════════

(def concept->home
  {"polynomial"      1
   "comonad"         1
   "cofunctor"       1
   "state"           1
   "dynamics"        1
   
   "span"            2
   "profunctor"      2
   "bimodule"        2
   "schema"          2
   "doctrine"        2
   "double category" 2
   "model"           2
   
   "graph"           3
   "path"            3
   "algebra"         3
   "nerve"           3
   "equivalence"     3
   "bisimulation"    3})

;; ═══════════════════════════════════════════════════════════════════
;; DISPLAY FUNCTIONS
;; ═══════════════════════════════════════════════════════════════════

(defn show-home [id]
  (let [{:keys [name structure description skill trit color formula]} (homes id)]
    (println (str "\n🏠 HOME " id ": " name))
    (println "════════════════════════════════════════════════")
    (println (str "  Structure:   " structure))
    (println (str "  Formula:     " formula))
    (println (str "  Description: " description))
    (println (str "  Skill:       " (clojure.core/name skill) " [" (if (pos? trit) "+" "") trit "]"))
    (println (str "  Color:       " color))))

(defn show-all-homes []
  (println "\n╔════════════════════════════════════════════════════════════════╗")
  (println "║          CAT# = Comod(Poly, y, ◁) — THREE HOMES               ║")
  (println "╠════════════════════════════════════════════════════════════════╣")
  (println "║                                                                ║")
  (println "║  HOME 1: Polynomial Comonads        [+1] gay-mcp              ║")
  (println "║          Categories ARE objects of Cat#                        ║")
  (println "║                                                                ║")
  (println "║  HOME 2: Monads in Span             [ 0] acsets               ║")
  (println "║          Comod(Set,1,×) ≅ Span, Mod(Span) ≅ Prof              ║")
  (println "║                                                                ║")
  (println "║  HOME 3: Path Algebras              [-1] bisimulation-game    ║")
  (println "║          Categories = path-complete graphs                     ║")
  (println "║                                                                ║")
  (println "╠════════════════════════════════════════════════════════════════╣")
  (println "║  GF(3): (-1) + (0) + (+1) = 0 ✓  BALANCED                     ║")
  (println "╚════════════════════════════════════════════════════════════════╝"))

(defn dispatch-concept [concept]
  (let [home-id (get concept->home (str/lower-case concept) 2)
        home (homes home-id)]
    (println (str "\n📍 DISPATCH: \"" concept "\""))
    (println (str "  → Home " home-id ": " (:name home)))
    (println (str "  → Skill: " (name (:skill home)) " [" (:trit home) "]"))
    (println (str "  → Color: " (:color home)))))

(defn show-triads []
  (println "\n🔺 GF(3) TRIADS")
  (println "════════════════════════════════════════════════")
  (println "  bisimulation-game (-1) ⊗ cat-three-homes (0) ⊗ gay-mcp (+1) = 0 ✓")
  (println "  path-algebras     (-1) ⊗ span-prof      (0) ⊗ poly-comonad (+1) = 0 ✓")
  (println "  temporal-coalgebra(-1) ⊗ catsharp      (0) ⊗ free-monad-gen(+1) = 0 ✓"))

;; ═══════════════════════════════════════════════════════════════════
;; DUCKDB INTEGRATION
;; ═══════════════════════════════════════════════════════════════════

(defn export-to-duckdb []
  (let [sql "CREATE TABLE IF NOT EXISTS cat_homes (
    home_id INT PRIMARY KEY,
    name VARCHAR,
    structure VARCHAR,
    skill VARCHAR,
    trit TINYINT,
    color VARCHAR
);

INSERT OR REPLACE INTO cat_homes VALUES
(1, 'Polynomial Comonads', 'Comod(Poly,y,◁)', 'gay-mcp', 1, '#E67F86'),
(2, 'Monads in Span', 'Mod(Span)≅Prof', 'acsets', 0, '#49EE54'),
(3, 'Path Algebras', 'path-complete graphs', 'bisimulation-game', -1, '#1316BB');

SELECT * FROM cat_homes;"]
    (shell "duckdb" "dendroidal.duckdb" "-c" sql)))

;; ═══════════════════════════════════════════════════════════════════
;; MAIN
;; ═══════════════════════════════════════════════════════════════════

(defn -main [& args]
  (let [cmd (first args)]
    (case cmd
      "--home" (if-let [id (some-> (second args) parse-long)]
                 (show-home id)
                 (println "Usage: --home <1|2|3>"))
      
      "--dispatch" (if-let [concept (second args)]
                     (dispatch-concept concept)
                     (println "Usage: --dispatch <concept>"))
      
      "--triads" (show-triads)
      
      "--export" (do (export-to-duckdb)
                     (println "Exported to dendroidal.duckdb"))
      
      "--all" (show-all-homes)
      
      ;; Default
      (show-all-homes))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
