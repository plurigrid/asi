#!/usr/bin/env bb
;;; Chemputation Triad Loader
;;; Loads turing-chemputer (-1), modelica (0), crn-topology (+1)
;;; GF(3) Sum: -1 + 0 + 1 = 0 ✓

(ns chemputation-triad
  (:require [babashka.process :refer [shell]]
            [clojure.java.io :as io]
            [clojure.string :as str]))

(def triad
  [{:name "turing-chemputer"
    :trit -1
    :role "MINUS (Executor)"
    :description "XDL → Hardware execution"
    :color "#2626D8"}  ; Blue
   {:name "modelica"
    :trit 0
    :role "ERGODIC (Coordinator)"
    :description "Thermodynamic simulation"
    :color "#26D826"}  ; Green
   {:name "crn-topology"
    :trit +1
    :role "PLUS (Generator)"
    :description "Reaction network topology"
    :color "#D82626"}]) ; Red

(defn verify-gf3 [skills]
  (let [sum (reduce + (map :trit skills))]
    {:sum sum
     :mod3 (mod sum 3)
     :conserved? (zero? (mod sum 3))}))

(defn skill-path [name]
  (str (System/getenv "HOME") "/.claude/skills/" name "/SKILL.md"))

(defn skill-exists? [name]
  (.exists (io/file (skill-path name))))

(defn print-triad-status []
  (println "\n╔════════════════════════════════════════════════════════════╗")
  (println "║           CHEMPUTATION TRIAD (GF(3) = 0)                   ║")
  (println "╠════════════════════════════════════════════════════════════╣")
  (doseq [{:keys [name trit role description color]} triad]
    (let [exists? (skill-exists? name)
          status (if exists? "✓" "✗")
          trit-str (format "%+d" trit)]
      (printf "║ %s %-20s │ %s │ %-25s ║\n"
              status name trit-str role)))
  (println "╠════════════════════════════════════════════════════════════╣")
  (let [{:keys [sum mod3 conserved?]} (verify-gf3 triad)]
    (printf "║ GF(3) Sum: %d ≡ %d (mod 3) │ %s                        ║\n"
            sum mod3 (if conserved? "CONSERVED ✓" "VIOLATED ✗")))
  (println "╚════════════════════════════════════════════════════════════╝\n"))

(defn announce-triad []
  (try
    (shell "say" "-v" "Anna" "Chemputation triad loaded. Turing chemputer minus one. Modelica zero. C R N topology plus one. G F 3 conserved.")
    (catch Exception e
      (println "Voice announcement failed (say not available)"))))

(defn load-skill! [skill]
  (let [{:keys [name trit role]} skill
        path (skill-path name)]
    (if (skill-exists? name)
      (do
        (printf "Loading %s (%+d) %s... " name trit role)
        (println "✓"))
      (printf "⚠ Skill not found: %s\n" name))))

(defn wolframscript-available? []
  (try
    (zero? (:exit (shell {:out :string :err :string} "which" "wolframscript")))
    (catch Exception _ false)))

(defn test-modelica-connection []
  (when (wolframscript-available?)
    (println "\nTesting Wolfram Language connection...")
    (try
      (let [result (shell {:out :string :err :string}
                          "wolframscript" "-code"
                          "Print[SystemModelExamples[\"Modelica.Electrical.*\"] // Length]")]
        (if (zero? (:exit result))
          (printf "✓ Modelica Standard Library accessible (%s examples)\n"
                  (str/trim (:out result)))
          (println "⚠ wolframscript available but SystemModel not accessible")))
      (catch Exception e
        (println "⚠ wolframscript test failed")))))

(defn demo-pipeline []
  (println "\n── Chemputation Pipeline Demo ──\n")
  (println "Step 1: crn-topology (+1) generates reaction network")
  (println "        A + B ⇌ C (Keq = 10)")
  (println)
  (println "Step 2: modelica (0) simulates thermodynamics")
  (println "        FindSystemModelEquilibrium → {A: 0.1, B: 0.1, C: 0.8}")
  (println)
  (println "Step 3: turing-chemputer (-1) executes synthesis")
  (println "        XDL: Add A, Add B, Heat 80°C, React 2h, Filter")
  (println)
  (println "GF(3) Conservation: (+1) + (0) + (-1) = 0 ✓"))

(defn -main [& args]
  (print-triad-status)
  
  (println "Loading triad skills...")
  (doseq [skill triad]
    (load-skill! skill))
  
  (test-modelica-connection)
  
  (when (some #{"--demo"} args)
    (demo-pipeline))
  
  (when (some #{"--voice"} args)
    (announce-triad))
  
  (println "\nChemputation triad ready."))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
