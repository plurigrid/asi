#!/usr/bin/env bb
;;; skill_invocation_acset.clj — Lazy ACSet for bidirectionally indexed invocations
;;;
;;; Schema:
;;;   Objects: Skill, Session, Invocation, Role
;;;   Morphisms:
;;;     skill: Invocation → Skill
;;;     session: Invocation → Session
;;;     role: Skill → Role
;;;   Attributes:
;;;     name: Skill → String
;;;     trit: Role → {-1, 0, +1}
;;;     timestamp: Invocation → DateTime
;;;
;;; Bidirectional indices:
;;;   skill_invocations: Skill → [Invocation]  (preimage of skill morphism)
;;;   session_invocations: Session → [Invocation]  (preimage of session morphism)

(ns skill-invocation-acset
  (:require [babashka.process :refer [shell]]
            [cheshire.core :as json]
            [clojure.string :as str]))

;; ═══════════════════════════════════════════════════════════════════════════
;; ACSet Schema Definition
;; ═══════════════════════════════════════════════════════════════════════════

(def schema
  "Catlab-style schema for skill invocations."
  {:name "SkillInvocationACSet"
   :objects [:Skill :Session :Invocation :Role]
   :morphisms {:skill {:dom :Invocation :cod :Skill}
               :session {:dom :Invocation :cod :Session}
               :role {:dom :Skill :cod :Role}}
   :attributes {:skill_name {:dom :Skill :cod :String}
                :session_id {:dom :Session :cod :String}
                :trit {:dom :Role :cod :Int}
                :gf3_role {:dom :Role :cod :String}
                :timestamp {:dom :Invocation :cod :DateTime}
                :args {:dom :Invocation :cod :String}}})

;; ═══════════════════════════════════════════════════════════════════════════
;; Lazy ACSet State (memoized DuckDB queries)
;; ═══════════════════════════════════════════════════════════════════════════

(defonce ^:private cache (atom {}))

(defn- query-duckdb
  "Execute DuckDB query and return results as EDN."
  [db-path sql]
  (let [cache-key [db-path sql]]
    (if-let [cached (get @cache cache-key)]
      cached
      (let [result (shell {:out :string :err :string}
                          "duckdb" "-readonly" db-path "-json" sql)]
        (when (zero? (:exit result))
          (let [parsed (json/parse-string (:out result) true)]
            (swap! cache assoc cache-key parsed)
            parsed))))))

(defn clear-cache! []
  (reset! cache {}))

;; ═══════════════════════════════════════════════════════════════════════════
;; Forward Morphisms (Invocation → Skill, Invocation → Session)
;; ═══════════════════════════════════════════════════════════════════════════

(defn skill
  "Forward morphism: Invocation → Skill"
  [db-path invocation-id]
  (first
   (query-duckdb db-path
    (format "SELECT DISTINCT tool_name AS skill_name
             FROM skill_usage_counts
             WHERE tool_name = (
               SELECT tool_name FROM skill_usage_counts LIMIT 1 OFFSET %d
             )" invocation-id))))

(defn session
  "Forward morphism: Invocation → Session"
  [db-path invocation-id session-file]
  {:session_id session-file
   :invocation_id invocation-id})

(defn role
  "Forward morphism: Skill → Role"
  [skill-record]
  (let [{:keys [velocity invocations]} skill-record
        velocity (or velocity 0)
        invocations (or invocations 0)]
    (cond
      (and (> velocity 5) (> invocations 100))
      {:trit 1 :gf3_role "GENERATOR"}

      (and (>= velocity 1) (<= velocity 5))
      {:trit 0 :gf3_role "COORDINATOR"}

      :else
      {:trit -1 :gf3_role "VALIDATOR"})))

;; ═══════════════════════════════════════════════════════════════════════════
;; Backward Indices (Preimages)
;; ═══════════════════════════════════════════════════════════════════════════

(defn skill-invocations
  "Preimage: Skill → [Invocation]
   Returns all invocations of a given skill."
  [db-path skill-name]
  (let [sql (format "
    SELECT
      tool_name AS skill_name,
      invocations,
      first_used,
      last_used
    FROM skill_usage_counts
    WHERE tool_name = '%s'
    " (str/replace skill-name "'" "''"))]
    (query-duckdb db-path sql)))

(defn session-invocations
  "Preimage: Session → [Invocation]
   Returns all skill invocations in a session."
  [session-file]
  ;; Parse JSONL session file for tool calls
  (try
    (let [lines (str/split-lines (slurp session-file))]
      (->> lines
           (keep (fn [line]
                   (try
                     (let [msg (json/parse-string line true)]
                       (when (= "assistant" (:role msg))
                         (when-let [tool-use (:toolUse (:content msg))]
                           {:tool_name (:name tool-use)
                            :timestamp (get msg :timestamp (System/currentTimeMillis))
                            :session_id session-file})))
                     (catch Exception _ nil))))
           vec))
    (catch Exception _ [])))

(defn role-skills
  "Preimage: Role → [Skill]
   Returns all skills assigned to a role."
  [db-path gf3-role]
  (let [trit-clause (case gf3-role
                      "GENERATOR" "velocity > 5 AND invocations > 100"
                      "COORDINATOR" "velocity BETWEEN 1 AND 5"
                      "VALIDATOR" "velocity < 1 OR invocations <= 100")
        sql (format "
    SELECT * FROM skill_portfolio_gf3
    WHERE gf3_role = '%s'
    ORDER BY sharpe DESC
    " gf3-role)]
    (query-duckdb db-path sql)))

;; ═══════════════════════════════════════════════════════════════════════════
;; ACSet Operations
;; ═══════════════════════════════════════════════════════════════════════════

(defn all-skills
  "Return all skills in the ACSet."
  [db-path]
  (query-duckdb db-path
    "SELECT tool_name AS skill_name, call_type, invocations, velocity, sharpe, trit, gf3_role
     FROM skill_portfolio_gf3
     ORDER BY sharpe DESC"))

(defn all-roles
  "Return all GF(3) roles."
  []
  [{:trit 1 :gf3_role "GENERATOR" :description "High velocity generators (>5/day, >100 total)"}
   {:trit 0 :gf3_role "COORDINATOR" :description "Moderate usage (1-5/day)"}
   {:trit -1 :gf3_role "VALIDATOR" :description "Low velocity specialists (<1/day)"}])

(defn skill-by-name
  "Lookup skill by name."
  [db-path skill-name]
  (first
   (query-duckdb db-path
    (format "SELECT * FROM skill_portfolio_gf3 WHERE tool_name = '%s'"
            (str/replace skill-name "'" "''")))))

;; ═══════════════════════════════════════════════════════════════════════════
;; Bidirectional Navigation (Specter-style)
;; ═══════════════════════════════════════════════════════════════════════════

(defn navigate
  "Bidirectional navigation through the ACSet.

   Paths:
     [:skill skill-name :invocations] → all invocations of skill
     [:role gf3-role :skills] → all skills with role
     [:session session-file :invocations] → all invocations in session
     [:skill skill-name :role] → GF(3) role of skill
   "
  [db-path & path]
  (let [[obj id attr] path]
    (case [obj attr]
      [:skill :invocations] (skill-invocations db-path id)
      [:skill :role] (role (skill-by-name db-path id))
      [:role :skills] (role-skills db-path id)
      [:session :invocations] (session-invocations id)
      nil)))

;; ═══════════════════════════════════════════════════════════════════════════
;; GF(3) Triad Verification
;; ═══════════════════════════════════════════════════════════════════════════

(defn gf3-sum
  "Compute GF(3) sum of a collection of skills."
  [skills]
  (reduce + (map :trit skills)))

(defn gf3-conserved?
  "Check if a skill set satisfies GF(3) conservation (sum ≡ 0 mod 3)."
  [skills]
  (zero? (mod (gf3-sum skills) 3)))

(defn find-balancing-skill
  "Find a skill that would balance the GF(3) sum to 0."
  [db-path current-skills]
  (let [current-sum (gf3-sum current-skills)
        needed-trit (- (mod (- current-sum) 3) (if (< (mod (- current-sum) 3) 0) 0 0))
        needed-trit (cond
                      (= (mod current-sum 3) 0) 0  ; Already balanced
                      (= (mod current-sum 3) 1) -1 ; Need MINUS
                      :else 1)                      ; Need PLUS
        candidates (role-skills db-path
                     (case needed-trit
                       1 "GENERATOR"
                       0 "COORDINATOR"
                       -1 "VALIDATOR"))]
    (first candidates)))

;; ═══════════════════════════════════════════════════════════════════════════
;; Export to Catlab-compatible format
;; ═══════════════════════════════════════════════════════════════════════════

(defn to-catlab-json
  "Export ACSet to Catlab-compatible JSON format."
  [db-path]
  (let [skills (all-skills db-path)
        roles (all-roles)
        ;; Build index maps
        skill-idx (into {} (map-indexed (fn [i s] [(:skill_name s) i]) skills))
        role-idx (into {} (map-indexed (fn [i r] [(:gf3_role r) i]) roles))]
    {:_type "SkillInvocationACSet"
     :Skill (mapv (fn [s] {:skill_name (:skill_name s)}) skills)
     :Role (mapv (fn [r] {:trit (:trit r) :gf3_role (:gf3_role r)}) roles)
     :Invocation []  ; Populated lazily
     :Session []     ; Populated lazily
     :skill []       ; morphism indices
     :session []
     :role (mapv (fn [s]
                   (role-idx (:gf3_role s)))
                 skills)}))

;; ═══════════════════════════════════════════════════════════════════════════
;; CLI and Demo
;; ═══════════════════════════════════════════════════════════════════════════

(defn print-portfolio-summary [db-path]
  (println)
  (println "╔═══════════════════════════════════════════════════════════════════════════════╗")
  (println "║              LAZY ACSET: Bidirectionally Indexed Invocations                  ║")
  (println "╚═══════════════════════════════════════════════════════════════════════════════╝")
  (println)
  (println "Schema: SkillInvocationACSet")
  (println "  Objects: Skill, Session, Invocation, Role")
  (println "  Morphisms: skill: Inv→Skill, session: Inv→Session, role: Skill→Role")
  (println)

  (println "═══════════════════════════════════════════════════════════════════════════════")
  (println "GF(3) Role Distribution:")
  (println "═══════════════════════════════════════════════════════════════════════════════")

  (doseq [role-name ["GENERATOR" "COORDINATOR" "VALIDATOR"]]
    (let [skills (role-skills db-path role-name)
          trit (case role-name "GENERATOR" "+1" "COORDINATOR" " 0" "VALIDATOR" "-1")]
      (println (format "\n  %s (trit=%s):" role-name trit))
      (println (format "    Count: %d skills" (count skills)))
      (when (seq skills)
        (println "    Top 5 by Sharpe ratio:")
        (doseq [s (take 5 skills)]
          (println (format "      - %-35s sharpe=%.2f  vel=%.1f  inv=%d"
                          (:tool_name s)
                          (or (:sharpe s) 0)
                          (or (:velocity s) 0)
                          (or (:invocations s) 0)))))))

  (println)
  (println "═══════════════════════════════════════════════════════════════════════════════")
  (println "Bidirectional Navigation Examples:")
  (println "═══════════════════════════════════════════════════════════════════════════════")

  (println "\n  (navigate db [:skill \"Bash\" :role])")
  (println "    →" (navigate db-path :skill "Bash" :role))

  (println "\n  (navigate db [:role \"VALIDATOR\" :skills])")
  (let [validators (take 3 (navigate db-path :role "VALIDATOR" :skills))]
    (doseq [v validators]
      (println (format "    → %s (sharpe=%.2f)" (:tool_name v) (or (:sharpe v) 0)))))

  (println)
  (println "═══════════════════════════════════════════════════════════════════════════════")
  (println "GF(3) Conservation Check:")
  (println "═══════════════════════════════════════════════════════════════════════════════")

  (let [all (all-skills db-path)
        sum (gf3-sum all)
        conserved? (gf3-conserved? all)]
    (println (format "\n  Total skills: %d" (count all)))
    (println (format "  Trit sum: %d" sum))
    (println (format "  Sum mod 3: %d" (mod sum 3)))
    (println (format "  GF(3) Conserved: %s" (if conserved? "YES ✓" "NO ✗"))))

  (println))

(defn -main [& args]
  (let [db-path (or (first args) (str (System/getProperty "user.home") "/.claude/history.duckdb"))]
    (print-portfolio-summary db-path)))

(when (= *file* (System/getProperty "babashka.file"))
  (-main))

;; Run demo
(-main)
