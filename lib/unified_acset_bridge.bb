#!/usr/bin/env bb
;;; unified_acset_bridge.bb — Polyglot ACSet Bridge
;;;
;;; Unifies ACSet representations across:
;;;   - Babashka/Clojure (EDN)
;;;   - Julia/ACSets.jl (Catlab JSON)
;;;   - Hylang/Python (py-acset)
;;;   - LispSyntax.jl (S-expressions)
;;;
;;; Common interchange format: Colored S-expressions with GF(3) trits
;;;
;;; Schema: (acset :name <string> :objects [...] :morphisms {...} :attributes {...})

(ns unified-acset-bridge
  (:require [babashka.fs :as fs]
            [babashka.process :refer [shell]]
            [cheshire.core :as json]
            [clojure.string :as str]
            [clojure.edn :as edn]))

;; ═══════════════════════════════════════════════════════════════════════════
;; SplitMix64 (matches Gay.jl seed=1069=0x42D)
;; ═══════════════════════════════════════════════════════════════════════════

(def ^:const GOLDEN 0x9E3779B97F4A7C15)
(def ^:const MIX1 0xBF58476D1CE4E5B9)
(def ^:const MIX2 0x94D049BB133111EB)
(def ^:const MASK64 0xFFFFFFFFFFFFFFFF)

(defn splitmix64-next
  "Generate next SplitMix64 state and output."
  [state]
  (let [state' (bit-and (+ state GOLDEN) MASK64)
        z state'
        z (bit-and (* (bit-xor z (bit-shift-right z 30)) MIX1) MASK64)
        z (bit-and (* (bit-xor z (bit-shift-right z 27)) MIX2) MASK64)]
    [state' (bit-xor z (bit-shift-right z 31))]))

(defn color-at
  "Generate OkLCH color at index from seed."
  [seed index]
  (loop [state (bit-and seed MASK64)
         i 0]
    (let [[state' z] (splitmix64-next state)]
      (if (= i index)
        (let [[s1 z1] (splitmix64-next state')
              [s2 z2] (splitmix64-next s1)
              [_ z3] (splitmix64-next s2)
              L (+ 10 (* (/ z1 (double MASK64)) 85))
              C (* (/ z2 (double MASK64)) 100)
              H (* (/ z3 (double MASK64)) 360)]
          {:L L :C C :H H :index index})
        (recur state' (inc i))))))

;; ═══════════════════════════════════════════════════════════════════════════
;; GF(3) Trit Operations
;; ═══════════════════════════════════════════════════════════════════════════

(defn trit-from-hue
  "Map hue angle to GF(3) trit."
  [H]
  (cond
    (or (< H 60) (>= H 300)) 1    ; PLUS (warm)
    (< H 180) 0                    ; ERGODIC (green/cyan)
    :else -1))                     ; MINUS (cool)

(defn gf3-sum
  "Compute sum of trits."
  [trits]
  (reduce + 0 trits))

(defn gf3-balanced?
  "Check if trits sum to 0 (mod 3)."
  [trits]
  (zero? (mod (gf3-sum trits) 3)))

;; ═══════════════════════════════════════════════════════════════════════════
;; ACSet Schema Definition (S-expression format)
;; ═══════════════════════════════════════════════════════════════════════════

(defn make-schema
  "Create an ACSet schema from specification."
  [name objects morphisms & [attributes]]
  {:type :acset-schema
   :name name
   :objects (vec objects)
   :morphisms (into {} morphisms)
   :attributes (into {} (or attributes {}))})

(def skill-invocation-schema
  "Standard schema for skill invocations."
  (make-schema
   "SkillInvocationACSet"
   [:Skill :Session :Invocation :Role]
   {:skill {:dom :Invocation :cod :Skill}
    :session {:dom :Invocation :cod :Session}
    :role {:dom :Skill :cod :Role}}
   {:skill_name {:dom :Skill :cod :String}
    :trit {:dom :Role :cod :Int}
    :gf3_role {:dom :Role :cod :String}}))

;; ═══════════════════════════════════════════════════════════════════════════
;; S-expression Serialization (ppx_sexp_conv style)
;; ═══════════════════════════════════════════════════════════════════════════

(defn sexp-of-schema
  "Convert schema to S-expression string."
  [schema]
  (pr-str
   (list 'acset-schema
         :name (:name schema)
         :objects (:objects schema)
         :morphisms (:morphisms schema)
         :attributes (:attributes schema))))

(defn schema-of-sexp
  "Parse S-expression string to schema."
  [sexp-str]
  (let [form (edn/read-string sexp-str)]
    (when (and (list? form) (= 'acset-schema (first form)))
      (let [kv-pairs (partition 2 (rest form))]
        (into {:type :acset-schema}
              (map (fn [[k v]] [(keyword (name k)) v]) kv-pairs))))))

(defn sexp-of-acset
  "Convert ACSet instance to colored S-expression."
  [acset seed]
  (let [color (color-at seed 0)
        trit (trit-from-hue (:H color))]
    (pr-str
     (list 'acset
           :schema (:schema acset)
           :color {:L (:L color) :C (:C color) :H (:H color)}
           :trit trit
           :parts (:parts acset)))))

;; ═══════════════════════════════════════════════════════════════════════════
;; Catlab JSON Export (Julia interop)
;; ═══════════════════════════════════════════════════════════════════════════

(defn to-catlab-json
  "Export schema to Catlab-compatible JSON."
  [schema]
  (json/generate-string
   {:_type (:name schema)
    :objects (mapv name (:objects schema))
    :homs (mapv (fn [[k v]]
                  {:name (name k)
                   :dom (name (:dom v))
                   :cod (name (:cod v))})
                (:morphisms schema))
    :attrs (mapv (fn [[k v]]
                   {:name (name k)
                    :dom (name (:dom v))
                    :type (name (:cod v))})
                 (:attributes schema))}
   {:pretty true}))

(defn from-catlab-json
  "Import schema from Catlab JSON."
  [json-str]
  (let [data (json/parse-string json-str true)]
    (make-schema
     (:_type data)
     (mapv keyword (:objects data))
     (into {} (map (fn [h]
                     [(keyword (:name h))
                      {:dom (keyword (:dom h))
                       :cod (keyword (:cod h))}])
                   (:homs data)))
     (into {} (map (fn [a]
                     [(keyword (:name a))
                      {:dom (keyword (:dom a))
                       :cod (keyword (:type a))}])
                   (:attrs data))))))

;; ═══════════════════════════════════════════════════════════════════════════
;; py-acset Export (Python/Hylang interop)
;; ═══════════════════════════════════════════════════════════════════════════

(defn to-pyacset-dict
  "Export to py-acset compatible Python dict format."
  [schema]
  (json/generate-string
   {"schema_name" (:name schema)
    "objects" (mapv name (:objects schema))
    "morphisms" (into {}
                      (map (fn [[k v]]
                             [(name k)
                              {"dom" (name (:dom v))
                               "cod" (name (:cod v))}])
                           (:morphisms schema)))
    "attributes" (into {}
                       (map (fn [[k v]]
                              [(name k)
                               {"dom" (name (:dom v))
                                "type" (name (:cod v))}])
                            (:attributes schema)))}
   {:pretty true}))

(defn to-hy-sexp
  "Export to Hylang S-expression format."
  [schema]
  (str "(defacset " (:name schema) "\n"
       "  :objects " (pr-str (:objects schema)) "\n"
       "  :morphisms " (pr-str (:morphisms schema)) "\n"
       "  :attributes " (pr-str (:attributes schema)) ")"))

;; ═══════════════════════════════════════════════════════════════════════════
;; LispSyntax.jl Bridge
;; ═══════════════════════════════════════════════════════════════════════════

(defn to-lispsyntax-jl
  "Generate Julia code using LispSyntax.jl for ACSet schema."
  [schema]
  (str "# Generated from Babashka unified_acset_bridge\n"
       "using LispSyntax\n"
       "using Catlab, Catlab.CategoricalAlgebra\n\n"
       "@present Schema" (:name schema) "(FreeSchema) begin\n"
       (str/join "\n"
         (map (fn [obj] (str "    " (name obj) "::Ob")) (:objects schema)))
       "\n"
       (str/join "\n"
         (map (fn [[m spec]]
                (str "    " (name m) "::" (name (:dom spec)) "→" (name (:cod spec))))
              (:morphisms schema)))
       "\nend\n\n"
       "const " (:name schema) " = ACSetType(Schema" (:name schema) ")\n"))

;; ═══════════════════════════════════════════════════════════════════════════
;; Specter-style Navigation
;; ═══════════════════════════════════════════════════════════════════════════

(defn navigate
  "Navigate ACSet using path specification.
   
   Paths:
     [:object obj-name] → get all parts of object type
     [:morphism m from-id] → follow morphism from part
     [:preimage m to-id] → get preimage of morphism
     [:attribute a from-id] → get attribute value"
  [acset path]
  (let [[op & args] path
        parts (:parts acset)]
    (case op
      :object (get parts (first args))
      :morphism (let [[m from-id] args
                      m-data (get-in acset [:morphism-data m])]
                  (get m-data from-id))
      :preimage (let [[m to-id] args
                      m-data (get-in acset [:morphism-data m])]
                  (keep-indexed (fn [i v] (when (= v to-id) i)) m-data))
      :attribute (let [[a from-id] args
                       a-data (get-in acset [:attribute-data a])]
                   (get a-data from-id))
      nil)))

;; ═══════════════════════════════════════════════════════════════════════════
;; CLI
;; ═══════════════════════════════════════════════════════════════════════════

(defn -main [& args]
  (let [cmd (first args)]
    (case cmd
      "schema" (do
                 (println "=== Skill Invocation ACSet Schema ===\n")
                 (println "S-expression:")
                 (println (sexp-of-schema skill-invocation-schema))
                 (println "\nCatlab JSON:")
                 (println (to-catlab-json skill-invocation-schema))
                 (println "\npy-acset dict:")
                 (println (to-pyacset-dict skill-invocation-schema))
                 (println "\nHylang S-expression:")
                 (println (to-hy-sexp skill-invocation-schema))
                 (println "\nLispSyntax.jl:")
                 (println (to-lispsyntax-jl skill-invocation-schema)))
      
      "color" (let [seed (or (some-> (second args) parse-long) 0x42D)
                    index (or (some-> (nth args 2 nil) parse-long) 0)
                    color (color-at seed index)]
                (println (format "Seed: 0x%X  Index: %d" seed index))
                (println (format "L=%.2f C=%.2f H=%.2f" (:L color) (:C color) (:H color)))
                (println (format "Trit: %d" (trit-from-hue (:H color)))))
      
      "gf3" (let [trits (mapv parse-long (rest args))
                  sum (gf3-sum trits)
                  balanced (gf3-balanced? trits)]
              (println (format "Trits: %s" trits))
              (println (format "Sum: %d" sum))
              (println (format "Balanced (mod 3 = 0): %s" (if balanced "YES" "NO"))))
      
      (do
        (println "unified_acset_bridge.bb — Polyglot ACSet Bridge")
        (println)
        (println "Commands:")
        (println "  schema            Show schema in all formats")
        (println "  color [seed] [i]  Generate color at index (default seed=0x42D)")
        (println "  gf3 t1 t2 ...     Check GF(3) balance of trits")
        (println)
        (println "Supported formats:")
        (println "  - EDN (Clojure/Babashka)")
        (println "  - Catlab JSON (Julia/ACSets.jl)")
        (println "  - py-acset dict (Python/Hylang)")
        (println "  - LispSyntax.jl (Julia S-expressions)")))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
