#!/usr/bin/env bb
;;; preserves_acset_bridge.bb — Preserves-based Polyglot ACSet Bridge
;;;
;;; Uses Preserves (preserves.dev) as the canonical interchange format for ACSets.
;;; Preserves provides:
;;;   - Richer types than JSON (symbols, sets, records, embedded values)
;;;   - Syrup binary encoding for CapTP wire protocol
;;;   - Annotations for metadata without changing semantics
;;;   - Record syntax <Label field1 field2> perfect for ACSet schemas
;;;
;;; Bridges:
;;;   - Babashka/Clojure (EDN subset)
;;;   - Julia/ACSets.jl (Catlab)
;;;   - Hylang/Python (py-acset)
;;;   - CapTP/Syrup (OCapN wire format)
;;;
;;; Schema in Preserves:
;;;   <acset-schema "Name" [objects...] {morphisms...} {attributes...}>

(ns preserves-acset-bridge
  (:require [babashka.fs :as fs]
            [cheshire.core :as json]
            [clojure.string :as str]))

;; ═══════════════════════════════════════════════════════════════════════════
;; Preserves Text Syntax Generator
;; ═══════════════════════════════════════════════════════════════════════════

(declare to-preserves)

(defn preserves-symbol
  "Format a Clojure keyword/symbol as Preserves symbol."
  [x]
  (let [s (name x)]
    (if (re-matches #"^[a-zA-Z_][a-zA-Z0-9_-]*$" s)
      s
      (str "'" s "'"))))

(defn preserves-string
  "Format string with Preserves escaping."
  [s]
  (str "\""
       (-> s
           (str/replace "\\" "\\\\")
           (str/replace "\"" "\\\"")
           (str/replace "\n" "\\n")
           (str/replace "\t" "\\t"))
       "\""))

(defn preserves-record
  "Format a Preserves record: <label field1 field2 ...>"
  [label & fields]
  (str "<" (preserves-symbol label) " "
       (str/join " " (map to-preserves fields))
       ">"))

(defn preserves-sequence
  "Format a Preserves sequence: [v1, v2, ...]"
  [xs]
  (str "[" (str/join ", " (map to-preserves xs)) "]"))

(defn preserves-set
  "Format a Preserves set: #{v1, v2, ...}"
  [xs]
  (str "#{" (str/join ", " (map to-preserves xs)) "}"))

(defn preserves-dict
  "Format a Preserves dictionary: {k1: v1, k2: v2, ...}"
  [m]
  (str "{"
       (str/join ", "
         (map (fn [[k v]]
                (str (to-preserves k) ": " (to-preserves v)))
              m))
       "}"))

(defn preserves-annotate
  "Add annotation to value: @annotation value"
  [annotation value]
  (str "@" (to-preserves annotation) " " (to-preserves value)))

(defn preserves-embed
  "Embed a value (for CapTP references): #:value"
  [value]
  (str "#:" (to-preserves value)))

(defn to-preserves
  "Convert Clojure value to Preserves text syntax."
  [x]
  (cond
    (nil? x) "#f"  ; Use false for nil
    (true? x) "#t"
    (false? x) "#f"
    (keyword? x) (preserves-symbol x)
    (symbol? x) (preserves-symbol x)
    (string? x) (preserves-string x)
    (integer? x) (str x)
    (float? x) (str x)
    (vector? x) (preserves-sequence x)
    (set? x) (preserves-set x)
    (map? x) (preserves-dict x)
    (sequential? x) (preserves-sequence (vec x))
    :else (preserves-string (str x))))

;; ═══════════════════════════════════════════════════════════════════════════
;; Syrup Binary Encoding (subset for CapTP compatibility)
;; ═══════════════════════════════════════════════════════════════════════════

(declare to-syrup)

(defn varint-encode
  "Encode integer as varint (7 bits per byte, MSB continuation)."
  [n]
  (loop [n n
         bytes []]
    (if (< n 128)
      (conj bytes (byte n))
      (recur (bit-shift-right n 7)
             (conj bytes (byte (bit-or 0x80 (bit-and n 0x7F))))))))

(defn syrup-string
  "Encode string in Syrup: length:content"
  [s]
  (let [bytes (.getBytes s "UTF-8")]
    (str (count bytes) ":" s)))

(defn syrup-symbol
  "Encode symbol in Syrup: length'content"
  [sym]
  (let [s (name sym)]
    (str (count s) "'" s)))

(defn syrup-list
  "Encode list in Syrup: (elements)"
  [xs]
  (str "(" (str/join "" (map to-syrup xs)) ")"))

(defn syrup-dict
  "Encode dict in Syrup: {key value pairs}"
  [m]
  (str "{"
       (str/join ""
         (mapcat (fn [[k v]]
                   [(to-syrup k) (to-syrup v)])
                 m))
       "}"))

(defn syrup-record
  "Encode record in Syrup: <label fields>"
  [label & fields]
  (str "<" (to-syrup label) (str/join "" (map to-syrup fields)) ">"))

(defn to-syrup
  "Convert Clojure value to Syrup text encoding."
  [x]
  (cond
    (nil? x) "f"
    (true? x) "t"
    (false? x) "f"
    (keyword? x) (syrup-symbol x)
    (symbol? x) (syrup-symbol x)
    (string? x) (syrup-string x)
    (integer? x) (if (neg? x)
                   (str (- (count (str (- x)))) "-" (- x))
                   (str (count (str x)) "+" x))
    (float? x) (str "D" x ";")
    (vector? x) (syrup-list x)
    (set? x) (str "#" (syrup-list (vec x)))
    (map? x) (syrup-dict x)
    (sequential? x) (syrup-list (vec x))
    :else (syrup-string (str x))))

;; ═══════════════════════════════════════════════════════════════════════════
;; GF(3) Trit Operations (with Preserves annotations)
;; ═══════════════════════════════════════════════════════════════════════════

(def ^:const GOLDEN 0x9E3779B97F4A7C15)
(def ^:const MASK64 0xFFFFFFFFFFFFFFFF)
(def ^:const MIX1 0xBF58476D1CE4E5B9)
(def ^:const MIX2 0x94D049BB133111EB)

(defn splitmix64-next [state]
  (let [state' (bit-and (+ state GOLDEN) MASK64)
        z state'
        z (bit-and (* (bit-xor z (unsigned-bit-shift-right z 30)) MIX1) MASK64)
        z (bit-and (* (bit-xor z (unsigned-bit-shift-right z 27)) MIX2) MASK64)]
    [state' (bit-xor z (unsigned-bit-shift-right z 31))]))

(defn color-at [seed index]
  (loop [state (bit-and seed MASK64), i 0]
    (let [[state' _] (splitmix64-next state)]
      (if (= i index)
        (let [[s1 z1] (splitmix64-next state')
              [s2 z2] (splitmix64-next s1)
              [_ z3] (splitmix64-next s2)]
          {:L (+ 10 (* (/ (double z1) (double MASK64)) 85))
           :C (* (/ (double z2) (double MASK64)) 100)
           :H (* (/ (double z3) (double MASK64)) 360)
           :index index})
        (recur state' (inc i))))))

(defn trit-from-hue [H]
  (cond (or (< H 60) (>= H 300)) 1
        (< H 180) 0
        :else -1))

(defn gf3-balanced? [trits]
  (zero? (mod (reduce + 0 trits) 3)))

;; ═══════════════════════════════════════════════════════════════════════════
;; ACSet Schema in Preserves
;; ═══════════════════════════════════════════════════════════════════════════

(defn make-schema
  "Create ACSet schema as Preserves-compatible structure."
  [name objects morphisms & [attributes]]
  {:_preserves_type :acset-schema
   :name name
   :objects (vec objects)
   :morphisms (into {} morphisms)
   :attributes (into {} (or attributes {}))})

(defn schema->preserves
  "Convert schema to Preserves record syntax."
  [schema]
  (str "<acset-schema "
       (preserves-string (:name schema)) " "
       (preserves-sequence (map preserves-symbol (:objects schema))) " "
       (preserves-dict
         (into {}
           (map (fn [[k v]]
                  [k {:dom (:dom v) :cod (:cod v)}])
                (:morphisms schema)))) " "
       (preserves-dict
         (into {}
           (map (fn [[k v]]
                  [k {:dom (:dom v) :type (:cod v)}])
                (:attributes schema))))
       ">"))

(defn schema->syrup
  "Convert schema to Syrup encoding."
  [schema]
  (str "<"
       (syrup-symbol :acset-schema)
       (syrup-string (:name schema))
       (syrup-list (map #(keyword %) (:objects schema)))
       (syrup-dict (:morphisms schema))
       (syrup-dict (:attributes schema))
       ">"))

;; ═══════════════════════════════════════════════════════════════════════════
;; Standard ACSet Schemas
;; ═══════════════════════════════════════════════════════════════════════════

(def skill-invocation-schema
  (make-schema
   "SkillInvocationACSet"
   [:Skill :Session :Invocation :Role]
   {:skill {:dom :Invocation :cod :Skill}
    :session {:dom :Invocation :cod :Session}
    :role {:dom :Skill :cod :Role}}
   {:skill_name {:dom :Skill :cod :String}
    :trit {:dom :Role :cod :Int}
    :gf3_role {:dom :Role :cod :Symbol}}))

(def colored-sexp-schema
  "Schema for colored S-expressions (term rewriting as graph rewriting)."
  (make-schema
   "ColoredSexpACSet"
   [:Term :Color :Trit]
   {:color {:dom :Term :cod :Color}
    :trit_of {:dom :Color :cod :Trit}
    :parent {:dom :Term :cod :Term}}
   {:sexp {:dom :Term :cod :String}
    :L {:dom :Color :cod :Float}
    :C {:dom :Color :cod :Float}
    :H {:dom :Color :cod :Float}
    :value {:dom :Trit :cod :Int}}))

;; ═══════════════════════════════════════════════════════════════════════════
;; ACSet Instance Operations
;; ═══════════════════════════════════════════════════════════════════════════

(defn make-acset
  "Create an ACSet instance."
  [schema]
  {:_preserves_type :acset
   :schema (:name schema)
   :parts (into {} (map (fn [obj] [obj []]) (:objects schema)))
   :morphisms (into {} (map (fn [[m _]] [m []]) (:morphisms schema)))
   :attributes (into {} (map (fn [[a _]] [a []]) (:attributes schema)))})

(defn add-part!
  "Add a part to an ACSet (returns new ACSet)."
  [acset obj-type & attrs]
  (let [idx (count (get-in acset [:parts obj-type]))]
    (-> acset
        (update-in [:parts obj-type] conj idx)
        (as-> a
          (reduce (fn [acc [k v]]
                    (update-in acc [:attributes k] conj v))
                  a
                  (partition 2 attrs))))))

(defn set-morphism!
  "Set morphism value for a part."
  [acset morphism from-idx to-idx]
  (update-in acset [:morphisms morphism]
             (fn [m]
               (let [m (vec m)]
                 (if (< from-idx (count m))
                   (assoc m from-idx to-idx)
                   (conj (vec (concat m (repeat (- from-idx (count m)) nil))) to-idx))))))

(defn acset->preserves
  "Convert ACSet instance to Preserves format."
  [acset seed]
  (let [color (color-at seed 0)
        trit (trit-from-hue (:H color))]
    (str "@<gf3 " trit " "
         (preserves-dict {:L (:L color) :C (:C color) :H (:H color)})
         "> "
         "<acset "
         (preserves-string (:schema acset)) " "
         (preserves-dict (:parts acset)) " "
         (preserves-dict (:morphisms acset)) " "
         (preserves-dict (:attributes acset))
         ">")))

;; ═══════════════════════════════════════════════════════════════════════════
;; CapTP Message Encoding
;; ═══════════════════════════════════════════════════════════════════════════

(defn captp-op-invoke
  "Create CapTP op:invoke message for skill invocation."
  [to-desc method-name args]
  (str "<op:invoke "
       (preserves-embed to-desc) " "
       (preserves-symbol method-name) " "
       (preserves-sequence args)
       ">"))

(defn captp-op-deliver
  "Create CapTP op:deliver message with result."
  [answer-pos result]
  (str "<op:deliver "
       (preserves-embed answer-pos) " "
       (to-preserves result)
       ">"))

(defn captp-op-listen
  "Create CapTP op:listen message for skill subscription."
  [to-desc listener-pos]
  (str "<op:listen "
       (preserves-embed to-desc) " "
       (preserves-embed listener-pos)
       ">"))

;; ═══════════════════════════════════════════════════════════════════════════
;; Export to Other Formats
;; ═══════════════════════════════════════════════════════════════════════════

(defn schema->catlab-json
  "Export to Julia/Catlab JSON format."
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

(defn schema->hy-sexp
  "Export to Hylang S-expression."
  [schema]
  (str "(defacset " (:name schema) "\n"
       "  :objects " (pr-str (:objects schema)) "\n"
       "  :morphisms " (pr-str (:morphisms schema)) "\n"
       "  :attributes " (pr-str (:attributes schema)) ")"))

;; ═══════════════════════════════════════════════════════════════════════════
;; CLI
;; ═══════════════════════════════════════════════════════════════════════════

;; ═══════════════════════════════════════════════════════════════════════════
;; EDN Export (Clojure native)
;; ═══════════════════════════════════════════════════════════════════════════

(defn schema->edn
  "Export schema to EDN (Clojure/Babashka native)."
  [schema]
  (pr-str
   {:_type :acset-schema
    :name (:name schema)
    :objects (:objects schema)
    :morphisms (:morphisms schema)
    :attributes (:attributes schema)}))

(defn acset->edn
  "Export ACSet instance to EDN with GF(3) metadata."
  [acset seed]
  (let [color (color-at seed 0)
        trit (trit-from-hue (:H color))]
    (pr-str
     (with-meta
       {:_type :acset
        :schema (:schema acset)
        :parts (:parts acset)
        :morphisms (:morphisms acset)
        :attributes (:attributes acset)}
       {:gf3/trit trit
        :gf3/color {:L (:L color) :C (:C color) :H (:H color)}
        :gf3/seed seed}))))

;; ═══════════════════════════════════════════════════════════════════════════
;; jq/cq Query Extensions for ACSet
;; ═══════════════════════════════════════════════════════════════════════════
;;
;; The ACSet bridges both:
;;   1. WIRE FORMAT: Syrup/Preserves binary encoding for CapTP messages
;;   2. AST FORMAT: Structured data for query/transformation
;;
;; Query patterns for jq (JSON) and cq (Clojure):
;;
;; === JQ QUERIES (on Catlab JSON export) ===
;;
;; # Get all objects
;; jq '.objects[]'
;;
;; # Get morphisms with specific codomain
;; jq '.homs[] | select(.cod == "Skill")'
;;
;; # Get morphism graph as DOT
;; jq -r '"digraph { " + ([.homs[] | "\(.dom) -> \(.cod) [label=\"\(.name)\"]"] | join("; ")) + " }"'
;;
;; # Filter by GF(3) trit (if in instance)
;; jq '.parts.Role[] | select(.trit == 1)'
;;
;; === CQ QUERIES (Clojure/Babashka on EDN) ===
;;
;; # Get all objects
;; (-> acset :objects)
;;
;; # Get morphisms into Skill
;; (->> (:morphisms acset) (filter #(= :Skill (:cod (val %)))))
;;
;; # Navigate forward: Invocation -> Skill
;; (get-in acset [:morphisms :skill :cod])
;;
;; # Navigate backward (preimage): Skill -> [Invocation]
;; (keep-indexed (fn [i v] (when (= skill-id v) i)) 
;;               (get-in acset [:morphism-data :skill]))
;;
;; # GF(3) balance check
;; (->> (:parts acset) :Role (map :trit) (reduce +) (#(zero? (mod % 3))))
;;

(def jq-acset-queries
  "Common jq query patterns for ACSet JSON."
  {"objects" ".objects[]"
   "morphisms" ".homs[]"
   "attributes" ".attrs[]"
   "morphism-graph" "\"digraph { \" + ([.homs[] | \"\\(.dom) -> \\(.cod) [label=\\\"\\(.name)\\\"]\"] | join(\"; \")) + \" }\""
   "find-by-cod" ".homs[] | select(.cod == $target)"
   "find-by-dom" ".homs[] | select(.dom == $target)"})

(defn generate-jq-module
  "Generate jq module for ACSet queries."
  []
  (str "# acset.jq - ACSet query module for jq\n"
       "# Usage: jq -L . 'import \"acset\" as a; a::morphisms'\n\n"
       "def objects: .objects[];\n"
       "def morphisms: .homs[];\n"
       "def attrs: .attrs[];\n"
       "def find_by_cod(target): .homs[] | select(.cod == target);\n"
       "def find_by_dom(target): .homs[] | select(.dom == target);\n"
       "def morphism_graph: \"digraph { \" + ([.homs[] | \"\\(.dom) -> \\(.cod) [label=\\\"\\(.name)\\\"]\"] | join(\"; \")) + \" }\";\n"
       "def gf3_sum: [.. | .trit? // empty] | add;\n"
       "def gf3_balanced: (gf3_sum % 3) == 0;\n"))

(defn generate-cq-ns
  "Generate Clojure namespace for ACSet queries (cq = Clojure query)."
  []
  (str ";; acset_query.clj - ACSet query functions for Babashka/Clojure\n"
       ";; Usage: (require '[acset-query :as aq])\n\n"
       "(ns acset-query)\n\n"
       "(defn objects [acset] (:objects acset))\n"
       "(defn morphisms [acset] (:morphisms acset))\n"
       "(defn attrs [acset] (:attributes acset))\n\n"
       "(defn find-by-cod [acset target]\n"
       "  (->> (:morphisms acset)\n"
       "       (filter #(= target (:cod (val %))))))\n\n"
       "(defn find-by-dom [acset target]\n"
       "  (->> (:morphisms acset)\n"
       "       (filter #(= target (:dom (val %))))))\n\n"
       "(defn navigate [acset from-obj morph-name]\n"
       "  (get-in acset [:morphisms morph-name :cod]))\n\n"
       "(defn preimage [acset morph-name to-id]\n"
       "  (keep-indexed (fn [i v] (when (= to-id v) i))\n"
       "                (get-in acset [:morphism-data morph-name])))\n\n"
       "(defn gf3-sum [acset]\n"
       "  (->> (get-in acset [:parts :Role])\n"
       "       (keep :trit)\n"
       "       (reduce + 0)))\n\n"
       "(defn gf3-balanced? [acset]\n"
       "  (zero? (mod (gf3-sum acset) 3)))\n\n"
       ";; Specter-style path navigation\n"
       "(defn path-navigate [acset & path]\n"
       "  (reduce (fn [acc step]\n"
       "            (cond\n"
       "              (keyword? step) (get acc step)\n"
       "              (vector? step) (get-in acc step)\n"
       "              (fn? step) (step acc)\n"
       "              :else acc))\n"
       "          acset path))\n"))

;; ═══════════════════════════════════════════════════════════════════════════
;; Dual-Mode ACSet: Wire + AST
;; ═══════════════════════════════════════════════════════════════════════════
;;
;; The ACSet serves two purposes:
;;
;; 1. WIRE FORMAT (CapTP/Syrup):
;;    - Compact binary encoding for network transmission
;;    - Canonical form for cryptographic hashing
;;    - Embedded references (#:ref) for capability passing
;;    - Records <op:invoke ...> for RPC messages
;;
;; 2. AST FORMAT (Preserves/EDN):
;;    - Structured representation for query/transform
;;    - Annotations (@metadata value) for GF(3) trits
;;    - Navigation via morphisms (forward) and preimages (backward)
;;    - Schema-aware validation
;;
;; Bridge functions convert between:
;;   Syrup (wire) <-> Preserves (interchange) <-> EDN (query) <-> JSON (export)
;;

(defn wire->ast
  "Convert wire format (Syrup) to AST format (EDN)."
  [syrup-str schema]
  ;; Parse Syrup and reconstruct as EDN
  ;; This is a simplified version - full parser would handle all Syrup types
  {:_type :acset
   :schema (:name schema)
   :_wire syrup-str
   :_format :syrup})

(defn ast->wire
  "Convert AST format (EDN) to wire format (Syrup)."
  [acset]
  (to-syrup acset))

(defn dual-encode
  "Encode ACSet in both wire and AST formats."
  [acset seed]
  {:wire (ast->wire acset)
   :ast (acset->edn acset seed)
   :preserves (acset->preserves acset seed)
   :json (json/generate-string acset {:pretty true})})

;; ═══════════════════════════════════════════════════════════════════════════
;; LazyFrame / Polars / Nushell Equivalences
;; ═══════════════════════════════════════════════════════════════════════════
;;
;; ACSet morphisms map naturally to relational/dataframe operations:
;;
;; | ACSet Concept      | Polars/LazyFrame    | Nushell              | DuckDB           |
;; |--------------------|---------------------|----------------------|------------------|
;; | Object (Ob)        | DataFrame           | table                | TABLE            |
;; | Morphism (Hom)     | join / select       | join                 | FOREIGN KEY      |
;; | Attribute (Attr)   | column              | column               | COLUMN           |
;; | Parts              | rows                | rows                 | rows             |
;; | Forward nav        | .join(right, on=)   | join --left          | JOIN ON          |
;; | Preimage (back)    | .filter(col == id)  | where col == id      | WHERE            |
;; | Schema             | Schema              | describe             | DESCRIBE         |
;; | Lazy eval          | LazyFrame.collect() | lazy evaluation      | EXPLAIN          |
;;
;; Key insight: ACSet bidirectional indices = Polars join + filter
;;
;; === NUSHELL EQUIVALENTS ===
;;
;; # Forward morphism: Invocation -> Skill
;; $acset.Invocation | join $acset.Skill skill_id id
;;
;; # Preimage: all Invocations for a Skill
;; $acset.Invocation | where skill_id == $skill_id
;;
;; # GF(3) balance check
;; $acset.Role | get trit | math sum | $in mod 3 == 0
;;
;; # Morphism graph
;; $schema.homs | each {|h| $"($h.dom) -> ($h.cod)"} | str join "\n"
;;
;; === POLARS EQUIVALENTS ===
;;
;; # Forward morphism
;; invocations.lazy().join(skills.lazy(), on="skill_id").collect()
;;
;; # Preimage  
;; invocations.lazy().filter(pl.col("skill_id") == skill_id).collect()
;;
;; # GF(3) balance
;; roles.select(pl.col("trit").sum() % 3 == 0)
;;

(defn generate-nushell-module
  "Generate Nushell module for ACSet operations."
  []
  (str "# acset.nu - ACSet operations for Nushell\n"
       "# Usage: use acset.nu *\n\n"
       "# Get objects from schema\n"
       "export def objects [schema] {\n"
       "  $schema.objects\n"
       "}\n\n"
       "# Get morphisms from schema\n"
       "export def morphisms [schema] {\n"
       "  $schema.homs\n"
       "}\n\n"
       "# Forward navigation via morphism\n"
       "export def navigate [acset: record, from_table: string, morph: string, to_table: string] {\n"
       "  $acset | get $from_table | join ($acset | get $to_table) $morph id\n"
       "}\n\n"
       "# Preimage query (backward navigation)\n"
       "export def preimage [acset: record, table: string, morph: string, target_id: int] {\n"
       "  $acset | get $table | where ($morph) == $target_id\n"
       "}\n\n"
       "# GF(3) sum of trits\n"
       "export def gf3-sum [table] {\n"
       "  $table | get trit | math sum\n"
       "}\n\n"
       "# Check GF(3) balance\n"
       "export def gf3-balanced [table] {\n"
       "  (gf3-sum $table) mod 3 == 0\n"
       "}\n\n"
       "# Convert schema to DOT graph\n"
       "export def to-dot [schema] {\n"
       "  let edges = ($schema.homs | each {|h| $\"  ($h.dom) -> ($h.cod) [label=\\\"($h.name)\\\"];\"})\n"
       "  $\"digraph ACSet {\\n($edges | str join \"\\n\")\\n}\"\n"
       "}\n\n"
       "# Lazy evaluation marker (for pipeline optimization)\n"
       "export def lazy [table] {\n"
       "  # Nushell pipelines are already lazy by default\n"
       "  # This is a semantic marker for ACSet operations\n"
       "  $table | describe | wrap _lazy_schema | merge $table\n"
       "}\n"))

(defn generate-polars-module
  "Generate Python/Polars module for ACSet operations."
  []
  (str "# acset_polars.py - ACSet operations for Polars LazyFrames\n"
       "# Usage: from acset_polars import ACSet\n\n"
       "import polars as pl\n"
       "from dataclasses import dataclass\n"
       "from typing import Dict, List, Any\n\n"
       "@dataclass\n"
       "class ACSetSchema:\n"
       "    \"\"\"ACSet schema with lazy evaluation support.\"\"\"\n"
       "    name: str\n"
       "    objects: List[str]\n"
       "    morphisms: Dict[str, dict]  # {name: {dom, cod}}\n"
       "    attributes: Dict[str, dict]  # {name: {dom, type}}\n\n"
       "class ACSet:\n"
       "    \"\"\"ACSet instance backed by Polars LazyFrames.\"\"\"\n"
       "    \n"
       "    def __init__(self, schema: ACSetSchema):\n"
       "        self.schema = schema\n"
       "        self._frames: Dict[str, pl.LazyFrame] = {}\n"
       "        self._morphism_data: Dict[str, pl.LazyFrame] = {}\n"
       "    \n"
       "    def add_parts(self, obj: str, df: pl.DataFrame) -> 'ACSet':\n"
       "        \"\"\"Add parts to an object as LazyFrame.\"\"\"\n"
       "        self._frames[obj] = df.lazy()\n"
       "        return self\n"
       "    \n"
       "    def navigate(self, morph: str) -> pl.LazyFrame:\n"
       "        \"\"\"Forward navigation via morphism (lazy join).\"\"\"\n"
       "        spec = self.schema.morphisms[morph]\n"
       "        dom, cod = spec['dom'], spec['cod']\n"
       "        return self._frames[dom].join(\n"
       "            self._frames[cod],\n"
       "            left_on=morph + '_id',\n"
       "            right_on='id'\n"
       "        )\n"
       "    \n"
       "    def preimage(self, morph: str, target_id: int) -> pl.LazyFrame:\n"
       "        \"\"\"Backward navigation (preimage query).\"\"\"\n"
       "        spec = self.schema.morphisms[morph]\n"
       "        dom = spec['dom']\n"
       "        return self._frames[dom].filter(\n"
       "            pl.col(morph + '_id') == target_id\n"
       "        )\n"
       "    \n"
       "    def gf3_sum(self) -> int:\n"
       "        \"\"\"Compute GF(3) sum of all trits.\"\"\"\n"
       "        if 'Role' not in self._frames:\n"
       "            return 0\n"
       "        return self._frames['Role'].select(\n"
       "            pl.col('trit').sum()\n"
       "        ).collect().item()\n"
       "    \n"
       "    def gf3_balanced(self) -> bool:\n"
       "        \"\"\"Check GF(3) conservation.\"\"\"\n"
       "        return self.gf3_sum() % 3 == 0\n"
       "    \n"
       "    def collect(self) -> Dict[str, pl.DataFrame]:\n"
       "        \"\"\"Collect all LazyFrames (execute pending operations).\"\"\"\n"
       "        return {k: v.collect() for k, v in self._frames.items()}\n"
       "    \n"
       "    def explain(self) -> Dict[str, str]:\n"
       "        \"\"\"Get query plans for all LazyFrames.\"\"\"\n"
       "        return {k: v.explain() for k, v in self._frames.items()}\n\n"
       "# GF(3) trit from hue angle\n"
       "def trit_from_hue(H: float) -> int:\n"
       "    if H < 60 or H >= 300:\n"
       "        return 1   # PLUS\n"
       "    elif H < 180:\n"
       "        return 0   # ERGODIC\n"
       "    else:\n"
       "        return -1  # MINUS\n"))

(defn generate-duckdb-views
  "Generate DuckDB views for ACSet schema."
  [schema]
  (let [name (:name schema)]
    (str "-- " name " ACSet views for DuckDB\n"
         "-- Usage: .read acset_views.sql\n\n"
         "-- Object tables\n"
         (str/join "\n"
           (map (fn [obj]
                  (str "CREATE TABLE IF NOT EXISTS " (name obj) " (\n"
                       "  id INTEGER PRIMARY KEY,\n"
                       "  -- Add attributes here\n"
                       ");"))
                (:objects schema)))
         "\n\n-- Morphism foreign keys (add to tables above)\n"
         (str/join "\n"
           (map (fn [[m spec]]
                  (str "-- " (name (:dom spec)) "." (name m) "_id REFERENCES " (name (:cod spec)) "(id)"))
                (:morphisms schema)))
         "\n\n-- Forward navigation view\n"
         "CREATE OR REPLACE VIEW morphism_graph AS\n"
         "SELECT\n"
         (str/join " UNION ALL\n"
           (map (fn [[m spec]]
                  (str "  SELECT '" (name m) "' as morphism, '"
                       (name (:dom spec)) "' as dom, '"
                       (name (:cod spec)) "' as cod"))
                (:morphisms schema)))
         ";\n\n"
         "-- GF(3) balance check\n"
         "CREATE OR REPLACE VIEW gf3_balance AS\n"
         "SELECT\n"
         "  SUM(trit) as trit_sum,\n"
         "  SUM(trit) % 3 = 0 as balanced\n"
         "FROM Role;\n")))

;; ═══════════════════════════════════════════════════════════════════════════
;; CLI
;; ═══════════════════════════════════════════════════════════════════════════

(defn -main [& args]
  (let [cmd (first args)]
    (case cmd
      "schema" (do
                 (println "=== Skill Invocation ACSet Schema ===\n")
                 (println "Preserves:")
                 (println (schema->preserves skill-invocation-schema))
                 (println "\nSyrup:")
                 (println (schema->syrup skill-invocation-schema))
                 (println "\nEDN:")
                 (println (schema->edn skill-invocation-schema))
                 (println "\nCatlab JSON:")
                 (println (schema->catlab-json skill-invocation-schema))
                 (println "\nHylang:")
                 (println (schema->hy-sexp skill-invocation-schema)))
      
      "colored" (do
                  (println "=== Colored S-expression ACSet Schema ===\n")
                  (println "Preserves:")
                  (println (schema->preserves colored-sexp-schema))
                  (println "\nSyrup:")
                  (println (schema->syrup colored-sexp-schema)))
      
      "captp" (let [skill (or (second args) "triad-interleave")]
                (println "=== CapTP Messages for Skill Invocation ===\n")
                (println "op:invoke:")
                (println (captp-op-invoke
                          {:type :sturdy-ref :oid skill}
                          :invoke
                          [{:seed 0x42D :n_triplets 5}]))
                (println "\nop:deliver:")
                (println (captp-op-deliver
                          {:answer-pos 1}
                          {:schedule-id "abc123" :gf3-conserved true}))
                (println "\nop:listen:")
                (println (captp-op-listen
                          {:type :sturdy-ref :oid skill}
                          {:listener-pos 2})))
      
      "color" (let [seed (or (some-> (second args) parse-long) 0x42D)
                    index (or (some-> (nth args 2 nil) parse-long) 0)
                    color (color-at seed index)
                    trit (trit-from-hue (:H color))]
                (println "Preserves annotation:")
                (println (str "@<gf3 " trit " "
                             (preserves-dict {:L (:L color) :C (:C color) :H (:H color)})
                             ">")))
      
      "jq" (do
             (println (generate-jq-module)))
      
      "cq" (do
             (println (generate-cq-ns)))
      
      "dual" (let [seed (or (some-> (second args) parse-long) 0x42D)]
               (println "=== Dual-Mode ACSet Encoding ===\n")
               (println "The ACSet bridges WIRE format (CapTP/Syrup) and AST format (EDN/Preserves).\n")
               (let [instance (make-acset skill-invocation-schema)
                     encoded (dual-encode instance seed)]
                 (println "WIRE (Syrup):")
                 (println (:wire encoded))
                 (println "\nAST (EDN):")
                 (println (:ast encoded))
                 (println "\nPreserves:")
                 (println (:preserves encoded))))
      
      "nushell" (do
                  (println (generate-nushell-module)))
      
      "polars" (do
                 (println (generate-polars-module)))
      
      "duckdb" (do
                 (println (generate-duckdb-views skill-invocation-schema)))
      
      (do
        (println "preserves_acset_bridge.bb — Preserves-based ACSet Bridge")
        (println "")
        (println "Uses Preserves (preserves.dev) as canonical interchange format.")
        (println "Compatible with CapTP/Syrup wire protocol.")
        (println "")
        (println "Commands:")
        (println "  schema          Show SkillInvocationACSet in all formats")
        (println "  colored         Show ColoredSexpACSet schema")
        (println "  captp [skill]   Generate CapTP messages for skill")
        (println "  color [seed] [i] Generate GF(3) color annotation")
        (println "  jq              Generate jq module for ACSet queries")
        (println "  cq              Generate Clojure query namespace")
        (println "  dual [seed]     Show dual-mode (wire+AST) encoding")
        (println "  nushell         Generate Nushell module (LazyFrame equiv)")
        (println "  polars          Generate Python/Polars module")
        (println "  duckdb          Generate DuckDB views")
        (println "")
        (println "Formats supported:")
        (println "  - Preserves text syntax (records, annotations)")
        (println "  - Syrup binary-compatible text encoding")
        (println "  - EDN (Clojure/Babashka native)")
        (println "  - Catlab JSON (Julia/ACSets.jl)")
        (println "  - Hylang S-expressions")
        (println "")
        (println "Wire vs AST:")
        (println "  WIRE: Syrup encoding for CapTP network messages")
        (println "  AST:  Preserves/EDN for jq/cq queries and transforms")))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
