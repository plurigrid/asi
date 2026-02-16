---
name: clojure
description: Clojure ecosystem = babashka + clj + lein + shadow-cljs. Based on "Clojure for the Brave and True".
version: 2.0.0
source: braveclojure.com
---

# clojure

Clojure ecosystem = babashka + clj + lein + shadow-cljs.

## Atomic Skills

| Skill | Startup | Domain |
|-------|---------|--------|
| babashka | 10ms | Scripting |
| clj | 2s | JVM REPL |
| lein | 3s | Build tool |
| shadow-cljs | 5s | ClojureScript |

## Quick Start

```bash
# Scripting (fast)
bb -e '(+ 1 2 3)'

# JVM (full)
clj -M -m myapp.core

# Web (ClojureScript)
npx shadow-cljs watch app
```

---

## Syntax Fundamentals (Brave and True Ch.3)

### Forms and Evaluation

All Clojure code is made of **forms** - valid expressions the reader can parse.

```clojure
;; Literals - evaluate to themselves
1                    ; => 1
"a string"           ; => "a string"
["a" "vector" "of" "strings"]

;; Operations - (operator operand1 operand2 ... operandN)
(+ 1 2 3)            ; => 6
(str "It was the panda " "in the library " "with a dust buster")
```

### Control Flow

```clojure
;; if - (if boolean-form then-form optional-else-form)
(if true
  "By Zeus's hammer!"
  "By Aquaman's trident!")
; => "By Zeus's hammer!"

;; do - wrap multiple forms
(if true
  (do (println "Success!")
      "By Zeus's hammer!")
  (do (println "Failure!")
      "By Aquaman's trident!"))

;; when - if + do without else
(when true
  (println "Success!")
  "abra cadabra")

;; nil and truthiness
(nil? nil)           ; => true
(if nil "truthy" "falsey")  ; => "falsey"
(if 0 "truthy" "falsey")    ; => "truthy" (only nil/false are falsey)

;; Equality
(= 1 1)              ; => true
(= nil nil)          ; => true
(= 1 2)              ; => false
```

### Binding with let

```clojure
;; let creates lexical bindings
(let [x 3]
  x)
; => 3

(let [x 3
      y (+ x 1)]
  (* x y))
; => 12

;; Destructuring in let
(let [[first-thing second-thing & rest] [1 2 3 4 5]]
  [first-thing second-thing rest])
; => [1 2 (3 4 5)]
```

---

## Data Structures (Brave and True Ch.3)

### Numbers, Strings, Keywords

```clojure
;; Numbers
93        ; integer
1.2       ; float
1/5       ; ratio (exact)

;; Strings (double quotes only)
"Lord Voldemort"
(str "clojure" " for " "the brave")  ; concatenation

;; Keywords - primarily for map keys
:a :rumplestiltskin :34
(:a {:a 1 :b 2 :c 3})  ; => 1 (keywords as functions)
```

### Maps

```clojure
;; Empty map
{}

;; Literal syntax
{:first-name "Charlie" :last-name "McFishwich"}

;; Nested maps
{:name {:first "John" :middle "Jacob" :last "Jingleheimerschmidt"}}

;; hash-map function
(hash-map :a 1 :b 2)  ; => {:a 1 :b 2}

;; get values
(get {:a 0 :b 1} :b)           ; => 1
(get {:a 0 :b 1} :c)           ; => nil
(get {:a 0 :b 1} :c "default") ; => "default"

;; get-in for nested access
(get-in {:a {:b "nested"}} [:a :b])  ; => "nested"
```

### Vectors

```clojure
;; Literal
[3 2 1]

;; Heterogeneous
[3 "two" :one]

;; Access by index
(get [3 2 1] 0)      ; => 3

;; conj adds to END
(conj [1 2 3] 4)     ; => [1 2 3 4]

;; vector function
(vector "creepy" "full" "moon")  ; => ["creepy" "full" "moon"]
```

### Lists

```clojure
;; Must quote literal lists (prevent evaluation)
'(1 2 3 4)

;; list function
(list 1 "two" {3 4})  ; => (1 "two" {3 4})

;; nth for access (linear time!)
(nth '(:a :b :c) 0)   ; => :a

;; conj adds to BEGINNING
(conj '(1 2 3) 4)     ; => (4 1 2 3)
```

### Sets

```clojure
;; Literal
#{"kurt vonnegut" 20 :icicle}

;; hash-set function
(hash-set 1 1 2 2)    ; => #{1 2}

;; set membership
(contains? #{:a :b} :a)   ; => true
(contains? #{:a :b} 3)    ; => false
(:a #{:a :b})             ; => :a (keyword as function)

;; get returns value or nil
(get #{:a :b} :a)         ; => :a
(get #{:a nil} nil)       ; => nil (ambiguous!)
```

---

## Functions (Brave and True Ch.3)

### Calling Functions

```clojure
;; Basic calls
(+ 1 2 3 4)
(* 1 2 3 4)
(first [1 2 3 4])

;; Functions can be expressions
((or + -) 1 2 3)     ; => 6 (or returns first truthy, which is +)

;; Higher-order functions
(inc 1.1)            ; => 2.1
(map inc [0 1 2 3])  ; => (1 2 3 4)
```

### Defining Functions

```clojure
;; Basic defn
(defn too-enthusiastic
  "Return a cheer for your name"  ; docstring
  [name]                           ; parameters
  (str "OH. MY. GOD! " name " YOU ARE GREAT!"))

;; Multi-arity
(defn multi-arity
  ([a b c] (+ a b c))
  ([a b] (+ a b))
  ([a] (+ a 10)))

;; Rest parameters
(defn codger
  [& whippersnappers]
  (map (fn [name] (str "Get off my lawn, " name "!"))
       whippersnappers))

(codger "Billy" "Anne-Marie" "The Alarm Clock")

;; Destructuring in parameters
(defn chooser
  [[first-choice second-choice & unimportant-choices]]
  (println (str "First: " first-choice))
  (println (str "Second: " second-choice))
  (println (str "Rest: " (clojure.string/join ", " unimportant-choices))))

;; Map destructuring
(defn announce-treasure-location
  [{lat :lat lng :lng}]
  (println (str "Treasure lat: " lat))
  (println (str "Treasure lng: " lng)))

;; With :keys shorthand
(defn announce-treasure-location
  [{:keys [lat lng]}]
  (println (str "Treasure lat: " lat))
  (println (str "Treasure lng: " lng)))

;; With :as to retain original
(defn receive-map
  [{:keys [lat lng] :as treasure-location}]
  (println (str "Lat: " lat))
  (println (str "Lng: " lng))
  treasure-location)  ; return original map
```

### Anonymous Functions

```clojure
;; fn form
(fn [param-list] function-body)

(map (fn [name] (str "Hi, " name)) ["Darth Vader" "Mr. Magoo"])
; => ("Hi, Darth Vader" "Hi, Mr. Magoo")

;; Reader macro #()
#(* % 3)             ; single arg
#(* %1 %2)           ; multiple args
#(identity %&)       ; rest args

(map #(str "Hi, " %) ["Darth Vader" "Mr. Magoo"])
```

### Returning Functions (Closures)

```clojure
(defn inc-maker
  "Create a custom incrementer"
  [inc-by]
  #(+ % inc-by))     ; captures inc-by

(def inc3 (inc-maker 3))
(inc3 7)             ; => 10
```

---

## Core Functions in Depth (Brave and True Ch.4)

### The Sequence Abstraction

All Clojure collections can be treated as sequences - a logical list of elements.

```clojure
;; map - transform each element
(map inc [1 2 3])           ; => (2 3 4)
(map str ["a" "b" "c"] ["A" "B" "C"])  ; => ("aA" "bB" "cC")

;; Multiple collections - stops at shortest
(map list [1 2] [3 4] [5 6 7])  ; => ((1 3 5) (2 4 6))
```

### Key Sequence Functions

```clojure
;; reduce - accumulate
(reduce + [1 2 3 4])         ; => 10
(reduce + 15 [1 2 3 4])      ; => 25 (with initial value)

;; Custom reduce
(reduce (fn [new-map [key val]]
          (assoc new-map key (inc val)))
        {}
        {:max 30 :min 10})
; => {:max 31 :min 11}

;; filter - keep matching elements
(filter #(> (:human-blood-volume %) 0)
        [{:name "Edward" :human-blood-volume 0}
         {:name "Bella" :human-blood-volume 4.7}])

;; some - find first truthy
(some #(> (:critter-hierarchies %) 3)
      [{:critter-hierarchies 2} {:critter-hierarchies 4}])
; => true

;; take and drop
(take 3 [1 2 3 4 5])         ; => (1 2 3)
(drop 3 [1 2 3 4 5])         ; => (4 5)

;; take-while and drop-while
(take-while #(< % 3) [1 2 3 4])  ; => (1 2)
(drop-while #(< % 3) [1 2 3 4])  ; => (3 4)

;; sort and sort-by
(sort [3 1 2])               ; => (1 2 3)
(sort-by count ["aaa" "c" "bb"])  ; => ("c" "bb" "aaa")

;; concat
(concat [1 2] [3 4])         ; => (1 2 3 4)
```

### Lazy Sequences

```clojure
;; Lazy evaluation - elements computed on demand
(def vampire-db
  [{:makes-blood-puns? false :has-pulse? true :name "McFishwich"}
   {:makes-blood-puns? true :has-pulse? false :name "Dracula"}])

(defn vampire?
  [record]
  (and (:makes-blood-puns? record)
       (not (:has-pulse? record))))

;; Lazy - stops at first match
(first (filter vampire? vampire-db))

;; repeat and repeatedly for infinite seqs
(take 3 (repeat "na"))       ; => ("na" "na" "na")
(take 3 (repeatedly (fn [] (rand-int 10))))
```

### Collection Functions

```clojure
;; into - pour elements into collection
(into {} [[:a 1] [:b 2]])    ; => {:a 1 :b 2}
(into [] #{1 2 3})           ; => [1 2 3]
(into {:a 1} {:b 2 :c 3})    ; => {:a 1 :b 2 :c 3}

;; conj - add elements
(conj [0] 1 2 3)             ; => [0 1 2 3]
(conj {:a 1} [:b 2] [:c 3])  ; => {:a 1 :b 2 :c 3}
```

### Function Functions

```clojure
;; apply - explode collection into args
(max 0 1 2)                  ; => 2
(max [0 1 2])                ; => [0 1 2] (wrong!)
(apply max [0 1 2])          ; => 2

;; partial - fix some arguments
(def add10 (partial + 10))
(add10 3)                    ; => 13
(add10 5 7)                  ; => 22

;; complement - negate predicate
(def not-empty? (complement empty?))
(not-empty? [])              ; => false
(not-empty? [1])             ; => true
```

---

## Functional Programming (Brave and True Ch.5)

### Pure Functions

A pure function:
1. Always returns same result for same arguments (referential transparency)
2. Has no side effects

```clojure
;; Pure - depends only on input
(defn wisdom [words]
  (str words ", Daniel-san"))

;; Impure - depends on external state
(defn year-end-evaluation []
  (if (> (rand) 0.5)
    "You get a raise!"
    "Better luck next year!"))
```

### Immutability

```clojure
;; Data structures never change
(def great-baby-name "Rosanthony")
great-baby-name              ; => "Rosanthony"

;; "Changing" creates new value
(let [name "Choco"
      new-name (str name " - the crunchy one")]
  new-name)
; => "Choco - the crunchy one"

;; Original unchanged
(def original [1 2 3])
(def changed (conj original 4))
original                     ; => [1 2 3]
changed                      ; => [1 2 3 4]
```

### Recursion

```clojure
;; Basic recursion
(defn sum
  ([vals] (sum vals 0))
  ([vals acc]
   (if (empty? vals)
     acc
     (sum (rest vals) (+ acc (first vals))))))

;; recur for tail-call optimization
(defn sum-recur
  ([vals] (sum-recur vals 0))
  ([vals acc]
   (if (empty? vals)
     acc
     (recur (rest vals) (+ acc (first vals))))))
```

### Function Composition

```clojure
;; comp - compose functions (right to left)
((comp inc *) 2 3)           ; => 7  ; (* 2 3) then inc

(def character
  {:name "Smooches McCutes"
   :attributes {:intelligence 10 :strength 4 :dexterity 5}})

(def c-int (comp :intelligence :attributes))
(c-int character)            ; => 10

;; More complex composition
(defn spell-slots [char]
  (int (inc (/ (c-int char) 2))))

(spell-slots character)      ; => 6

;; memoize - cache pure function results
(def memo-sleepy-identity (memoize sleepy-identity))
(memo-sleepy-identity "Mr. Fantastico")  ; 1 second
(memo-sleepy-identity "Mr. Fantastico")  ; instant!
```

---

## Project Configuration

### deps.edn

```clojure
{:deps {org.clojure/clojure {:mvn/version "1.12.0"}}
 :aliases {:dev {:extra-paths ["dev"]}
           :test {:extra-deps {lambdaisland/kaocha {:mvn/version "1.0"}}}
           :nrepl {:extra-deps {nrepl/nrepl {:mvn/version "1.3.1"}
                                cider/cider-nrepl {:mvn/version "0.50.2"}}
                   :main-opts ["-m" "nrepl.cmdline"
                               "--port" "7888"
                               "--middleware" "[cider.nrepl/cider-middleware]"]}}}
```

### bb.edn

```clojure
{:tasks {:build (shell "clj -T:build uber")
         :test (shell "clj -M:test")
         :repl (clojure "-M:dev -m nrepl.cmdline")}}
```

---

## Scientific Skill Interleaving

This skill connects to the K-Dense-AI/claude-scientific-skills ecosystem:

### Graph Theory
- **networkx** [O] via bicomodule
  - Universal graph hub

### Bibliography References

- `general`: 734 citations in bib.duckdb

---

## SDF Interleaving

This skill connects to **Software Design for Flexibility** (Hanson & Sussman, 2021):

### Primary Chapter: 1. Flexibility through Abstraction

**Concepts**: combinators, compose, parallel-combine, spread-combine, arity

### GF(3) Balanced Triad

```
clojure (-) + SDF.Ch1 (+) + [balancer] (O) = 0
```

**Skill Trit**: -1 (MINUS - verification)


### Connection Pattern

Combinators compose operations. This skill provides composable abstractions.

---

## Cat# Integration

This skill maps to **Cat# = Comod(P)** as a bicomodule in the equipment structure:

```
Trit: 0 (ERGODIC)
Home: Prof
Poly Op: (x)
Kan Role: Adj
Color: #26D826
```

### GF(3) Naturality

The skill participates in triads satisfying:
```
(-1) + (0) + (+1) = 0 (mod 3)
```

This ensures compositional coherence in the Cat# equipment structure.
