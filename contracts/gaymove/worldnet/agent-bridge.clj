#!/usr/bin/env bb
;; Agent-O-Rama → Worldnet Bridge
;; Wires 26 worlds to the worldnet ledger for claim minting
;;
;; Usage:
;;   bb agent-bridge.clj artifact <world> <artifact-hash> [delta]
;;   bb agent-bridge.clj verify <world> <artifact-hash>
;;   bb agent-bridge.clj canon <world> <artifact-hash>
;;   bb agent-bridge.clj status

(require '[babashka.process :refer [shell]])
(require '[clojure.string :as str])

(def decay-script (str (System/getProperty "user.home") "/.topos/GayMove/worldnet/decay.clj"))

;; 26 worlds with GF(3) role assignments
;; Cycle: PLUS → ERGODIC → MINUS → PLUS ...
;; Conservation: every 3 consecutive worlds sum to 0
(def world-roles
  {"a" {:role "PLUS"    :trit  1 :wallet "0x8699edc0960dd5b916074f1e9bd25d86fb416a8decfa46f78ab0af6eaebe9d7a"}
   "b" {:role "ERGODIC" :trit  0 :wallet nil}
   "c" {:role "MINUS"   :trit -1 :wallet nil}
   "d" {:role "PLUS"    :trit  1 :wallet nil}
   "e" {:role "ERGODIC" :trit  0 :wallet nil}
   "f" {:role "MINUS"   :trit -1 :wallet nil}
   "g" {:role "PLUS"    :trit  1 :wallet nil}
   "h" {:role "ERGODIC" :trit  0 :wallet nil}
   "i" {:role "MINUS"   :trit -1 :wallet nil}
   "j" {:role "PLUS"    :trit  1 :wallet nil}
   "k" {:role "ERGODIC" :trit  0 :wallet nil}
   "l" {:role "MINUS"   :trit -1 :wallet nil}
   "m" {:role "PLUS"    :trit  1 :wallet nil}
   "n" {:role "ERGODIC" :trit  0 :wallet nil}
   "o" {:role "MINUS"   :trit -1 :wallet nil}
   "p" {:role "PLUS"    :trit  1 :wallet nil}
   "q" {:role "ERGODIC" :trit  0 :wallet nil}
   "r" {:role "MINUS"   :trit -1 :wallet nil}
   "s" {:role "PLUS"    :trit  1 :wallet nil}
   "t" {:role "ERGODIC" :trit  0 :wallet nil}
   "u" {:role "MINUS"   :trit -1 :wallet nil}
   "v" {:role "PLUS"    :trit  1 :wallet nil}
   "w" {:role "ERGODIC" :trit  0 :wallet nil}
   "x" {:role "MINUS"   :trit -1 :wallet nil}
   "y" {:role "PLUS"    :trit  1 :wallet nil}
   "z" {:role "ERGODIC" :trit  0 :wallet nil}})

;; Reward amounts by action type
(def rewards
  {:artifact     1000.0   ;; PLUS: new hypothesis/traversal
   :verification 500.0    ;; MINUS: verified/reproduced
   :canon        300.0    ;; ERGODIC: canonicalized
   :falsification 750.0}) ;; MINUS: falsified (higher reward)

(defn mint! [agent-id role delta reason]
  (println (str "Minting " delta " claims to " agent-id " (" role ") for: " reason))
  (let [result (shell {:out :string :err :string}
                      "bb" decay-script "mint" agent-id role (str delta) reason)]
    (println (:out result))
    result))

(defn get-world-info [world]
  (get world-roles (str/lower-case world)))

;; ============================================================
;; ARTIFACT PRODUCTION (PLUS worlds)
;; ============================================================

(defn on-artifact!
  "PLUS agent produced a new artifact (hypothesis, traversal, exploration)"
  [world artifact-hash & [custom-delta]]
  (let [{:keys [role]} (get-world-info world)
        agent-id (str "world-" (str/lower-case world))
        delta (or custom-delta (:artifact rewards))]
    (if (= role "PLUS")
      (mint! agent-id role delta (str "artifact:" artifact-hash))
      (println (str "Warning: " world " is " role ", not PLUS. PLUS worlds should produce artifacts.")))))

;; ============================================================
;; VERIFICATION (MINUS worlds)
;; ============================================================

(defn on-verify!
  "MINUS agent verified/reproduced an artifact"
  [world artifact-hash]
  (let [{:keys [role]} (get-world-info world)
        agent-id (str "world-" (str/lower-case world))]
    (if (= role "MINUS")
      (mint! agent-id role (:verification rewards) (str "verification:" artifact-hash))
      (println (str "Warning: " world " is " role ", not MINUS. MINUS worlds should verify.")))))

(defn on-falsify!
  "MINUS agent falsified an artifact (higher reward)"
  [world artifact-hash]
  (let [{:keys [role]} (get-world-info world)
        agent-id (str "world-" (str/lower-case world))]
    (if (= role "MINUS")
      (mint! agent-id role (:falsification rewards) (str "falsification:" artifact-hash))
      (println (str "Warning: " world " is " role ", not MINUS.")))))

;; ============================================================
;; CANONICALIZATION (ERGODIC worlds)
;; ============================================================

(defn on-canon!
  "ERGODIC agent canonicalized an artifact"
  [world artifact-hash]
  (let [{:keys [role]} (get-world-info world)
        agent-id (str "world-" (str/lower-case world))]
    (if (= role "ERGODIC")
      (mint! agent-id role (:canon rewards) (str "canon:" artifact-hash))
      (println (str "Warning: " world " is " role ", not ERGODIC. ERGODIC worlds should canonicalize.")))))

;; ============================================================
;; TRIADIC WORKFLOW
;; ============================================================

(defn triadic-cycle!
  "Run a full PLUS → MINUS → ERGODIC cycle for an artifact.
   Example: (triadic-cycle! \"a\" \"c\" \"b\" \"artifact-hash-123\")"
  [plus-world minus-world ergodic-world artifact-hash]
  (println "=== Triadic Cycle ===")
  (println (str "Artifact: " artifact-hash))

  ;; 1. PLUS generates
  (on-artifact! plus-world artifact-hash)

  ;; 2. MINUS verifies
  (on-verify! minus-world artifact-hash)

  ;; 3. ERGODIC canonicalizes
  (on-canon! ergodic-world artifact-hash)

  ;; Verify GF(3) conservation
  (let [plus-trit (get-in world-roles [(str/lower-case plus-world) :trit])
        minus-trit (get-in world-roles [(str/lower-case minus-world) :trit])
        ergodic-trit (get-in world-roles [(str/lower-case ergodic-world) :trit])
        sum (+ plus-trit minus-trit ergodic-trit)]
    (println (str "GF(3) sum: " plus-trit " + " minus-trit " + " ergodic-trit " = " sum))
    (if (zero? (mod sum 3))
      (println "✓ GF(3) conservation verified")
      (println "⚠ GF(3) violation!"))))

;; ============================================================
;; STATUS
;; ============================================================

(defn show-world-roles []
  (println "\n=== World Role Assignments ===")
  (println "World | Role    | Trit")
  (println "------+---------+-----")
  (doseq [[w {:keys [role trit]}] (sort world-roles)]
    (println (format "  %s   | %-7s | %+d" (str/upper-case w) role trit)))

  (println "\n=== Role Counts ===")
  (let [counts (->> (vals world-roles)
                    (map :role)
                    (frequencies))]
    (doseq [[role cnt] (sort counts)]
      (println (str role ": " cnt " worlds"))))

  (println "\n=== GF(3) Triads (example) ===")
  (println "A(+1) + B(0) + C(-1) = 0 ✓")
  (println "D(+1) + E(0) + F(-1) = 0 ✓")
  (println "..."))

;; ============================================================
;; CLI
;; ============================================================

(defn -main [& args]
  (let [[cmd world artifact-hash delta] args]
    (case cmd
      "artifact" (on-artifact! world artifact-hash (when delta (parse-double delta)))
      "verify"   (on-verify! world artifact-hash)
      "falsify"  (on-falsify! world artifact-hash)
      "canon"    (on-canon! world artifact-hash)
      "triadic"  (let [[_ plus minus ergodic hash] args]
                   (triadic-cycle! plus minus ergodic hash))
      "status"   (show-world-roles)
      "roles"    (show-world-roles)

      ;; Default: show help
      (do
        (println "Agent-O-Rama → Worldnet Bridge")
        (println "==============================")
        (println)
        (println "Commands:")
        (println "  artifact <world> <hash> [delta]  - PLUS world produced artifact")
        (println "  verify <world> <hash>            - MINUS world verified artifact")
        (println "  falsify <world> <hash>           - MINUS world falsified artifact")
        (println "  canon <world> <hash>             - ERGODIC world canonicalized")
        (println "  triadic <plus> <minus> <ergodic> <hash> - Full cycle")
        (println "  status                           - Show world roles")
        (println)
        (println "Examples:")
        (println "  bb agent-bridge.clj artifact A abc123")
        (println "  bb agent-bridge.clj verify C abc123")
        (println "  bb agent-bridge.clj canon B abc123")
        (println "  bb agent-bridge.clj triadic A C B abc123")))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
