#!/usr/bin/env bb
;; skill-semilattice.bb — Semilattice-based skill discovery for plurigrid/asi
;;
;; The Droid's trice applied to skill composition:
;;   Substrate: SplitMix64(skill-name) → deterministic seed → fiber
;;   Trit:      GF(3) conservation across triads (validator/coordinator/generator)
;;   Color:     OKLAB join = perceptual similarity metric for skill clustering
;;
;; Usage:
;;   bb skill-semilattice.bb fiber <skill-name>     — compute fiber for one skill
;;   bb skill-semilattice.bb join <skill-a> <skill-b> — join two skills
;;   bb skill-semilattice.bb triad <skill-a> <skill-b> — find the balancing third
;;   bb skill-semilattice.bb cluster <n>             — top-n clusters by fiber proximity
;;   bb skill-semilattice.bb conserved?              — verify global GF(3) = 0
;;   bb skill-semilattice.bb discover <query>        — find skills by fiber similarity

(require '[clojure.string :as str]
         '[clojure.java.io :as io]
         '[clojure.edn :as edn])

;; ─── SplitMix64 (mirrors substrate.zig exactly) ────────────────────
(def GOLDEN (unchecked-long 0x9e3779b97f4a7c15))
(def MIX1   (unchecked-long 0xbf58476d1ce4e5b9))
(def MIX2   (unchecked-long 0x94d049bb133111eb))

(defn mix64 [z]
  (let [z (long z)
        z (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 30)) MIX1)
        z (unchecked-multiply (bit-xor z (unsigned-bit-shift-right z 27)) MIX2)
        z (bit-xor z (unsigned-bit-shift-right z 31))]
    z))

(defn splitmix-at [seed index]
  (mix64 (unchecked-add (long seed) (unchecked-multiply (long index) GOLDEN))))

;; ─── Trit projection ───────────────────────────────────────────────
(defn trit-at
  "Balanced trit at position: every group of 3 is a permutation of {-1,0,+1}."
  [seed index]
  (let [triple-idx (quot index 3)
        within     (mod index 3)
        v          (splitmix-at seed triple-idx)
        perms      [[-1 0 1] [-1 1 0] [0 -1 1] [0 1 -1] [1 -1 0] [1 0 -1]]
        triple     (nth perms (mod v 6))]
    (nth triple within)))

(defn find-balancer
  "GF(3) balancer: c such that a + b + c ≡ 0 mod 3."
  [a b]
  (let [r (mod (- (+ a b)) 3)]
    (case (int r) 0 0, 1 1, 2 -1, -1 -1, -2 1, 0)))

;; ─── OKLAB color from seed (mirrors substrate.zig colorAt → fromSRGB) ──
(defn seed->rgb [seed index]
  (let [v (splitmix-at seed index)]
    {:r (bit-and (unsigned-bit-shift-right v 16) 0xFF)
     :g (bit-and (unsigned-bit-shift-right v 8) 0xFF)
     :b (bit-and v 0xFF)}))

(defn srgb->linear [v]
  (let [v (/ v 255.0)]
    (if (<= v 0.04045)
      (/ v 12.92)
      (Math/pow (/ (+ v 0.055) 1.055) 2.4))))

(defn rgb->oklab [{:keys [r g b]}]
  (let [rl (srgb->linear r) gl (srgb->linear g) bl (srgb->linear b)
        l_ (+ (* 0.4122214708 rl) (* 0.5363325363 gl) (* 0.0514459929 bl))
        m_ (+ (* 0.2119034982 rl) (* 0.6806995451 gl) (* 0.1073969566 bl))
        s_ (+ (* 0.0883024619 rl) (* 0.2220049368 gl) (* 0.6696926014 bl))
        lc (Math/cbrt l_) mc (Math/cbrt m_) sc (Math/cbrt s_)]
    {:L (+ (* 0.2104542553 lc) (* 0.7936177850 mc) (* -0.0040720468 sc))
     :a (+ (* 1.9779984951 lc) (* -2.4285922050 mc) (* 0.4505937099 sc))
     :b (+ (* 0.0259040371 lc) (* 0.7827717662 mc) (* -0.8086757660 sc))}))

;; ─── Semilattice fiber ─────────────────────────────────────────────
(defn name->seed
  "Deterministic seed from skill name (same as substrate.zig: hash name bytes)."
  [name]
  (reduce (fn [s b] (unchecked-add s (unchecked-multiply (long (bit-and b 0xFF)) MIX1)))
          0 (.getBytes (str name) "UTF-8")))

(defn skill-fiber
  "Compute SemilatticeFiber for a skill: {color, trit, hash}."
  [skill-name]
  (let [seed  (name->seed skill-name)
        h     (splitmix-at seed 0)
        rgb   (seed->rgb seed 0)
        color (rgb->oklab rgb)
        trit  (trit-at seed 0)]
    {:name  skill-name
     :hash  h
     :trit  trit
     :color color
     :seed  seed}))

(defn color-distance [{L1 :L a1 :a b1 :b} {L2 :L a2 :a b2 :b}]
  (Math/sqrt (+ (* (- L1 L2) (- L1 L2))
                (* (- a1 a2) (- a1 a2))
                (* (- b1 b2) (- b1 b2)))))

(defn color-join [c1 c2]
  {:L (* 0.5 (+ (:L c1) (:L c2)))
   :a (* 0.5 (+ (:a c1) (:a c2)))
   :b (* 0.5 (+ (:b c1) (:b c2)))})

(defn fiber-join [a b]
  {:name  (str (:name a) " ⊔ " (:name b))
   :hash  (mix64 (unchecked-add (:hash a) (:hash b)))
   :trit  (find-balancer (:trit a) (:trit b))
   :color (color-join (:color a) (:color b))
   :seed  (mix64 (unchecked-add (:seed a) (:seed b)))})

;; ─── SKILL.md parser ────────────────────────────────────────────────
(defn parse-frontmatter [text]
  (when (str/starts-with? text "---")
    (let [end (str/index-of text "---" 3)]
      (when end
        (let [yaml (subs text 3 end)]
          (->> (str/split-lines yaml)
               (keep (fn [line]
                       (when-let [[_ k v] (re-matches #"(\w[\w-]*):\s*(.+)" (str/trim line))]
                         [(keyword k) (str/trim v)])))
               (into {})))))))

(defn load-skill-meta [skill-dir]
  (let [f (io/file skill-dir "SKILL.md")]
    (when (and (.exists f) (.isFile f))
      (try
        (let [text (slurp f)
              fm   (parse-frontmatter text)]
          (merge {:name (.getName skill-dir)} fm))
        (catch Exception _ {:name (.getName skill-dir)})))))

;; ─── Load all skills ────────────────────────────────────────────────
(def skills-dir (io/file "/Users/bob/i/asi/skills"))

(defn all-skill-dirs []
  (->> (.listFiles skills-dir)
       (filter #(.isDirectory %))
       (filter #(.exists (io/file % "SKILL.md")))
       (sort-by #(.getName %))))

(defn all-fibers []
  (->> (all-skill-dirs)
       (map #(let [name (.getName %)]
               (assoc (skill-fiber name)
                      :meta (load-skill-meta %))))))

;; ─── Commands ───────────────────────────────────────────────────────

(defn cmd-fiber [name]
  (let [f (skill-fiber name)]
    (println (format "Skill:  %s" name))
    (println (format "Seed:   %016x" (:seed f)))
    (println (format "Hash:   %016x" (:hash f)))
    (println (format "Trit:   %+d" (:trit f)))
    (println (format "Color:  L=%.3f a=%.3f b=%.3f"
                     (:L (:color f)) (:a (:color f)) (:b (:color f))))))

(defn cmd-join [a b]
  (let [fa (skill-fiber a)
        fb (skill-fiber b)
        j  (fiber-join fa fb)]
    (println (format "%s ⊔ %s" a b))
    (println (format "  trit: %+d ⊔ %+d → %+d (balancer)" (:trit fa) (:trit fb) (:trit j)))
    (println (format "  color distance: %.4f" (color-distance (:color fa) (:color fb))))
    (println (format "  joined color: L=%.3f a=%.3f b=%.3f"
                     (:L (:color j)) (:a (:color j)) (:b (:color j))))
    (println (format "  conservation: %+d + %+d + %+d = %d (mod 3)"
                     (:trit fa) (:trit fb) (:trit j)
                     (mod (+ (:trit fa) (:trit fb) (:trit j)) 3)))))

(defn cmd-triad [a b]
  (let [fa (skill-fiber a)
        fb (skill-fiber b)
        needed-trit (find-balancer (:trit fa) (:trit fb))
        all-f (all-fibers)
        ;; Find skills matching the needed trit, sorted by color proximity to join point
        join-color (color-join (:color fa) (:color fb))
        candidates (->> all-f
                        (filter #(= needed-trit (:trit %)))
                        (sort-by #(color-distance join-color (:color %)))
                        (take 10))]
    (println (format "Triad completion for %s (trit %+d) and %s (trit %+d):" a (:trit fa) b (:trit fb)))
    (println (format "Need trit %+d to conserve GF(3)." needed-trit))
    (println)
    (doseq [[i c] (map-indexed vector candidates)]
      (println (format "  %2d. %-40s trit=%+d  dist=%.4f"
                       (inc i) (:name c) (:trit c)
                       (color-distance join-color (:color c)))))))

(defn cmd-discover [query]
  (let [qf (skill-fiber query)
        all-f (all-fibers)
        ;; Sort by color proximity to query fiber
        ranked (->> all-f
                    (map #(assoc % :dist (color-distance (:color qf) (:color %))))
                    (sort-by :dist)
                    (take 20))]
    (println (format "Discovery for \"%s\" (trit %+d, L=%.3f a=%.3f b=%.3f):"
                     query (:trit qf)
                     (:L (:color qf)) (:a (:color qf)) (:b (:color qf))))
    (println)
    (doseq [[i r] (map-indexed vector ranked)]
      (println (format "  %2d. %-40s trit=%+d  dist=%.4f  %s"
                       (inc i) (:name r) (:trit r) (:dist r)
                       (or (:description (:meta r)) ""))))))

(defn cmd-conserved []
  (let [all-f (all-fibers)
        trit-sum (reduce + (map :trit all-f))
        n (count all-f)
        by-trit (frequencies (map :trit all-f))]
    (println (format "Skills: %d" n))
    (println (format "Trit distribution: +1=%d  0=%d  -1=%d"
                     (get by-trit 1 0) (get by-trit 0 0) (get by-trit -1 0)))
    (println (format "Trit sum: %d" trit-sum))
    (println (format "GF(3) balanced: %s (sum mod 3 = %d)"
                     (if (zero? (mod trit-sum 3)) "YES ✓" "NO ✗")
                     (mod trit-sum 3)))))

(defn cmd-cluster [n]
  (let [all-f (all-fibers)
        ;; Simple: group by trit, then within each trit find closest pairs
        by-trit (group-by :trit all-f)
        ;; For each trit value, find the n densest neighborhoods
        report (fn [trit skills]
                 (println (format "\n=== Trit %+d (%d skills) ===" trit (count skills)))
                 ;; Pick n random anchors and show their neighborhoods
                 (let [anchors (take n (shuffle skills))]
                   (doseq [anchor anchors]
                     (let [neighbors (->> skills
                                         (remove #(= (:name %) (:name anchor)))
                                         (sort-by #(color-distance (:color anchor) (:color %)))
                                         (take 5))]
                       (println (format "  %s (L=%.2f):" (:name anchor) (:L (:color anchor))))
                       (doseq [nb neighbors]
                         (println (format "    → %-35s dist=%.4f" (:name nb) (color-distance (:color anchor) (:color nb)))))))))]
    (doseq [trit [-1 0 1]]
      (report trit (get by-trit trit [])))))

;; ─── Main ───────────────────────────────────────────────────────────
(let [[cmd & args] *command-line-args*]
  (case cmd
    "fiber"     (cmd-fiber (first args))
    "join"      (cmd-join (first args) (second args))
    "triad"     (cmd-triad (first args) (second args))
    "discover"  (cmd-discover (str/join " " args))
    "conserved?" (cmd-conserved)
    "cluster"   (cmd-cluster (parse-long (or (first args) "3")))
    (do (println "Usage: bb skill-semilattice.bb <command> [args]")
        (println "Commands: fiber, join, triad, discover, conserved?, cluster"))))
