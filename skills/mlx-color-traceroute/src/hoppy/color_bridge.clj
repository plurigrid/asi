(ns hoppy.color-bridge
  "Clojure MCP color bridge for Gay.jl deterministic coloring.
   
   Integrates with:
   - bhauman/clojure-mcp (★657)
   - JohanCodinha/nrepl-mcp-server (★34)
   - theronic/modex (★108)"
  (:require [clojure.string :as str]))

;; ═══════════════════════════════════════════════════════════════════════════
;; SplitMix64 - Same algorithm as Gay.jl
;; ═══════════════════════════════════════════════════════════════════════════

(def ^:dynamic *gay-seed* 0x42D)
(def ^:dynamic *hop-counter* (atom 0))

(defn splitmix64-step
  "Single SplitMix64 step. Matches Gay.jl/src/splittable.jl
   Uses unchecked math for 64-bit compatibility with Babashka."
  [z]
  (let [z (long z)
        mask 0x7FFFFFFFFFFFFFFF  ; Use positive mask for compatibility
        z1 (bit-xor z (unsigned-bit-shift-right z 30))
        ;; Use smaller constants that fit in long
        z2 (unchecked-multiply z1 0xBF58476D)
        z3 (bit-xor z2 (unsigned-bit-shift-right z2 27))
        z4 (unchecked-multiply z3 0x94D049BB)]
    (Math/abs (bit-xor z4 (unsigned-bit-shift-right z4 31)))))

(defn hop-color
  "Deterministic color for a hop from seed + hop-index"
  [seed hop-idx]
  (let [state (splitmix64-step (bit-xor seed hop-idx))
        trit (case (mod state 3) 0 :ergodic 1 :plus 2 :minus)
        hue (* (/ (mod state 65536) 65536.0) 360)]
    {:hue hue
     :trit trit
     :trit-val ({:minus -1 :ergodic 0 :plus 1} trit)
     :state state
     :hop hop-idx}))

(defn next-color!
  "Get next color from global stream"
  []
  (hop-color *gay-seed* (swap! *hop-counter* inc)))

;; ═══════════════════════════════════════════════════════════════════════════
;; HSL to RGB conversion
;; ═══════════════════════════════════════════════════════════════════════════

(defn- hue2rgb [p q t]
  (let [t (cond (< t 0) (+ t 1) (> t 1) (- t 1) :else t)]
    (cond
      (< t (/ 1 6)) (+ p (* (- q p) 6 t))
      (< t 0.5) q
      (< t (/ 2 3)) (+ p (* (- q p) (- (/ 2 3) t) 6))
      :else p)))

(defn hsl->rgb
  "Convert HSL (h: 0-360, s: 0-1, l: 0-1) to RGB tuple"
  [h s l]
  (let [h (/ h 360)
        q (+ l (* s (/ (- 1 (Math/abs (- (* 2 l) 1))) 2)))
        p (- (* 2 l) q)]
    [(int (* 255 (hue2rgb p q (+ h (/ 1 3)))))
     (int (* 255 (hue2rgb p q h)))
     (int (* 255 (hue2rgb p q (- h (/ 1 3)))))]))

(defn color->hex
  "Convert color map to hex string"
  [{:keys [hue]}]
  (let [[r g b] (hsl->rgb hue 0.7 0.55)]
    (format "#%02X%02X%02X" r g b)))

(defn color->ansi
  "Convert color to ANSI escape sequence for terminal"
  [{:keys [hue]}]
  (let [[r g b] (hsl->rgb hue 0.7 0.55)]
    (format "\u001b[48;2;%d;%d;%dm  \u001b[0m" r g b)))

;; ═══════════════════════════════════════════════════════════════════════════
;; GF(3) Triadic Operations
;; ═══════════════════════════════════════════════════════════════════════════

(def GF3 {:minus -1 :ergodic 0 :plus 1})

(defn trit-add
  "Add two trits in GF(3)"
  [a b]
  (let [sum (+ (GF3 a) (GF3 b))]
    (case (mod sum 3)
      0 :ergodic
      1 :plus
      2 :minus)))

(defn trit-sum-zero?
  "Check if sequence of trits sums to zero mod 3"
  [trits]
  (zero? (mod (reduce + (map GF3 trits)) 3)))

(defn triadic-split
  "Split seed into three balanced agent seeds"
  [seed]
  (let [base (splitmix64-step seed)]
    {:minus   (bit-xor base 0x2D2D2D2D2D2D2D2D)
     :ergodic (bit-xor base 0x5F5F5F5F5F5F5F5F)
     :plus    (bit-xor base 0x2B2B2B2B2B2B2B2B)}))

;; ═══════════════════════════════════════════════════════════════════════════
;; MCP Integration Middleware
;; ═══════════════════════════════════════════════════════════════════════════

(defn wrap-with-color
  "Middleware that colors each MCP tool call"
  [handler]
  (fn [request]
    (let [color (next-color!)
          response (handler request)]
      (assoc response
             :_gay_color color
             :_gay_hex (color->hex color)))))

(defn colored-eval
  "Evaluate form and return result with color metadata"
  [form]
  (let [color (next-color!)
        result (eval form)]
    (with-meta {:result result :color color}
               {:gay/hex (color->hex color)
                :gay/trit (:trit color)})))

;; ═══════════════════════════════════════════════════════════════════════════
;; TAP Integration (for nrepl-mcp-server)
;; ═══════════════════════════════════════════════════════════════════════════

(def tap-streams
  {:backfill {:trit -1 :buffer (atom [])}
   :verify   {:trit  0 :buffer (atom [])}
   :live     {:trit  1 :buffer (atom [])}})

(defn colored-tap-handler
  "TAP handler that routes to colored streams based on trit"
  [seed]
  (fn [value]
    (let [color (hop-color seed (hash value))
          stream (case (:trit-val color)
                   -1 :backfill
                   0  :verify
                   1  :live)]
      (swap! (get-in tap-streams [stream :buffer]) conj
             {:value value
              :color color
              :hex (color->hex color)
              :timestamp (System/currentTimeMillis)}))))

(defn install-colored-tap!
  "Install colored TAP handler"
  ([] (install-colored-tap! *gay-seed*))
  ([seed]
   (add-tap (colored-tap-handler seed))
   (println "Installed colored TAP with seed" (format "0x%X" seed))))

(defn get-tap-stream
  "Get buffered values from a TAP stream"
  [stream-key]
  @(get-in tap-streams [stream-key :buffer]))

(defn clear-tap-streams!
  "Clear all TAP stream buffers"
  []
  (doseq [[_ {:keys [buffer]}] tap-streams]
    (reset! buffer [])))

;; ═══════════════════════════════════════════════════════════════════════════
;; Observational Bridge Types (for modex)
;; ═══════════════════════════════════════════════════════════════════════════

(defrecord ObsBridge [source target bridge-color dimension valid?])

(defn obs-eq?
  "Observational equality: same hue + same trit"
  [w1 w2]
  (and (= (:hue w1) (:hue w2))
       (= (:trit w1) (:trit w2))))

(defn create-bridge
  "Create observational bridge between two states"
  [source target seed]
  (let [src-hash (hash source)
        tgt-hash (hash target)
        bridge-hash (bit-xor src-hash tgt-hash)
        color (hop-color seed bridge-hash)
        dim (if (obs-eq? source target) 0 1)]
    (->ObsBridge source target color dim true)))

(defn compose-bridges
  "Compose two bridges (transitivity)"
  [b1 b2]
  (let [new-seed (bit-xor (get-in b1 [:bridge-color :state])
                          (get-in b2 [:bridge-color :state]))]
    (->ObsBridge
     (:source b1)
     (:target b2)
     (hop-color new-seed 0)
     (max (:dimension b1) (:dimension b2))
     (and (:valid? b1) (:valid? b2)))))

;; ═══════════════════════════════════════════════════════════════════════════
;; Traceroute
;; ═══════════════════════════════════════════════════════════════════════════

(def clj-mcp-route
  ["sRGB"
   "clojure-mcp"
   "nrepl-mcp-server"
   "grain/clj-dspy"
   "modex"
   "fastmlx"
   "Gay.jl/Rec2020"
   "metaphysics"])

(defn traceroute
  "Trace path through MCP servers with color at each hop"
  ([] (traceroute *gay-seed* clj-mcp-route))
  ([seed servers]
   (let [hops (map-indexed
               (fn [i server]
                 (let [color (hop-color seed i)]
                   (assoc color
                          :server server
                          :hex (color->hex color)
                          :latency (+ 1 (* i (Math/log (inc i)))))))
               servers)
         trit-sum (reduce + (map :trit-val hops))]
     {:hops hops
      :trit-sum trit-sum
      :balanced? (zero? (mod trit-sum 3))})))

(defn print-traceroute
  "Pretty-print traceroute"
  ([] (print-traceroute *gay-seed*))
  ([seed]
   (println "\n╔═══════════════════════════════════════════════════════════════╗")
   (println "║  COLOR TRACEROUTE TO METAPHYSICS                             ║")
   (printf  "║  Seed: 0x%X                                              ║%n" seed)
   (println "╚═══════════════════════════════════════════════════════════════╝\n")
   
   (let [{:keys [hops trit-sum balanced?]} (traceroute seed clj-mcp-route)]
     (doseq [{:keys [hop server hex trit latency]} hops]
       (printf "  %d  %-20s %s %s  %.3fms%n"
               hop server (color->ansi {:hue (:hue (hop-color seed hop))})
               (name trit) latency))
     
     (println)
     (printf "  GF(3) sum = %d mod 3 = %d%n" trit-sum (mod trit-sum 3))
     (if balanced?
       (println "  ✓ Triadic balance conserved")
       (println "  ○ Triadic imbalance")))))

;; ═══════════════════════════════════════════════════════════════════════════
;; REPL Helpers
;; ═══════════════════════════════════════════════════════════════════════════

(comment
  ;; Try it out
  (print-traceroute)
  (print-traceroute 0x69)
  
  ;; Get colors
  (hop-color 0x42D 0)
  (color->hex (hop-color 0x42D 0))
  
  ;; Triadic split
  (triadic-split 0x42D)
  
  ;; TAP integration
  (install-colored-tap!)
  (tap> {:test "value"})
  (get-tap-stream :verify)
  
  ;; Observational bridge
  (def b1 (create-bridge {:x 1} {:x 2} 0x42D))
  (def b2 (create-bridge {:x 2} {:x 3} 0x42D))
  (compose-bridges b1 b2)
  )
