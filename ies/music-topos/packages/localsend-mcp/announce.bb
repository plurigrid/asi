#!/usr/bin/env bb
;; Gay-colored LocalSend announcer with varying speech rate
;; Voice: Emma (Premium) Italian | Base rate: 69, varied by Gay.jl color chain

(require '[babashka.process :as p])

(def dns-name "causality.pirate-dragon.ts.net")
(def port 53317)
(def ip "100.69.33.107")
(def voice "Emma (Premium)")
(def base-rate 69)

;; Simple LCG for rate variation (avoids BigInt issues)
(def ^:dynamic *seed* (atom 1069))

(defn next-random! []
  (swap! *seed* (fn [s] (mod (+ (* s 1103515245) 12345) 2147483648)))
  @*seed*)

(defn get-rate []
  (let [r (next-random!)
        variation (- (mod r 100) 50)]
    (+ base-rate variation 100))) ;; 119-219 for audibility

(defn get-color []
  (let [r (mod (next-random!) 256)
        g (mod (next-random!) 256)
        b (mod (next-random!) 256)]
    (format "#%02X%02X%02X" r g b)))

(defn announce! [idx]
  (let [color (get-color)
        rate (get-rate)
        message (str "Attenzione! LocalSend peer available! "
                     "Connect to causality dot pirate dragon dot ti es dot net, porta 53317. "
                     "Ripeto: causality, pirate dragon, ti es net, porta cinque tre tre uno sette. "
                     "IP address: cento punto sessantanove punto trentatré punto centosétte. "
                     "Awaiting file transfers adesso!")]
    (println)
    (println (str "📢 Announcement " (inc idx) "/5"))
    (println (str "🌈 Color: " color " | Rate: " rate))
    (p/shell {:out :inherit :err :inherit}
             "say" "-v" voice "-r" (str rate) message)))

(defn banner []
  (println "╔══════════════════════════════════════════════════════════════╗")
  (println "║  🏴‍☠️ LocalSend Announcer - causality.pirate-dragon.ts.net    ║")
  (println (format "║  Port: %d | IP: %s                              ║" port ip))
  (println (format "║  Voice: %s | Base Rate: %d                    ║" voice base-rate))
  (println "╚══════════════════════════════════════════════════════════════╝"))

(defn -main []
  (banner)
  (doseq [i (range 5)]
    (announce! i)
    (Thread/sleep 2000))
  (println)
  (println "✅ Tutti gli annunci completati!")
  (println (str "🔗 Send files to: http://" dns-name ":" port)))

(-main)
