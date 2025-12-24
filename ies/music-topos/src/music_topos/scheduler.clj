(ns music-topos.scheduler
  "Centralized timing scheduler using monotonic clock.
   Replaces scattered Thread/sleep with single scheduling loop."
  (:require [overtone.osc :as osc]))

(def ^:private osc-client (atom nil))

(defn connect!
  "Connect to SuperCollider OSC server."
  ([] (connect! "127.0.0.1" 57110))
  ([host port]
   (reset! osc-client (osc/osc-client host port))))

(defn disconnect! []
  (when-let [client @osc-client]
    (osc/osc-close client)
    (reset! osc-client nil)))

(defn beats->seconds
  "Convert beats to seconds at given tempo (BPM)."
  [beats tempo]
  (/ (* beats 60.0) tempo))

(defn seconds->nanos
  "Convert seconds to nanoseconds."
  [seconds]
  (long (* seconds 1e9)))

(defn nanos->millis
  "Convert nanoseconds to milliseconds for Thread/sleep."
  [nanos]
  (/ nanos 1e6))

(defn play-event!
  "Send a single event to SuperCollider via OSC.
   Event is a map with :freq, :amp, :dur, etc."
  [{:keys [freq amp dur] :or {freq 440 amp 0.3 dur 0.5}}]
  (when-let [client @osc-client]
    (osc/osc-send client "/s_new" "default" -1 0 1
                  "freq" (float freq)
                  "amp" (float amp)
                  "dur" (float dur))))

(defn schedule-events!
  "Schedule and play a sequence of score events with centralized timing.
   
   Args:
     tempo  - beats per minute
     events - seq of {:beat n :freq f :amp a :dur d ...}
   
   Uses monotonic System/nanoTime for accurate scheduling.
   Single sleep loop instead of scattered Thread/sleep calls."
  [tempo events]
  (when (seq events)
    (let [start-nanos (System/nanoTime)
          scheduled   (mapv (fn [{:keys [beat] :as event}]
                              (let [offset-secs  (beats->seconds beat tempo)
                                    offset-nanos (seconds->nanos offset-secs)
                                    target-nanos (+ start-nanos offset-nanos)]
                                (assoc event :target-nanos target-nanos)))
                            events)
          sorted      (sort-by :target-nanos scheduled)]
      (doseq [{:keys [target-nanos] :as event} sorted]
        (let [now        (System/nanoTime)
              wait-nanos (- target-nanos now)]
          (when (pos? wait-nanos)
            (Thread/sleep (nanos->millis wait-nanos)))
          (play-event! event))))))

(defn play-score!
  "Convenience function: connect, play events, disconnect.
   
   Example:
     (play-score! 120 [{:beat 0 :freq 440}
                       {:beat 1 :freq 550}
                       {:beat 2 :freq 660}])"
  [tempo events]
  (connect!)
  (try
    (schedule-events! tempo events)
    (finally
      (Thread/sleep 500)
      (disconnect!))))
