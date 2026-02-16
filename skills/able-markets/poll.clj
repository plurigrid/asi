#!/usr/bin/env bb
;; *Able Markets - Protocol Proposal Polling
;; Tracks draft proposals across Aptos AIPs, Swift SE, Scheme SRFIs

(ns able-markets.poll
  (:require [babashka.http-client :as http]
            [cheshire.core :as json]
            [clojure.string :as str]))

;; =============================================================================
;; Configuration
;; =============================================================================

(def ecosystems
  {:aptos {:name "Aptos AIPs"
           :base-url "https://api.github.com/repos/aptos-foundation/AIPs/contents/aips/"
           :proposals [{:id "AIP-137" :file "aip-137.md" :able-trait "PQ-Signable" :prob 0.65}
                       {:id "AIP-129" :file "aip-129.md" :able-trait "Replay-Protectable" :prob 0.80}
                       {:id "AIP-113" :file "aip-113.md" :able-trait "Derivable" :prob 0.70}
                       ;; Asymmetric bets - high impact, low probability
                       {:id "AIP-119" :file "aip-119.md" :able-trait "Deflationary" :prob 0.15 :asymmetric true}
                       {:id "AIP-120" :file "aip-120.md" :able-trait "CLOB-Native" :prob 0.25 :asymmetric true}
                       {:id "AIP-125" :file "aip-125.md" :able-trait "Time-Triggerable" :prob 0.40 :asymmetric true}
                       {:id "AIP-130" :file "aip-130.md" :able-trait "Negatable" :prob 0.65 :asymmetric true}]}
   :swift {:name "Swift Evolution"
           :base-url "https://api.github.com/repos/swiftlang/swift-evolution/contents/proposals/"
           :proposals [{:id "SE-0487" :file "0487-extensible-enums.md" :able-trait "Extensible"}
                       {:id "SE-0499" :file "0499-support-non-copyable-simple-protocols.md" :able-trait "NonCopyable"}
                       {:id "SE-0500" :file "0500-package-manager-templates.md" :able-trait "Templatable"}]}
   :srfi {:name "Scheme SRFIs"
          :base-url "https://srfi.schemers.org/srfi-"
          :proposals [{:id "SRFI-265" :file "265" :able-trait "CFG-Composable"}
                      {:id "SRFI-263" :file "263" :able-trait "Prototype-Clonable"}]}})

;; =============================================================================
;; GitHub API Polling
;; =============================================================================

(defn fetch-github-file [url]
  (try
    (let [response (http/get url {:headers {"Accept" "application/vnd.github.v3+json"
                                            "User-Agent" "able-markets-poll"}})]
      (when (= 200 (:status response))
        (-> response :body (json/parse-string true))))
    (catch Exception e
      (println "Error fetching" url ":" (.getMessage e))
      nil)))

(defn decode-base64 [s]
  (when s
    (String. (.decode (java.util.Base64/getDecoder) 
                      (str/replace s #"\n" "")))))

(defn extract-status [content]
  (when content
    (let [status-match (re-find #"(?i)Status:\s*(\w+)" content)]
      (when status-match
        (str/lower-case (second status-match))))))

(defn extract-last-call [content]
  (when content
    (let [lc-match (re-find #"last-call-end-date.*?(\d{2}/\d{2}/\d{4})" content)]
      (second lc-match))))

;; =============================================================================
;; Proposal Status Checking
;; =============================================================================

(defn check-aptos-proposal [{:keys [id file able-trait]}]
  (let [url (str (get-in ecosystems [:aptos :base-url]) file)
        data (fetch-github-file url)]
    (when data
      (let [content (decode-base64 (:content data))
            status (extract-status content)
            last-call (extract-last-call content)]
        {:id id
         :ecosystem :aptos
         :status status
         :last-call last-call
         :able-trait able-trait
         :updated (:sha data)}))))

(defn check-swift-proposal [{:keys [id file able-trait]}]
  (let [url (str (get-in ecosystems [:swift :base-url]) file)
        data (fetch-github-file url)]
    (when data
      (let [content (decode-base64 (:content data))
            status-match (re-find #"(?i)\*\*Status:\*\*\s*(\w+)" content)]
        {:id id
         :ecosystem :swift
         :status (when status-match (str/lower-case (second status-match)))
         :able-trait able-trait
         :updated (:sha data)}))))

(defn check-srfi-proposal [{:keys [id file able-trait]}]
  ;; SRFI uses HTML pages, simplified check
  {:id id
   :ecosystem :srfi
   :status "draft"  ;; Would need HTML parsing for actual status
   :able-trait able-trait})

(defn poll-all-proposals []
  (println "\n=== *Able Markets: Proposal Status ===\n")
  
  ;; Aptos AIPs
  (println "📦 Aptos AIPs:")
  (doseq [proposal (get-in ecosystems [:aptos :proposals])]
    (let [result (check-aptos-proposal proposal)]
      (when result
        (println (format "  %s [%s] - %s (last-call: %s)"
                         (:id result)
                         (:status result)
                         (:able-trait result)
                         (or (:last-call result) "none"))))))
  
  ;; Swift Evolution
  (println "\n🍎 Swift Evolution:")
  (doseq [proposal (get-in ecosystems [:swift :proposals])]
    (let [result (check-swift-proposal proposal)]
      (when result
        (println (format "  %s [%s] - %s"
                         (:id result)
                         (or (:status result) "unknown")
                         (:able-trait result))))))
  
  ;; SRFIs
  (println "\n🔧 Scheme SRFIs:")
  (doseq [proposal (get-in ecosystems [:srfi :proposals])]
    (let [result (check-srfi-proposal proposal)]
      (println (format "  %s [%s] - %s"
                       (:id result)
                       (:status result)
                       (:able-trait result)))))
  
  (println "\n✅ Poll complete"))

;; =============================================================================
;; WEV Calculation
;; =============================================================================

(defn calculate-wev 
  "Calculate World Extractable Value for a proposal."
  [proposal-id {:keys [accounts-at-risk avg-value-apt probability value-at-risk-ratio]
                :or {accounts-at-risk 10000000
                     avg-value-apt 100
                     probability 0.15
                     value-at-risk-ratio 0.001}}]
  (let [wev (* accounts-at-risk avg-value-apt probability value-at-risk-ratio)]
    {:proposal-id proposal-id
     :wev-apt wev
     :inputs {:accounts accounts-at-risk
              :avg-value avg-value-apt
              :probability probability
              :var-ratio value-at-risk-ratio}}))

;; =============================================================================
;; Market Simulation (LMSR)
;; =============================================================================

(defn lmsr-cost [yes-shares no-shares liquidity]
  (* liquidity 
     (Math/log (+ (Math/exp (/ yes-shares liquidity))
                  (Math/exp (/ no-shares liquidity))))))

(defn lmsr-price-yes [yes-shares no-shares liquidity]
  (let [exp-yes (Math/exp (/ yes-shares liquidity))
        exp-no (Math/exp (/ no-shares liquidity))]
    (/ exp-yes (+ exp-yes exp-no))))

(defn simulate-market [proposal-id initial-liquidity trades]
  (loop [yes 0.0
         no 0.0
         remaining trades
         history []]
    (if (empty? remaining)
      {:proposal-id proposal-id
       :final-yes-shares yes
       :final-no-shares no
       :implied-probability (lmsr-price-yes yes no initial-liquidity)
       :history history}
      (let [[direction amount] (first remaining)
            new-yes (if (= direction :yes) (+ yes amount) yes)
            new-no (if (= direction :no) (+ no amount) no)
            price (lmsr-price-yes new-yes new-no initial-liquidity)]
        (recur new-yes new-no (rest remaining)
               (conj history {:direction direction
                              :amount amount
                              :price-after price}))))))

;; =============================================================================
;; CLI Entry Point
;; =============================================================================

(defn -main [& args]
  (case (first args)
    "poll" (poll-all-proposals)
    "wev" (let [result (calculate-wev (or (second args) "AIP-137")
                                       {:probability (or (some-> (nth args 2) parse-double) 0.15)})]
            (println "\n=== WEV Calculation ===")
            (println (format "Proposal: %s" (:proposal-id result)))
            (println (format "WEV: %.2f APT" (:wev-apt result)))
            (println "Inputs:" (:inputs result)))
    "simulate" (let [result (simulate-market "AIP-137" 1000.0
                                              [[:yes 50] [:no 30] [:yes 100] [:no 20]])]
                 (println "\n=== Market Simulation ===")
                 (println (format "Proposal: %s" (:proposal-id result)))
                 (println (format "Implied Probability: %.2f%%" (* 100 (:implied-probability result))))
                 (println "Trade History:" (:history result)))
    (do
      (println "Usage: bb poll.clj <command>")
      (println "Commands:")
      (println "  poll      - Check all proposal statuses")
      (println "  wev [id] [prob] - Calculate WEV")
      (println "  simulate  - Run market simulation"))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
