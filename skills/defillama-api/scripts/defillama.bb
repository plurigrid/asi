#!/usr/bin/env bb
;; DefiLlama API Client
;; Trit: -1 (MINUS) - Validator/Data Source

(ns defillama
  (:require [babashka.http-client :as http]
            [cheshire.core :as json]
            [clojure.string :as str]))

;; Configuration
(def base-urls
  {:free "https://api.llama.fi"           ;; Free endpoints
   :coins "https://coins.llama.fi"        ;; Price data
   :yields "https://yields.llama.fi"      ;; Yield data (some free)
   :pro "https://pro-api.llama.fi"        ;; Pro endpoints (needs key)
   :bridges "https://bridges.llama.fi"    ;; Bridge data
   :stablecoins "https://stablecoins.llama.fi"})

(def api-key (System/getenv "DEFILLAMA_API_KEY"))

(defn build-url
  "Build URL with optional API key for pro endpoints"
  ([base endpoint] (build-url base endpoint false))
  ([base endpoint pro?]
   (let [base-url (get base-urls base (:free base-urls))]
     (if (and pro? api-key)
       (str (:pro base-urls) "/" api-key endpoint)
       (str base-url endpoint)))))

(defn fetch
  "Fetch JSON from DefiLlama API"
  ([endpoint] (fetch :free endpoint false))
  ([base endpoint] (fetch base endpoint false))
  ([base endpoint pro?]
   (let [url (build-url base endpoint pro?)
         resp (http/get url {:headers {"Accept" "application/json"}
                             :throw false})]
     (if (< (:status resp) 400)
       (json/parse-string (:body resp) true)
       (throw (ex-info (str "API error: " (:status resp))
                       {:status (:status resp)
                        :body (:body resp)
                        :url url}))))))

;; ═══════════════════════════════════════════════════════════════
;; TVL & Protocol Data
;; ═══════════════════════════════════════════════════════════════

(defn protocols
  "List all protocols with current TVL"
  []
  (fetch "/protocols"))

(defn protocol
  "Get detailed protocol data including historical TVL"
  [slug]
  (fetch (str "/protocol/" slug)))

(defn tvl
  "Get simple TVL number for protocol"
  [slug]
  (fetch (str "/tvl/" slug)))

(defn token-protocols
  "Which protocols hold a specific token (Pro)"
  [symbol]
  (fetch (str "/api/tokenProtocols/" symbol) true))

(defn inflows
  "Daily capital flows for protocol (Pro)"
  [protocol-slug timestamp]
  (fetch (str "/api/inflows/" protocol-slug "/" timestamp) true))

;; ═══════════════════════════════════════════════════════════════
;; Chain Data
;; ═══════════════════════════════════════════════════════════════

(defn chains
  "Current TVL of all chains"
  []
  (fetch "/v2/chains"))

(defn historical-chain-tvl
  "Historical TVL for all chains or specific chain"
  ([] (fetch "/v2/historicalChainTvl"))
  ([chain] (fetch (str "/v2/historicalChainTvl/" chain))))

(defn chain-assets
  "Asset breakdown across all chains (Pro)"
  []
  (fetch "/api/chainAssets" true))

;; ═══════════════════════════════════════════════════════════════
;; Price Data
;; ═══════════════════════════════════════════════════════════════

(defn price
  "Current prices for coins (chain:address format)"
  [& coins]
  (let [coins-str (str/join "," coins)]
    (fetch :coins (str "/prices/current/" coins-str))))

(defn price-historical
  "Historical prices at timestamp"
  [timestamp & coins]
  (let [coins-str (str/join "," coins)]
    (fetch :coins (str "/prices/historical/" timestamp "/" coins-str))))

(defn price-chart
  "Price chart data"
  ([coins] (price-chart coins {}))
  ([coins {:keys [period span] :or {period "30d"}}]
   (let [coins-str (if (coll? coins) (str/join "," coins) coins)
         params (cond-> []
                  period (conj (str "period=" period))
                  span (conj (str "span=" span)))
         query (when (seq params) (str "?" (str/join "&" params)))]
     (fetch :coins (str "/chart/" coins-str query)))))

(defn price-first
  "First recorded price for coins"
  [& coins]
  (let [coins-str (str/join "," coins)]
    (fetch :coins (str "/prices/first/" coins-str))))

(defn block-at-time
  "Get block number at timestamp"
  [chain timestamp]
  (fetch (str "/coins/block/" chain "/" timestamp)))

;; ═══════════════════════════════════════════════════════════════
;; Yields (Pro)
;; ═══════════════════════════════════════════════════════════════

(defn yield-pools
  "All yield pools with current APY"
  []
  (fetch "/yields/pools" true))

(defn pool-chart
  "Historical APY/TVL for a pool"
  [pool-uuid]
  (fetch (str "/yields/chart/" pool-uuid) true))

(defn borrow-pools
  "Borrowing rates across protocols"
  []
  (fetch "/yields/poolsBorrow" true))

(defn lend-borrow-chart
  "Historical lend/borrow rates for pool"
  [pool-uuid]
  (fetch (str "/yields/chartLendBorrow/" pool-uuid) true))

(defn perps
  "Perpetual futures funding rates"
  []
  (fetch "/yields/perps" true))

(defn lsd-rates
  "Liquid staking derivative rates"
  []
  (fetch "/yields/lsdRates" true))

;; ═══════════════════════════════════════════════════════════════
;; Volume (DEXs, Derivatives, Options)
;; ═══════════════════════════════════════════════════════════════

(defn dex-overview
  "Aggregated DEX volumes"
  ([] (dex-overview nil))
  ([chain]
   (if chain
     (fetch (str "/api/overview/dexs/" chain))
     (fetch "/api/overview/dexs"))))

(defn dex-protocol
  "Specific DEX protocol volumes"
  [protocol-slug]
  (fetch (str "/api/summary/dexs/" protocol-slug)))

(defn options-overview
  "Options trading volumes"
  ([] (fetch "/api/overview/options"))
  ([chain] (fetch (str "/api/overview/options/" chain))))

(defn options-protocol
  "Specific options protocol data"
  [protocol-slug]
  (fetch (str "/api/summary/options/" protocol-slug)))

(defn derivatives-overview
  "Aggregated derivatives data (Pro)"
  []
  (fetch "/api/overview/derivatives" true))

(defn derivatives-protocol
  "Specific derivatives protocol (Pro)"
  [protocol-slug]
  (fetch (str "/api/summary/derivatives/" protocol-slug) true))

;; ═══════════════════════════════════════════════════════════════
;; Fees & Revenue
;; ═══════════════════════════════════════════════════════════════

(defn fees-overview
  "Protocol fees overview"
  ([] (fees-overview nil nil))
  ([chain] (fees-overview chain nil))
  ([chain data-type]
   (let [base-path (if chain
                     (str "/api/overview/fees/" chain)
                     "/api/overview/fees")
         query (when data-type (str "?dataType=" data-type))]
     (fetch (str base-path query)))))

(defn fees-protocol
  "Specific protocol fees"
  ([protocol-slug] (fees-protocol protocol-slug nil))
  ([protocol-slug data-type]
   (let [query (when data-type (str "?dataType=" data-type))]
     (fetch (str "/api/summary/fees/" protocol-slug query)))))

;; ═══════════════════════════════════════════════════════════════
;; Unlocks & Emissions (Pro)
;; ═══════════════════════════════════════════════════════════════

(defn emissions
  "All tokens with unlock schedules"
  []
  (fetch "/api/emissions" true))

(defn emission
  "Detailed vesting schedule for protocol"
  [protocol-slug]
  (fetch (str "/api/emission/" protocol-slug) true))

;; ═══════════════════════════════════════════════════════════════
;; Ecosystem Data (Pro)
;; ═══════════════════════════════════════════════════════════════

(defn categories
  "TVL by category"
  []
  (fetch "/api/categories" true))

(defn forks
  "Protocol fork relationships"
  []
  (fetch "/api/forks" true))

(defn oracles
  "Oracle protocol data"
  []
  (fetch "/api/oracles" true))

(defn entities
  "Company/entity information"
  []
  (fetch "/api/entities" true))

(defn treasuries
  "Protocol treasury balances"
  []
  (fetch "/api/treasuries" true))

(defn hacks
  "Historical exploits database"
  []
  (fetch "/api/hacks" true))

(defn raises
  "Funding rounds database"
  []
  (fetch "/api/raises" true))

(defn historical-liquidity
  "Historical liquidity for token"
  [token]
  (fetch (str "/api/historicalLiquidity/" token) true))

;; ═══════════════════════════════════════════════════════════════
;; ETF Data (Pro)
;; ═══════════════════════════════════════════════════════════════

(defn etf-overview
  "TradFi crypto ETF overview (BTC)"
  []
  (fetch "/etfs/overview" true))

(defn etf-overview-eth
  "Ethereum ETF data"
  []
  (fetch "/etfs/overviewEth" true))

(defn etf-history
  "Historical ETF flows (BTC)"
  []
  (fetch "/etfs/history" true))

(defn etf-history-eth
  "Historical Ethereum ETF data"
  []
  (fetch "/etfs/historyEth" true))

(defn fdv-performance
  "FDV performance metrics"
  [period]
  (fetch (str "/fdv/performance/" period) true))

;; ═══════════════════════════════════════════════════════════════
;; Bridges
;; ═══════════════════════════════════════════════════════════════

(defn bridges
  "List all bridges"
  []
  (fetch :bridges "/bridges"))

(defn bridge
  "Detailed bridge data"
  [id]
  (fetch :bridges (str "/bridge/" id)))

(defn bridge-volume
  "Bridge volume for chain"
  [chain]
  (fetch :bridges (str "/bridgevolume/" chain)))

(defn bridge-day-stats
  "Daily bridge stats"
  [timestamp chain]
  (fetch :bridges (str "/bridgedaystats/" timestamp "/" chain)))

(defn bridge-transactions
  "Bridge transactions"
  ([id] (bridge-transactions id {}))
  ([id {:keys [limit start-timestamp end-timestamp source-chain address]}]
   (let [params (cond-> []
                  limit (conj (str "limit=" limit))
                  start-timestamp (conj (str "startTimestamp=" start-timestamp))
                  end-timestamp (conj (str "endTimestamp=" end-timestamp))
                  source-chain (conj (str "sourceChain=" source-chain))
                  address (conj (str "address=" address)))
         query (when (seq params) (str "?" (str/join "&" params)))]
     (fetch :bridges (str "/transactions/" id query)))))

;; ═══════════════════════════════════════════════════════════════
;; Digital Asset Treasury (DAT) (Pro)
;; ═══════════════════════════════════════════════════════════════

(defn dat-institutions
  "Get comprehensive DAT data for all institutions"
  []
  (fetch "/dat/institutions" true))

(defn dat-institution
  "Get detailed DAT data for specific institution"
  [symbol]
  (fetch (str "/dat/institutions/" symbol) true))

;; ═══════════════════════════════════════════════════════════════
;; Account Management (Pro)
;; ═══════════════════════════════════════════════════════════════

(defn api-usage
  "Check API usage"
  []
  (when api-key
    (fetch (str "/usage/" api-key) true)))

;; ═══════════════════════════════════════════════════════════════
;; CLI Interface
;; ═══════════════════════════════════════════════════════════════

(defn -main [& args]
  (let [[cmd & cmd-args] args]
    (case cmd
      "protocols" (println (json/generate-string (protocols) {:pretty true}))
      "protocol" (println (json/generate-string (apply protocol cmd-args) {:pretty true}))
      "tvl" (println (apply tvl cmd-args))
      "chains" (println (json/generate-string (chains) {:pretty true}))
      "price" (println (json/generate-string (apply price cmd-args) {:pretty true}))
      "yields" (println (json/generate-string (yield-pools) {:pretty true}))
      "dex" (println (json/generate-string (dex-overview) {:pretty true}))
      "fees" (println (json/generate-string (fees-overview) {:pretty true}))
      "bridges" (println (json/generate-string (bridges) {:pretty true}))
      "dat" (println (json/generate-string (dat-institutions) {:pretty true}))
      "usage" (println (json/generate-string (api-usage) {:pretty true}))
      (println "Usage: defillama.bb <command> [args]
Commands:
  protocols           - List all protocols
  protocol <slug>     - Get protocol details
  tvl <slug>          - Get protocol TVL
  chains              - List all chains
  price <coins...>    - Get current prices
  yields              - List yield pools (Pro)
  dex                 - DEX overview
  fees                - Fees overview
  bridges             - List bridges
  dat                 - DAT institutions (Pro)
  usage               - Check API usage (Pro)"))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
