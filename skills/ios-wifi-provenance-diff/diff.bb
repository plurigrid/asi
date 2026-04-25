#!/usr/bin/env bb
;; ios-wifi-provenance.diff
;;
;; Diff two com.apple.wifi.known-networks.plist files (one per iPhone),
;; classify each entry's AddReason as a GF(3) trit, and emit:
;;   - per-device rows (DuckDB INSERTs into wifi_provenance_diff)
;;   - per-SSID diff (EDN to *out*) flagging asymmetric provenance
;;
;; Authorized-owner use only. Companion to SKILL.md in this directory.
;;
;; CLI:
;;   diff.bb <plist-A> <plist-B> <ECID-A> <ECID-B>
;;
;; REPL (from a project bb nREPL via forj):
;;   (require '[ios-wifi-provenance.diff :as d])
;;   (d/run! "/path/sysdiag-A/.../known-networks.plist" "ECID-A"
;;           "/path/sysdiag-B/.../known-networks.plist" "ECID-B")

(ns ios-wifi-provenance.diff
  (:require [clojure.data.json :as json]
            [clojure.java.shell :refer [sh]]
            [clojure.set :as set]
            [clojure.string :as str]
            [clojure.pprint :as pp]))

;; -- plist load (delegates to macOS plutil; no native binary-plist parser in bb) --

(defn plist->edn
  "Convert a binary or XML plist file to EDN via macOS plutil → JSON.
   Keys with spaces (e.g. 'List of known networks') become space-bearing keywords."
  [path]
  (let [{:keys [exit out err]} (sh "plutil" "-convert" "json" "-r" "-o" "-" path)]
    (when-not (zero? exit)
      (throw (ex-info "plutil failed" {:path path :stderr err})))
    (json/read-str out :key-fn keyword)))

;; -- shape detection (iOS 16+ vs pre-16) --

(def ^:private legacy-key (keyword "List of known networks"))

(defn entries
  "Return a seq of network maps regardless of plist schema version."
  [plist-data]
  (cond
    (and (map? plist-data) (contains? plist-data legacy-key))
    (get plist-data legacy-key)                          ; pre-iOS 16: array under that key

    (map? plist-data)
    (for [[k v] plist-data :when (map? v)]               ; iOS 16+: {ssid_str => entry-map}
      (assoc v :_ssid_key (name k)))

    :else (throw (ex-info "unrecognized plist shape" {}))))

;; -- GF(3) classification --

(def add-reason->trit
  "Manual=+1 (typed locally, full ShareableInfo).
   iCloudSync=0 (came from CKKS AppleWiFiPassword view).
   NetworkSharing=-1 (came from Share Password sheet via AWDL+BT).
   Other reasons (WAPI, Ranging, etc.) are 0 / unclassified."
  {"Manual"          1
   "iCloudSync"      0
   "NetworkSharing" -1})

(defn classify [entry]
  (get add-reason->trit (:AddReason entry) 0))

(defn ssid-of [entry]
  (or (:_ssid_key entry)                                ; iOS 16+
      (:SSID_STR entry)                                 ; pre-16 ASCII fallback
      (some-> (:SSID entry) str)))                      ; bytes; better than nothing

;; -- normalization --

(defn normalize-row [device-id plist-path entry]
  (let [os-spec (:__OSSpecific__ entry)]
    {:device-ecid          device-id
     :ssid                 (ssid-of entry)
     :add-reason           (:AddReason entry)
     :bundle-id            (:BundleID entry)
     :hidden               (boolean (:Hidden entry))
     :bssid                (:BSSID os-spec)
     :added-at             (:AddedAt entry)
     :joined-by-system-at  (:JoinedBySystemAt entry)
     :joined-by-user-at    (:JoinedByUserAt entry)
     :updated-at           (:UpdatedAt entry)
     :system-mode          (boolean (or (:SystemMode entry) (:SystemMode os-spec)))
     :has-shareable-info   (some? (:ShareableInfo entry))
     :has-password-enclave (some? (:PasswordEnclave entry))
     :provenance-trit      (classify entry)
     :sysdiag-path         plist-path}))

(defn parse-entries
  "Pure: map already-parsed plist EDN to a seq of normalized rows.
   No I/O — REPL-testable without plutil/macOS."
  [device-id source-tag plist-edn]
  (->> plist-edn entries
       (map (partial normalize-row device-id source-tag))
       (filter :ssid)))

(defn load-device
  "I/O: read plist from disk via plutil, return normalized rows."
  [plist-path device-id]
  (parse-entries device-id plist-path (plist->edn plist-path)))

;; -- diff --

(defn ssid-diff
  "For each SSID common to both devices, return a row describing the asymmetry."
  [a-rows b-rows]
  (let [a-by (into {} (map (juxt :ssid identity)) a-rows)
        b-by (into {} (map (juxt :ssid identity)) b-rows)
        common (set/intersection (set (keys a-by)) (set (keys b-by)))]
    (for [ssid (sort common)
          :let [a (a-by ssid) b (b-by ssid)]]
      {:ssid          ssid
       :a-add-reason  (:add-reason a)
       :b-add-reason  (:add-reason b)
       :a-trit        (:provenance-trit a)
       :b-trit        (:provenance-trit b)
       :trit-delta    (mod (- (:provenance-trit a) (:provenance-trit b)) 3)
       :asymmetric?   (not= (:add-reason a) (:add-reason b))
       :diff-keys     (vec (filter #(not= (get a %) (get b %))
                                   [:add-reason :has-shareable-info
                                    :has-password-enclave :system-mode
                                    :bundle-id]))})))

;; -- DuckDB SQL emission --

(def schema-ddl
  "CREATE TABLE IF NOT EXISTS wifi_provenance_diff (
    id INTEGER,
    ssid VARCHAR NOT NULL,
    device_ecid VARCHAR NOT NULL,
    add_reason VARCHAR,
    bundle_id VARCHAR,
    hidden BOOLEAN,
    bssid VARCHAR,
    added_at TIMESTAMP,
    joined_by_system_at TIMESTAMP,
    joined_by_user_at TIMESTAMP,
    updated_at TIMESTAMP,
    system_mode BOOLEAN,
    has_shareable_info BOOLEAN,
    has_password_enclave BOOLEAN,
    provenance_trit TINYINT,
    copy_enabled BOOLEAN,
    sysdiag_path VARCHAR,
    captured_at TIMESTAMP
  );")

(defn- sql-lit [v]
  (cond (nil? v)     "NULL"
        (boolean? v) (str v)
        (number? v)  (str v)
        :else        (str \' (str/replace (str v) "'" "''") \')))

(defn row->insert [r]
  (format
    (str "INSERT INTO wifi_provenance_diff (ssid, device_ecid, add_reason, "
         "bundle_id, hidden, bssid, added_at, joined_by_system_at, "
         "joined_by_user_at, updated_at, system_mode, has_shareable_info, "
         "has_password_enclave, provenance_trit, sysdiag_path, captured_at) "
         "VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, CURRENT_TIMESTAMP);")
    (sql-lit (:ssid r))                  (sql-lit (:device-ecid r))
    (sql-lit (:add-reason r))            (sql-lit (:bundle-id r))
    (sql-lit (:hidden r))                (sql-lit (:bssid r))
    (sql-lit (:added-at r))              (sql-lit (:joined-by-system-at r))
    (sql-lit (:joined-by-user-at r))     (sql-lit (:updated-at r))
    (sql-lit (:system-mode r))           (sql-lit (:has-shareable-info r))
    (sql-lit (:has-password-enclave r))  (sql-lit (:provenance-trit r))
    (sql-lit (:sysdiag-path r))))

;; -- top-level --

(defn run!
  "Emit DDL + INSERTs to *out* and per-SSID diff to *err* (so SQL can be piped)."
  [plist-a ecid-a plist-b ecid-b]
  (let [a (load-device plist-a ecid-a)
        b (load-device plist-b ecid-b)
        d (ssid-diff a b)]
    (println schema-ddl)
    (doseq [r (concat a b)] (println (row->insert r)))
    (binding [*out* *err*]
      (println "\n;; -- per-SSID diff --")
      (pp/pprint d)
      (println "\n;; asymmetric SSIDs:"
               (count (filter :asymmetric? d)) "/" (count d)))))

(when (= *file* (System/getProperty "babashka.file"))
  (let [[a ea b eb] *command-line-args*]
    (if (and a b ea eb)
      (run! a ea b eb)
      (binding [*out* *err*]
        (println "usage: diff.bb <plist-A> <plist-B> <ECID-A> <ECID-B>")
        (System/exit 2)))))

(comment
  ;; -- Smoke tests, REPL-callable. Run via forj eval_comment_block on a
  ;;    fresh bb nREPL (NOT the nash-ducklake REPL — see feedback memory).
  ;;    All assertions; final value :all-smoke-pass means green.

  ;; 1. classify covers known reasons + safe default
  (assert (= 1  (classify {:AddReason "Manual"})))
  (assert (= 0  (classify {:AddReason "iCloudSync"})))
  (assert (= -1 (classify {:AddReason "NetworkSharing"})))
  (assert (= 0  (classify {:AddReason "WAPI"})))
  (assert (= 0  (classify {})))

  ;; 2. iOS 16+ shape: {ssid_str => entry-map}
  (let [edn  {(keyword "MyHome") {:AddReason "Manual"
                                  :__OSSpecific__ {:BSSID "aa:bb:cc:dd:ee:ff"}
                                  :ShareableInfo {:k "v"}}
              (keyword "Cafe")   {:AddReason "NetworkSharing"
                                  :__OSSpecific__ {:BSSID "11:22:33:44:55:66"}}}
        rows (parse-entries "ECID-A" "fixture-A" edn)]
    (assert (= 2 (count rows)))
    (assert (= #{"MyHome" "Cafe"} (set (map :ssid rows))))
    (assert (true? (:has-shareable-info
                    (first (filter #(= "MyHome" (:ssid %)) rows)))))
    (assert (= "aa:bb:cc:dd:ee:ff"
               (:bssid (first (filter #(= "MyHome" (:ssid %)) rows))))))

  ;; 3. pre-iOS-16 shape: array under "List of known networks"
  (let [edn  {(keyword "List of known networks")
              [{:SSID_STR "Old1" :AddReason "Manual"}
               {:SSID_STR "Old2"}]}                       ; no AddReason → trit 0
        rows (parse-entries "ECID-OLD" "fixture-15" edn)]
    (assert (= 2 (count rows)))
    (assert (= #{"Old1" "Old2"} (set (map :ssid rows))))
    (assert (= 1 (:provenance-trit (first (filter #(= "Old1" (:ssid %)) rows)))))
    (assert (= 0 (:provenance-trit (first (filter #(= "Old2" (:ssid %)) rows))))))

  ;; 4. End-to-end diff: A all-Manual, B has one iCloudSync (the asymmetry)
  (let [a-edn   {(keyword "Home") {:AddReason "Manual"}
                 (keyword "Cafe") {:AddReason "Manual"}}
        b-edn   {(keyword "Home") {:AddReason "iCloudSync"}      ; asymmetric
                 (keyword "Cafe") {:AddReason "Manual"}          ; symmetric
                 (keyword "Solo") {:AddReason "Manual"}}         ; B-only, dropped
        a       (parse-entries "ECID-A" "A" a-edn)
        b       (parse-entries "ECID-B" "B" b-edn)
        d       (ssid-diff a b)
        by-ssid (into {} (map (juxt :ssid identity)) d)]
    (assert (= 2 (count d)) "diff should only include SSIDs common to both")
    (assert (true?  (:asymmetric? (by-ssid "Home"))))
    (assert (false? (:asymmetric? (by-ssid "Cafe"))))
    (assert (= 1 (:trit-delta (by-ssid "Home"))))                 ; (1 - 0) mod 3
    (assert (= 0 (:trit-delta (by-ssid "Cafe")))))                ; (1 - 1) mod 3

  ;; 5. SQL emission well-formed + escapes apostrophes
  (let [sql (row->insert {:device-ecid "X" :ssid "Test" :add-reason "Manual"
                          :hidden false :provenance-trit 1})]
    (assert (str/starts-with? sql "INSERT INTO wifi_provenance_diff"))
    (assert (str/includes? sql "'Test'"))
    (assert (str/includes? sql "'Manual'")))
  (assert (str/includes?
           (row->insert {:ssid "Bob's Place" :device-ecid "X" :provenance-trit 0})
           "'Bob''s Place'"))

  :all-smoke-pass)
