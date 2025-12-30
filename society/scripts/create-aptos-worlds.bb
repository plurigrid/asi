#!/usr/bin/env bb
;; create-aptos-worlds.bb - Generate 28 Aptos wallets with GF(3) trit assignment
;; Idempotent: skips existing wallets

(ns create-aptos-worlds
  (:require [babashka.fs :as fs]
            [babashka.process :refer [shell]]
            [cheshire.core :as json]
            [clojure.string :as str]))

(def worlds-dir (str (System/getProperty "user.home") "/.aptos/worlds"))

;; 28 wallets: alice, bob, world_a through world_z
(def wallet-names
  (concat ["alice" "bob"]
          (map #(str "world_" (char %)) (range (int \a) (inc (int \z))))))

;; GF(3) trit assignment
;; alice = +1, bob = 0
;; world_a through world_z: cycle [-1, 0, +1] starting at a
(defn trit-for-wallet [name]
  (cond
    (= name "alice") 1
    (= name "bob") 0
    :else
    (let [letter (last name)  ; Extract letter from "world_x"
          idx (- (int letter) (int \a))]
      (case (mod idx 3)
        0 -1      ; a, d, g, j, m, p, s, v, y
        1  0      ; b, e, h, k, n, q, t, w, z
        2  1))))  ; c, f, i, l, o, r, u, x

(defn key-path [name]
  (str worlds-dir "/" name ".key"))

(defn wallet-exists? [name]
  (fs/exists? (key-path name)))

(defn generate-wallet! [name]
  (let [path (key-path name)]
    (if (wallet-exists? name)
      (do
        (println (format "  ⏭️  %s already exists, skipping" name))
        nil)
      (do
        (println (format "  🔑 Generating %s..." name))
        (shell {:out :string :err :string}
               "aptos" "key" "generate"
               "--output-file" path
               "--assume-yes")
        path))))

(defn read-address [name]
  (let [key-file (key-path name)
        pub-file (str key-file ".pub")]
    (when (fs/exists? pub-file)
      (let [pubkey (str/trim (slurp pub-file))]
        ;; Derive address via aptos CLI
        (-> (shell {:out :string :err :string}
                   "aptos" "account" "derive-resource-account-address"
                   "--address" pubkey
                   "--seed" "")
            :out
            (str/trim)
            ;; Parse JSON output for address
            (json/parse-string true)
            :Result)))))

(defn get-account-address [name]
  "Get address from public key file using aptos account lookup-address"
  (let [pub-file (str (key-path name) ".pub")]
    (when (fs/exists? pub-file)
      (try
        (let [pubkey (str/trim (slurp pub-file))
              ;; Use aptos account lookup-address --public-key
              result (shell {:out :string :err :string :continue true}
                            "aptos" "account" "lookup-address"
                            "--public-key" pubkey)
              output (:out result)]
          ;; Parse JSON output for address
          (when-let [parsed (try (json/parse-string output true) (catch Exception _ nil))]
            (:Result parsed)))
        (catch Exception e
          (println (format "    ⚠️  Could not derive address for %s" name))
          nil)))))

(defn -main []
  (println "🌐 Creating Aptos Worlds (28 wallets)")
  (println (format "📁 Output directory: %s\n" worlds-dir))
  
  (fs/create-dirs worlds-dir)
  
  ;; Generate all wallets
  (println "🔐 Generating wallets...")
  (doseq [name wallet-names]
    (generate-wallet! name))
  
  (println "\n📋 Building manifest...")
  
  ;; Build manifest with addresses and trits
  (let [entries (for [name wallet-names]
                  (let [trit (trit-for-wallet name)
                        addr (get-account-address name)]
                    {:name name
                     :key_file (key-path name)
                     :address addr
                     :trit trit
                     :role (case trit
                             -1 "MINUS"
                              0 "ERGODIC"
                              1 "PLUS")}))
        manifest {:version "1.0.0"
                  :created_at (str (java.time.Instant/now))
                  :network "mainnet"
                  :wallets entries
                  :gf3_verification
                  {:total_sum (reduce + (map :trit entries))
                   :mod3 (mod (reduce + (map :trit entries)) 3)
                   :conserved? (zero? (mod (reduce + (map :trit entries)) 3))}}
        manifest-path (str worlds-dir "/manifest.json")]
    
    ;; Print summary
    (println "\n📊 GF(3) Trit Assignment:")
    (println "   PLUS (+1):    alice, world_c, world_f, world_i, world_l, world_o, world_r, world_u, world_x")
    (println "   ERGODIC (0):  bob, world_b, world_e, world_h, world_k, world_n, world_q, world_t, world_w, world_z")
    (println "   MINUS (-1):   world_a, world_d, world_g, world_j, world_m, world_p, world_s, world_v, world_y")
    
    ;; Verify GF(3) conservation
    (let [sum (:total_sum (:gf3_verification manifest))]
      (println (format "\n✅ GF(3) Sum: %d ≡ %d (mod 3) %s"
                       sum
                       (mod sum 3)
                       (if (zero? (mod sum 3)) "✓ CONSERVED" "✗ VIOLATION"))))
    
    ;; Write manifest
    (spit manifest-path (json/generate-string manifest {:pretty true}))
    (println (format "\n📝 Manifest written to: %s" manifest-path))
    
    ;; Count wallets
    (let [existing (count (filter wallet-exists? wallet-names))]
      (println (format "\n🏁 Complete: %d wallets ready" existing)))))

(when (= *file* (System/getProperty "babashka.file"))
  (-main))
