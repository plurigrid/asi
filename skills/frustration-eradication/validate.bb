#!/usr/bin/env bb
;; Frustration Eradication Validator
;; Babashka script for pre-response validation
;; GF(3) Trit: -1 (VALIDATOR)

(ns frustration.validate
  (:require [clojure.string :as str]
            [babashka.fs :as fs]
            [cheshire.core :as json]))

;; ═══════════════════════════════════════════════════════════════
;; FRUSTRATION PATTERNS (ranked by persistence score, lower = worse)
;; ═══════════════════════════════════════════════════════════════

(def frustration-index
  [{:id 1 :name "banned-voices" :persistence 2
    :pattern #"(?i)say\s+-v\s+(Daniel|Albert|Bad News|Bells|Boing|Bubbles|Cellos|Zarvox)"
    :message "❌ Banned voice detected"}
   
   {:id 2 :name "subagent-bypass" :persistence 2
    :pattern #"(?i)(I'll implement instead of subagents|I'll do this (sequentially|myself))"
    :message "❌ Subagent bypass detected - use Task tool"}
   
   {:id 3 :name "derive-resource-account" :persistence 3
    :pattern #"derive.resource.account.address.*wallet"
    :message "❌ derive-resource-account-address used for wallet"}
   
   {:id 4 :name "web-search-fallback" :persistence 3
    :pattern #"(?<!mcp__exa__)web_search"
    :message "❌ web_search used instead of Exa MCP"}
   
   {:id 5 :name "sequential-default" :persistence 4
    :pattern #"(?i)(sequentially|one by one|step by step)"
    :message "⚠️ Sequential execution - consider parallelization"}
   
   {:id 6 :name "verbose-response" :persistence 4
    :check :line-count
    :max-lines 4
    :message "⚠️ Response exceeds 4 lines"}
   
   {:id 7 :name "gf3-violation" :persistence 5
    :check :gf3-sum
    :message "❌ GF(3) conservation violated: Σ trits ≠ 0 (mod 3)"}
   
   {:id 8 :name "unwanted-comments" :persistence 5
    :pattern #"//\s*(TODO|FIXME|NOTE|HACK|XXX|This|Here|We)"
    :message "⚠️ Unwanted code comments detected"}])

;; ═══════════════════════════════════════════════════════════════
;; VALIDATION FUNCTIONS
;; ═══════════════════════════════════════════════════════════════

(defn validate-pattern
  "Check if text matches a banned pattern."
  [text {:keys [pattern message]}]
  (when (and pattern (re-find pattern text))
    {:violation true :message message}))

(defn validate-line-count
  "Check response verbosity."
  [text {:keys [max-lines message]}]
  (let [lines (->> (str/split-lines text)
                   (remove str/blank?)
                   (remove #(str/starts-with? % "```"))
                   count)]
    (when (> lines (or max-lines 4))
      {:violation true 
       :message (str message " (got " lines " lines)")})))

(defn validate-gf3
  "Check GF(3) conservation."
  [trits]
  (let [sum (reduce + 0 trits)]
    (when (not= 0 (mod sum 3))
      {:violation true 
       :message (str "GF(3) violation: sum=" sum " mod 3=" (mod sum 3))})))

(defn validate-all
  "Run all frustration checks on text."
  [text & {:keys [trits]}]
  (let [results (for [check frustration-index]
                  (cond
                    (:pattern check)
                    (validate-pattern text check)
                    
                    (= :line-count (:check check))
                    (validate-line-count text check)
                    
                    (= :gf3-sum (:check check))
                    (when trits (validate-gf3 trits))
                    
                    :else nil))]
    (filter :violation results)))

;; ═══════════════════════════════════════════════════════════════
;; SKILL SCANNER
;; ═══════════════════════════════════════════════════════════════

(defn scan-skill-file
  "Scan a skill file for violations."
  [path]
  (when (fs/exists? path)
    (let [content (slurp (str path))
          violations (validate-all content)]
      (when (seq violations)
        {:file (str path)
         :violations violations}))))

(defn scan-all-skills
  "Scan all skills for frustration patterns."
  []
  (let [skill-dirs [(fs/expand-home "~/.claude/skills")
                    (fs/expand-home "~/.agents/skills")]
        skill-files (mapcat #(fs/glob % "**/*.md") skill-dirs)]
    (->> skill-files
         (map scan-skill-file)
         (filter some?)
         vec)))

;; ═══════════════════════════════════════════════════════════════
;; APPROVED VOICES
;; ═══════════════════════════════════════════════════════════════

;; ALL skills should use "_" - say-narration resolves the voice
;; Non-English voices speaking English are preferred
;; Novelty voices allowed for effects (Bells, Boing, etc.)
(def approved-voices
  #{"_" "Alice (Enhanced)" "Emma (Enhanced)" "Federica (Enhanced)" "Paola (Enhanced)"
    "Anna (Premium)" "Amélie (Premium)" "Yuna (Premium)" "Milena" "Tingting"
    "Bells" "Boing" "Bad News" "Good News" "Zarvox" "Whisper"})  ; novelty OK

(def banned-voices
  ;; All native English voices are banned
  #{"Samantha" "Samantha (Enhanced)" "Ava" "Ava (Enhanced)" "Ava (Premium)"
    "Allison (Enhanced)" "Nathan (Enhanced)" "Evan (Enhanced)" "Nicky (Enhanced)"
    "Noelle (Enhanced)" "Karen" "Daniel" "Moira" "Tessa" "Fiona" "Alex"})

(defn validate-voice
  "Check if voice is approved."
  [voice]
  (cond
    (banned-voices voice) {:violation true :message (str "❌ BANNED: " voice)}
    (approved-voices voice) {:ok true :voice voice}
    :else {:warning true :message (str "⚠️ Unknown voice: " voice)}))

;; ═══════════════════════════════════════════════════════════════
;; CLI
;; ═══════════════════════════════════════════════════════════════

(defn -main [& args]
  (let [cmd (first args)]
    (case cmd
      "check" 
      (let [text (slurp *in*)
            violations (validate-all text)]
        (if (seq violations)
          (do (doseq [v violations]
                (println (:message v)))
              (System/exit 1))
          (println "✅ No frustration patterns detected")))
      
      "scan"
      (let [results (scan-all-skills)]
        (if (seq results)
          (do (println (json/generate-string results {:pretty true}))
              (System/exit 1))
          (println "✅ All skills clean")))
      
      "voice"
      (let [voice (second args)
            result (validate-voice voice)]
        (println (if (:violation result)
                   (:message result)
                   (str "✅ Voice approved: " voice))))
      
      ;; Default: show help
      (println "Usage: validate.bb <check|scan|voice> [args]"))))

(when (= *file* (System/getProperty "babashka.file"))
  (apply -main *command-line-args*))
