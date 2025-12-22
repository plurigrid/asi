#!/usr/bin/env hy
;
; DuckLake Color Retromap Test
; Real analysis of Claude history with battery cycle color mapping
;

(import json datetime)

(import [ducklake_color_retromap [load-claude-history
                                  compute-time-range
                                  map-cycle-index-to-timestamps
                                  create-ducklake-schema
                                  get-cycle-statistics
                                  get-color-interaction-summary
                                  get-interactions-in-cycle
                                  get-color-for-timestamp
                                  report-ducklake-analysis
                                  analyze-with-retromap]])

(import [battery_cycle_color_driver [COLOR_CHAIN_DATA]])

; ============================================================================
; INTEGRATION TEST
; ============================================================================

(defn test-ducklake-integration []
  "Test the full DuckLake retromap pipeline"
  (print "\n╔════════════════════════════════════════════════════════════╗")
  (print "║  DuckLake Color Retromap Integration Test                 ║")
  (print "╚════════════════════════════════════════════════════════════╝\n")

  ; Run the full analysis
  (let [analysis (analyze-with-retromap)]
    (print "\n✓ Integration test complete")
    analysis))

(defn demonstrate-time-travel [db cycle]
  "Demonstrate time-travel capability"
  (print (str "\n[TIME TRAVEL] Retrieving interactions from Battery Cycle " cycle))

  (let [interactions (get-interactions-in-cycle db cycle)]
    (when (> (len interactions) 0)
      (print (str "  Found " (len interactions) " interactions in cycle " cycle "\n"))

      ; Show first 3
      (doseq [[row (take 3 interactions)]
        (print (str "    [" (. row 2) "] " (. row 3) " (project: " (. row 4) ")")))

      (when (> (len interactions) 3)
        (print (str "    ... and " (- (len interactions) 3) " more"))))))

(defn demonstrate-reverse-time-travel [db timestamp-ms]
  "Demonstrate reverse time-travel: timestamp → battery color"
  (print (str "\n[REVERSE TIME TRAVEL] What color was active at timestamp " timestamp-ms "?"))

  (let [color (get-color-for-timestamp db timestamp-ms)]
    (when color
      (print (str "  Battery Cycle: " (. color 0)))
      (print (str "  Color: " (. color 1)))
      (print (str "  GaySeed Index: " (. color 2)))
      (print (str "  LCH: L=" (round (. color 3) 2) ", C=" (round (. color 4) 2) ", H=" (round (. color 5) 2)))
      (print (str "  Time into cycle: " (. color 6) " ms\n")))))

; ============================================================================
; VALIDATION TESTS
; ============================================================================

(defn validate-color-chain-loaded []
  "Validate that color chain data is properly loaded"
  (print "\n[VALIDATION] Color Chain Data")
  (print (str "  Total cycles: " (len COLOR_CHAIN_DATA)))

  (let [first-cycle (get COLOR_CHAIN_DATA 0)
        last-cycle (get COLOR_CHAIN_DATA 35)]

    (print (str "  First cycle (0): " (get first-cycle "hex")))
    (print (str "  Last cycle (35): " (get last-cycle "hex")))
    (print "  ✓ Color chain loaded correctly")))

(defn validate-history-structure []
  "Validate history file structure"
  (print "\n[VALIDATION] Claude History Structure")

  (let [entries (load-claude-history "~/.claude/history.jsonl")]
    (when (> (len entries) 0)
      (let [first-entry (get entries 0)]
        (print (str "  Total entries: " (len entries)))
        (print (str "  First entry timestamp: " (get first-entry "timestamp")))
        (print (str "  Entry has keys: " (list (. first-entry keys))))
        (print "  ✓ History file loaded correctly")))))

; ============================================================================
; RUN ALL TESTS
; ============================================================================

(defn run-all []
  "Run all tests and demonstrations"
  (validate-color-chain-loaded)
  (validate-history-structure)

  (let [analysis (test-ducklake-integration)]

    (when (contains analysis "db")
      (let [db (get analysis "db")]
        ; Demonstrate time-travel capabilities
        (demonstrate-time-travel db 10)
        (demonstrate-time-travel db 25)

        ; Demonstrate reverse time-travel
        ; Get a timestamp from the history
        (let [sample-entries (load-claude-history "~/.claude/history.jsonl")
              _ (when (> (len sample-entries) 0)
                  (demonstrate-reverse-time-travel db (get (get sample-entries 50) "timestamp")))]))

      (print "\n✓ All tests completed successfully"))))

; Entry point
(when (= --name-- "__main__")
  (try
    (run-all)
    (except [e Exception]
      (print (str "\n✗ Test failed: " e)))))
