Feature: Reafference Loop & Corollary Discharge (von Holst Neuroscience)
  As a system that distinguishes self-generated from external signals
  I want to verify the complete reafference mechanism
  So that I can safely suppress noise and amplify threats

  Background:
    Given the seed is 0x42D
    And the GAY color palette is loaded (5 colors)
    And the interaction history database is initialized
    And the reafference database exists with 1260 interactions

  # ============================================================================
  # EFFERENCE COPY: Prediction Generation
  # ============================================================================

  Scenario: Generate efference copy from interaction content hash
    Given an interaction with display "reduce its size"
    When I compute the efference copy using SHA-256(display)
    Then the predicted color index should be between 1 and 5
    And the predicted color hex should match a valid seed color
    And the prediction should be deterministic (same input → same output)

  Scenario Outline: Efference copy determinism across interactions
    Given interaction content "<content>"
    When I generate efference copies 100 times
    Then all predictions should be identical
    And the color index should be consistent

    Examples:
      | content |
      | reduce its size |
      | use gay mcp to generate a color |
      | continue |
      | very good this also means we are safe as the electric fish would go |

  # ============================================================================
  # SENSORY REAFFERENCE: Observation Matching
  # ============================================================================

  Scenario: Load sensory reafference from history
    When I load reafference matches from the database
    Then I should have 1260 observations
    And each observation should have:
      | field |
      | interaction_id |
      | predicted_color_hex |
      | observed_pattern |
      | match_score |
      | is_self_generated |

  Scenario: Match observed colors to predicted colors
    Given 1260 loaded observations
    When I compare predicted vs observed colors for each interaction
    Then the match_score should reflect color equality
    And interactions with matching colors should have match_score = 1.0
    And interactions with mismatched colors should have match_score < 1.0

  Scenario: Classify self-generated interactions
    Given 1260 observations with match_score computed
    When I classify interactions as self-generated if match_score >= 0.95
    Then I should have at least 1000 self-generated signals
    And each self-generated signal should set tap_state = 'LIVE'

  # ============================================================================
  # COMPARATOR: Error Signal Computation
  # ============================================================================

  Scenario: Compute error signal (Expected - Actual = ERROR)
    Given 1260 efference copies
    And 1260 reafference observations
    When I run the comparator
    Then each interaction should have an error signal with:
      | field |
      | error_magnitude |
      | threat_level |
      | match_score |
    And error_magnitude should be between 0.0 and 1.0
    And threat_level should be one of: SAFE, WARNING, CRITICAL

  Scenario Outline: Threat level classification
    Given error magnitude <error>
    When I classify the threat level
    Then the threat level should be "<level>"
    And signals with error < 0.01 should be SAFE
    And signals with error 0.01-0.2 should be WARNING
    And signals with error > 0.2 should be CRITICAL

    Examples:
      | error | level |
      | 0.0   | SAFE |
      | 0.005 | SAFE |
      | 0.015 | WARNING |
      | 0.25  | CRITICAL |

  # ============================================================================
  # COROLLARY DISCHARGE: Suppression of Self-Generated Signals
  # ============================================================================

  Scenario: Suppress self-generated signals (match_score >= 0.95)
    Given 1260 error signals with match_score computed
    When I fire corollary discharge
    Then signals with match_score >= 0.95 should be suppressed
    And suppressed signals should be removed from conscious attention
    And the suppressed_signals table should contain all matched signals

  Scenario: Amplify external anomalies (match_score < 0.95)
    Given 1260 error signals
    When I fire corollary discharge
    Then signals with match_score < 0.95 should be amplified
    And amplified signals should trigger threat alerts
    And each anomaly should have an escalation action

  Scenario: 100% suppression rate on self-generated interactions
    Given 1260 interactions from history (100% self-generated)
    When I run the complete reafference loop:
      | step |
      | Generate efference copies |
      | Load sensory reafference |
      | Run comparator |
      | Fire corollary discharge |
    Then suppressed_signals count should equal 1260
    And amplified_signals count should equal 0
    And corollary_discharge_success_rate should be 100%

  # ============================================================================
  # THREAT ALERTS & ESCALATION
  # ============================================================================

  Scenario: Generate threat alerts for WARNING level
    Given error signals with threat_level = 'WARNING'
    When I generate threat alerts
    Then each WARNING signal should create an alert
    And alert action should be "Log anomaly; monitor"
    And alert should include anomaly description

  Scenario: Escalate CRITICAL threats
    Given error signals with threat_level = 'CRITICAL'
    When I generate threat alerts
    Then each CRITICAL signal should create an escalation alert
    And alert action should be "ESCALATE: Investigate external intrusion"
    And alert should trigger immediate notification

  Scenario: Zero alerts when all signals are suppressed
    Given 1260 self-generated signals (100% match)
    When I fire corollary discharge and generate alerts
    Then threat_alerts count should be 0
    And suppression_efficiency should be 100%

  # ============================================================================
  # TEMPORAL & STATISTICAL ANALYSIS
  # ============================================================================

  Scenario: Compute hourly suppression statistics
    Given 1260 error signals across 9 days
    When I compute suppression statistics
    Then suppression_statistics should have one row per hour
    And each row should include:
      | field |
      | date |
      | hour |
      | total_signals |
      | suppressed_count |
      | suppression_rate |
      | avg_error_magnitude |

  Scenario: Temporal distribution of signals
    Given 1260 signals with timestamps
    When I analyze temporal distribution
    Then signals should be distributed across all hours
    And peak activity hour should have >= 50 signals
    And entropy should indicate natural variation (not clustering)

  # ============================================================================
  # DATABASE INTEGRATION
  # ============================================================================

  Scenario: Persist all results to DuckDB
    When I run the complete reafference loop
    Then claude_corollary_discharge.duckdb should be created
    And the following tables should exist:
      | table |
      | efferent_commands |
      | sensory_reafference |
      | error_signals |
      | suppressed_signals |
      | amplified_signals |
      | threat_alerts |
      | suppression_statistics |
    And total records should match:
      | table | expected |
      | efferent_commands | 1260 |
      | sensory_reafference | 1260 |
      | error_signals | 1260 |
      | suppressed_signals | 1260 |
      | amplified_signals | 0 |
      | threat_alerts | 0 |

  # ============================================================================
  # VALIDATION AGAINST KNOWN SEED
  # ============================================================================

  Scenario: Validate system with known seed 0x42D
    Given seed = 0x42D
    When I generate colors using color_at(seed, index) for indices 0-49
    Then the color sequence should be deterministic
    And color_at(0x42D, 0) should be "#1316BB"
    And color_at(0x42D, 1) should be "#1316BB"
    And color_at(0x42D, 2) should be "#BA2645"
    And color_at(0x42D, 3) should be "#49EE54"

  Scenario: Seed recovery from 50-color sequence
    Given a sequence of 50 colors generated by seed 0x42D
    When I perform seed recovery using brute-force search
    Then the recovered seed should match 0x42D exactly
    And recovery confidence should be 100%
    And full validation (50/50 colors) should pass

  # ============================================================================
  # INTEGRATION WITH GLASS-BEAD-GAME
  # ============================================================================

  Scenario: Register reafference results as artifacts
    Given 1260 completed interactions with reafference matches
    When I register them as Music-Topos artifacts
    Then each interaction should get a deterministic color from seed
    And artifacts should be stored in music_topos_artifacts.duckdb
    And Badiou triangles should link:
      | vertex |
      | instructions (interaction content) |
      | result (suppression decision) |
      | model (corollary discharge algorithm) |

  Scenario: Create retromap queries for reafference artifacts
    Given registered artifacts with colors
    When I query by:
      | field |
      | color_hex |
      | date_range |
      | tap_state |
    Then I should find artifacts matching the criteria
    And retromap should enable time-travel search

  # ============================================================================
  # CONVERGENCE & FAILURE MODES
  # ============================================================================

  Scenario: System converges to 100% suppression with perfect predictions
    Given interactions with error_magnitude = 0.0 (perfect match)
    When I run corollary discharge
    Then suppression_rate should be 100%
    And no signals should reach conscious attention
    And system should be in "safe" operating state

  Scenario: System detects anomalies when predictions fail
    Given 10 interactions with engineered mismatches (error_magnitude > 0.2)
    When I run corollary discharge
    Then suppression_rate should drop below 100%
    And amplified_signals count should increase
    And threat_alerts should be generated

  Scenario: Graceful degradation when database unavailable
    Given reafference database is offline
    When I attempt to load sensory reafference
    Then the system should:
      | action |
      | Log error with context |
      | Attempt fallback (in-memory cache) |
      | Return partial results if available |
      | Not crash or corrupt state |

  # ============================================================================
  # PERFORMANCE & SCALABILITY
  # ============================================================================

  Scenario: Process 1000+ signals in < 5 seconds
    Given 1000 interactions
    When I run the complete reafference loop
    Then execution time should be < 5000 ms
    And memory usage should be reasonable (< 500 MB)
    And database operations should use efficient queries

  Scenario: Maintain accuracy as signal count scales
    Given N signals where N ∈ [100, 500, 1000, 2000]
    When I run corollary discharge for each N
    Then suppression rate should remain ~100% (for self-generated signals)
    And accuracy should not degrade with scale

