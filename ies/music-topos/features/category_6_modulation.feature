Feature: Category 6 - Modulation & Transposition

  Background:
    Given modulation is a change of key center
    And transposition is a pitch shift by fixed interval
    And chromatic distance measures key relationships

  Scenario: Transposition shifts all pitches by interval
    Given a chord C Major = [C, E, G]
    When I transpose by 2 semitones (up to D)
    Then the result is [D, F#, A] (D Major)
    And all intervals preserved (major triad)
    And transposition T₊₂ is a group operation

  Scenario: Chromatic distance between keys
    Given two keys and chromatic scale
    When I measure distance using circle metric:
      | Key1 | Key2 | Chromatic Distance |
      | C    | D    | 2                  |
      | C    | G    | 7 (or 5 reverse)   |
      | C    | C#   | 1                  |
      | C    | F    | 5 (or 7 reverse)   |
    Then distance uses shortest path on chromatic circle
    And d(C, C) = 0
    And d(C, D) = d(D, C) (symmetric)

  Scenario: Circle of fifths structure
    Given circle of fifths: C - G - D - A - E - B - F# - C# - G# - D# - A# - F - C
    When I measure distance in circle of fifths:
      | Key1 | Key2 | CoF Distance |
      | C    | G    | 1            |
      | C    | D    | 2            |
      | C    | F    | 1 (reverse)  |
      | C    | B    | 5 (or 7 rev) |
    Then CoF distance indicates harmonic closeness
    And adjacent keys in CoF differ by 1 sharp/flat
    And CoF cycle is musically natural

  Scenario: Pivot chord modulation
    Given modulation from C Major to G Major
    When I find shared chord:
      | Key      | Chords          |
      | C Major  | I, II, III, IV, V, VI, VII |
      | G Major  | I, II, III, IV, V, VI, VII |
      | Shared   | D minor         |
    Then pivot chord (D minor = ii in C, iv in G)
    And modulation is smooth (shared harmony)
    And voice leading is parsimonious

  Scenario: Direct modulation (key shift)
    Given immediate key change without pivot
    When modulation is direct:
      | From | To  | Type   | Distance |
      | C    | D   | Direct | 2        |
      | C    | F#  | Direct | 6        |
    Then no shared chord between keys
    And requires more abrupt transition
    And distance indicates modulation effort

  Scenario: Triangle inequality in key space
    Given three keys: C, G, D
    When I verify triangle inequality:
      | d(C,G) | d(G,D) | d(C,D) | Satisfied? |
      | 1      | 1      | 2      | Yes (2≤2)  |
    Then triangle inequality holds in key space
    And modulation paths satisfy metric axioms

  Scenario: Modulation path: sequence of keys
    Given modulation path C → G → D → A → E
    When I analyze the path:
      | Step | From | To  | Distance | CoF Distance |
      | 1    | C    | G   | 7/5      | 1            |
      | 2    | G    | D   | 7/5      | 1            |
      | 3    | D    | A   | 7/5      | 1            |
      | 4    | A    | E   | 7/5      | 1            |
    Then path follows circle of fifths (natural progression)
    And total distance = 4 steps
    And path can return to origin (closed modulation)

  Scenario: Common tone retention in modulation
    Given two keys sharing scale degrees
    When I find common tones:
      | From Key | To Key | Common Tones | Distance |
      | C Major  | A min  | C, E         | 1        |
      | C Major  | F Maj  | C, F         | 1        |
      | C Major  | G Maj  | G            | 2        |
      | C Major  | D Maj  | D            | 2        |
    Then common tones minimize voice leading
    And distance reflects number of shared notes
    And modulation type chosen by common tone distance

  Scenario: ModulationWorld with multiple keys
    Given a ModulationWorld
    When I add keys and modulation paths:
      | Key | Added |
      | C   | Yes   |
      | G   | Yes   |
      | D   | Yes   |
      | A   | Yes   |
    And verify metric space properties
    Then all triangle inequalities satisfied
    And modulation closure verified (8 dimensions)
    And world ready for next category (voice leading)

  Scenario: Semantic closure for modulation
    Given 8-dimensional closure requirement
    When validating modulation composition:
      | Dimension              | Check              |
      | pitch_space            | Keys in 12-tone    |
      | chord_space            | Triads in keys     |
      | metric_valid           | Triangle ineq.     |
      | appearance             | Keys present       |
      | transformations_necessary | Transposition rules |
      | consistent             | No contradictions  |
      | existence              | Modulations exist  |
      | complete               | Paths close        |
    Then all 8 dimensions verified
    And modulation world coherent
