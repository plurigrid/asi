Feature: Category 5 - Harmonic Function Analysis (T/S/D)

  Background:
    Given harmonic functions are three elements: T (Tonic), S (Subdominant), D (Dominant)
    And they form a closed cycle: T → S → D → T
    And the metric is functional distance (1 for valid transitions, >1 for unusual)

  Scenario: Three harmonic functions in any key
    Given key is C Major
    When I analyze chord roots:
      | Root | Function       |
      | C    | Tonic (T)      |
      | D    | Subdominant (S)|
      | E    | Subdominant (S)|
      | F    | Subdominant (S)|
      | G    | Dominant (D)   |
      | A    | Subdominant (S)|
      | B    | Dominant (D)   |
    Then each root maps to exactly one function
    And the mapping is consistent across the key

  Scenario: Valid functional progressions form a cycle
    Given the functional cycle T → S → D → T
    When I define valid transitions:
      | From           | To             | Distance |
      | Tonic          | Subdominant    | 1        |
      | Subdominant    | Dominant       | 1        |
      | Dominant       | Tonic          | 1        |
    And triangle inequality in functional space:
      | From   | Through | To     | Formula         |
      | T      | S       | D      | d(T,D) ≤ d(T,S)+d(S,D) |
      | T      | S       | T      | d(T,T) ≤ d(T,S)+d(S,T) |
      | D      | T       | S      | d(D,S) ≤ d(D,T)+d(T,S) |
    Then all transitions are valid
    And triangle inequality holds for all paths

  Scenario: Authentic cadence (V → I) creates closure
    Given a progression ending with dominant to tonic
    When the last two chords are V and I
    Then the cadence type is "authentic"
    And the progression is musically closed (resolves)
    And tonic is the final resting point

  Scenario: Plagal cadence (IV → I) creates closure
    Given a progression with subdominant to tonic ending
    When the final two chords are IV and I
    Then the cadence type is "plagal"
    And the progression is closed
    And tonic is reached (but from subdominant, not dominant)

  Scenario: Deceptive cadence (V → vi) breaks expectation
    Given a progression expecting V → I resolution
    When the actual progression is V → vi instead
    Then the cadence type is "deceptive"
    And the final chord is NOT tonic
    And this violates typical functional expectation

  Scenario: Functional closure requires both T and D
    Given a chord progression
    When I check functional closure:
      | Requirement     | Must Have |
      | At least Tonic  | Yes       |
      | At least Dominant | Yes       |
      | All three present | No (optional) |
    Then the progression is musically complete
    And it satisfies minimal harmonic closure

  Scenario: Unusual progressions have distance > 1
    Given functional progressions
    When I evaluate:
      | Progression | Distance | Reason              |
      | T → S → D → T | 1, 1, 1  | Valid cycle         |
      | T → D       | 2        | Skips subdominant   |
      | D → S       | 2        | Backwards motion    |
      | S → T       | 2        | No dominant closure |
    Then distances > 1 indicate unusual or deceptive practice
    And composer must justify distance > 1

  Scenario: Harmonic rhythm: frequency of functional changes
    Given a chord progression with chords
    When I analyze harmonic rhythm:
      | Measure | Chords     | Functions  | Changes |
      | 1       | I, I, IV   | T, T, S    | 1       |
      | 2       | IV, V, V   | S, D, D    | 1       |
      | 3       | I          | T          | 1       |
    Then harmonic_rhythm_ratio = changes / total_chords
    And ratio < 1.0 (not every chord changes function)
    And ratio indicates harmonic density

  Scenario: HarmonicFunctionWorld validates progressions
    Given a HarmonicFunctionWorld in C Major
    When I add chord progressions to world
    And validate each progression:
      | Progression | Valid? | Errors        |
      | I-IV-V-I    | Yes    | None          |
      | I-V-I       | No     | Skips S       |
      | I-IV-VII-I  | No     | Invalid chord |
    Then world accepts/rejects based on rules
    And unusual progressions are flagged
    And metric distance reflects unusuality

  Scenario: Semantic closure (8 dimensions) for harmonic function
    Given 8-dimensional closure requirement
    When I validate a composition:
      | Dimension              | Validation                |
      | pitch_space            | All notes in octave range |
      | chord_space            | All chords valid in key   |
      | metric_valid           | Triangle inequality       |
      | appearance             | Functions present in world|
      | transformations_necessary | Rules enforced         |
      | consistent             | No function contradictions|
      | existence              | Progressions have meaning |
      | complete               | Harmonic closure (T,D)    |
    Then all 8 must pass
    And composition exists in harmonic function world
    And it's ready for next category (modulation)

  Scenario: BDD with human feedback for unexpected progressions
    Given a composition with unusual functional progression
    When analysis shows distance > 1
    Then system reports:
      | Info               | Value              |
      | Expected function  | Subdominant        |
      | Actual function    | Dominant           |
      | Distance           | 2                  |
      | Reason             | Skips preparation  |
    And suggests:
      | Option | Action                             |
      | 1      | Accept (composer's choice)         |
      | 2      | Add missing subdominant            |
      | 3      | Modify analysis (different key?)   |
      | 4      | Continue with justification        |
    And waits for human input
    And continues based on human decision
