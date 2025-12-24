Feature: Category 7 - Polyphonic Voice Leading (SATB)

  Scenario: Minimizing voice motion in SATB writing
    Given a C Major chord in SATB voicing: [E4, C4, G3, C3]
    When I transition to an F Major chord with minimal motion
    Then the Soprano moves from E4 to F4 (1 semitone)
    And the Alto moves from C4 to C4 (0 semitones)
    And the Tenor moves from G3 to A3 (2 semitones)
    And the Bass moves from C3 to F3 (5 semitones)
    And the total voice leading distance is 8 semitones

  Scenario: Detecting parallel fifths and octaves
    Given a progression from C Major to G Major
    When the Soprano and Bass both move by a perfect fifth in the same direction
    Then a parallel fifth violation is reported
    And semantic closure fails on the "transformations_necessary" dimension

  Scenario: SATB Range Validation
    Given a soprano note C6
    When I validate the SATB ranges
    Then an out-of-range error is reported for the Soprano
    And the composition is marked as ontologically invalid
