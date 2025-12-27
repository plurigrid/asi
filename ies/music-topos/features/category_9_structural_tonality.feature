Feature: Category 9 - Structural Tonality

  Scenario: Detecting an Authentic Cadence
    Given a progression [G Major, C Major] in C Major
    When I analyze the cadence type
    Then it is identified as an "Authentic Cadence"
    And it achieves structural closure

  Scenario: Antecedent and Consequent phrases
    Given an antecedent phrase ending on a Half Cadence (V)
    And a consequent phrase ending on an Authentic Cadence (I)
    When I validate the period structure
    Then the structure is marked as a "Parallel Period"
    And the metric space satisfies triangle inequality across phrase boundaries

  Scenario: Deceptive Cadence subverting expectation
    Given a progression [V, vi]
    When I analyze the tonal resolution
    Then it is identified as a "Deceptive Cadence"
    And the appearance intensity reflects the subversion of expectation
