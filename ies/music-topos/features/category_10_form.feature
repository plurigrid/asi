Feature: Category 10 - Musical Form & Analysis

  Scenario: Sonata Form structure
    Given an Exposition with themes in I and V
    And a Development section exploring the hexatonic cycle
    And a Recapitulation returning themes to the Tonic
    When I validate the large-scale structure
    Then it is identified as a "Sonata Form"
    And the semantic closure confirms consistency across the whole composition

  Scenario: Sectional boundary detection
    Given a transition from a closed period to a developmental passage
    When I analyze the formal morphology
    Then a sectional boundary is detected
    And the metric distance between sections is calculated
