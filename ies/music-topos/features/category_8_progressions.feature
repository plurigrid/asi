Feature: Category 8 - Harmony & Progressions

  Scenario: Functional progression cycle
    Given a progression [I, IV, V, I] in C Major
    When I analyze the harmonic functions
    Then the sequence is [Tonic, Subdominant, Dominant, Tonic]
    And the progression is marked as functionally closed

  Scenario: Roman numeral analysis
    Given a chord [G, B, D] in the key of C Major
    When I perform Roman numeral analysis
    Then the result is "V"
    And its function is identified as Dominant

  Scenario: Secondary Dominant identification
    Given a chord [D, F#, A, C] in C Major
    When I check for secondary functions
    Then it is identified as "V/V" (Dominant of the Dominant)
    And it fulfills the Subdominant role in the primary key
