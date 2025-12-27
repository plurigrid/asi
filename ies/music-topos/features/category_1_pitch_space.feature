Feature: Category 1 - Pitch Space (ℝ/12ℤ as S¹)
  Mathematical foundation: pitch classes form a circle group
  As a music composition system
  I want to operate on pitch classes with topological correctness
  So that transposition and distance metrics are mathematically sound

  Scenario: Create pitch class from MIDI note
    # ELICITATION: System must understand MIDI → pitch class mapping
    # Test will guide us to implement PitchClass class
    Given a MIDI note 60 with name C4
    When I create a pitch class from this MIDI note
    Then the pitch class should be 0 with name C modulo 12

  Scenario: Transposition preserves circle group structure
    # ELICITATION: The system must know that transposition is group action
    # Z¹² under addition mod 12
    Given pitch class 0 (C)
    When I transpose by 5 semitones
    Then I get pitch class 5 (F)
    And transposing 5 by 7 should equal transposing 0 by 12

  Scenario: Circle metric - distance on the pitch circle
    # ELICITATION: ℝ/12ℤ is not a line, it's a CIRCLE
    # distance(a,b) = min(|a-b|, 12-|a-b|)
    Given pitch class 0 (C)
    And pitch class 11 (B)
    When I compute distance on the pitch circle
    Then the distance should be 1 (not 11)

  Scenario: Semantic closure - pitch space is complete
    # VALIDATION: Can the system recognize when pitch space is closed?
    Given a composition with notes [0, 4, 7] (C major triad)
    When I validate semantic closure for pitch space
    Then all notes should be valid pitch classes in Z¹²
    And the system should report pitch_space closure: VALID
