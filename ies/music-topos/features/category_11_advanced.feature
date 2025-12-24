Feature: Category 11 - Advanced Topics (Spectral & Beyond)

  Scenario: Generating a harmonic series
    Given a fundamental frequency of 130.81 Hz (C3)
    When I generate 8 partials
    Then the frequencies are integer multiples of the fundamental
    And the MIDI notes correspond to the natural overtone series

  Scenario: Timbre space navigation in SpectralWorld
    Given two harmonic spectra S1 and S2
    When I compute the distance in SpectralWorld
    Then the distance is the difference between their fundamental frequencies
    And triangle inequality is enforced on the spectral manifold
