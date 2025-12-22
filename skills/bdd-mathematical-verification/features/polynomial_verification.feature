Feature: Mathematical Formula Verification via BDD

  As a mathematician
  I want to verify polynomial formulas through executable specifications
  So that I can ensure mathematical correctness through behavioral tests

  Background:
    Given the mathematical extractor is initialized
    And the pattern matching engine is available
    And the equivalence verifier is configured

  # ============================================================================
  # Scenario 1: Basic Polynomial Parsing
  # ============================================================================

  Scenario: Extract and parse quadratic formula
    Given a quadratic formula "x^2 + 2*x + 1"
    When I parse the formula to AST
    Then the degree should be 2
    And the coefficients should be [1, 2, 1]
    And the variables should include "x"
    And the formula should have exactly 3 terms

  Scenario: Normalize formula with spacing variations
    Given a formula with spacing "x ^ 2  +  2 x  +  1"
    When I normalize the formula
    Then it should match the pattern "x^2 + 2*x + 1"

  # ============================================================================
  # Scenario 2: Polynomial Form Verification
  # ============================================================================

  Scenario: Verify polynomial in standard form
    Given a quadratic formula "x^2 - 5*x + 6"
    When I verify it is in expanded form
    Then the verification should pass
    And the coefficients should be [1, -5, 6]
    And it should have 3 distinct terms

  Scenario: Reject polynomial with factored components
    Given a factored expression "(x - 2)*(x - 3)"
    When I verify it is in expanded form
    Then the verification should fail
    But it should be in factored form

  # ============================================================================
  # Scenario 3: Algebraic Equivalence
  # ============================================================================

  Scenario: Verify binomial square expansion
    Given a binomial expression "(x + 1)^2"
    When I expand it using algebraic rules
    Then it should be equivalent to "x^2 + 2*x + 1"
    And both forms should have the same canonical representation

  Scenario: Verify quadratic factorization
    Given an expanded quadratic "x^2 - 5*x + 6"
    When I check equivalence with factored form "(x - 2)*(x - 3)"
    Then they should be algebraically equivalent
    And the factored form should have exactly 2 factors

  # ============================================================================
  # Scenario 4: Parameterized Examples - Binomial Family
  # ============================================================================

  Scenario Outline: Verify binomial expansion patterns
    Given a binomial expression "<binomial>"
    When I apply the binomial theorem
    Then the expanded form should be "<expanded>"
    And each term should have the correct sign
    And the degree should be <degree>

    Examples: Basic binomials
      | binomial   | expanded                  | degree |
      | (x + 1)^2  | x^2 + 2*x + 1            | 2      |
      | (x - 1)^2  | x^2 - 2*x + 1            | 2      |
      | (x + 2)^2  | x^2 + 4*x + 4            | 2      |

    Examples: Coefficient variations
      | binomial    | expanded                 | degree |
      | (2*x + 1)^2 | 4*x^2 + 4*x + 1         | 2      |
      | (x + 3)^2   | x^2 + 6*x + 9           | 2      |
      | (3*x - 2)^2 | 9*x^2 - 12*x + 4        | 2      |

    Examples: Cubic binomials
      | binomial   | expanded                        | degree |
      | (x + 1)^3  | x^3 + 3*x^2 + 3*x + 1         | 3      |
      | (x - 2)^3  | x^3 - 6*x^2 + 12*x - 8        | 3      |

  # ============================================================================
  # Scenario 5: Pattern Matching
  # ============================================================================

  Scenario: Match polynomial against standard form pattern
    Given a polynomial formula "x^2 + 5*x + 6"
    When I match it against the pattern "ax^2 + bx + c"
    Then the pattern should match
    And coefficient 'a' should be 1
    And coefficient 'b' should be 5
    And coefficient 'c' should be 6

  Scenario: Pattern matching with wildcards
    Given a polynomial formula "x^2 + 2*x + 1"
    When I match it against pattern "x^2 + * + *"
    Then the pattern should match
    And the wildcard values should be [2, 1]

  # ============================================================================
  # Scenario 6: Simplification Verification
  # ============================================================================

  Scenario: Verify simplified polynomial has no like terms
    Given a polynomial "3*x^2 + 2*x + 5"
    When I check if it is simplified
    Then it should be in simplified form
    And no like terms should be combinable

  Scenario: Detect combinable like terms
    Given a polynomial "x^2 + 2*x^2 + 3"
    When I check if it is simplified
    Then it should not be in simplified form
    And the like terms "x^2 + 2*x^2" should be combinable to "3*x^2"

  # ============================================================================
  # Scenario 7: Multi-Variable Polynomials
  # ============================================================================

  Scenario: Parse polynomial with multiple variables
    Given a polynomial "3*x^2 + 2*x*y + y^2"
    When I parse the formula
    Then the variables should be ["x", "y"]
    And the degree should be 2
    And all terms should be properly parsed

  # ============================================================================
  # Scenario 8: Mathematical Content Extraction (mathpix-gem)
  # ============================================================================

  @integration
  Scenario: Extract LaTeX from mathematical image
    Given I have a mathematical image file "quadratic.png"
    When I extract LaTeX using Mathpix API
    Then I should get a valid LaTeX formula
    And the formula should match pattern "^.*x.*\+.*$"
    And the extraction confidence should be above 0.85

  @integration
  Scenario: Extract formulas from PDF document
    Given I have a PDF document "mathematics_textbook.pdf"
    When I extract all formulas from the document
    Then I should find multiple mathematical formulas
    And each formula should be normalized
    And all formulas should be indexed by page number

  # ============================================================================
  # Scenario 9: Integration with Music-Topos System
  # ============================================================================

  @music-topos
  Scenario: Register verified formula as artifact
    Given a verified quadratic formula "x^2 - 5*x + 6"
    When I register it as a Music-Topos artifact
    Then it should receive a unique artifact ID
    And it should be assigned a GaySeed color deterministically
    And it should be stored in the provenance database
    And the formula should be searchable via retromap

  @music-topos
  Scenario: Link formula to Glass-Bead-Game synthesis
    Given a verified polynomial formula
    And a Badiou triangle from Glass-Bead-Game
    When I create a synthesis link
    Then the formula should be connected to the triangle
    And the connection should have the triangle's color
    And the relationship should be bidirectional

  # ============================================================================
  # Scenario 10: Error Handling
  # ============================================================================

  Scenario: Handle malformed formula gracefully
    Given a malformed formula "x ++ 2"
    When I attempt to parse it
    Then it should handle the error gracefully
    And return an error description
    And not crash the system

  Scenario: Handle empty input
    Given an empty formula string ""
    When I attempt to parse it
    Then it should return empty AST
    And not raise an exception

  # ============================================================================
  # Scenario 11: Caching and Performance
  # ============================================================================

  @performance
  Scenario: Cache extraction results for repeated formulas
    Given a mathematical formula "x^2 + 2*x + 1"
    When I extract it the first time
    And I extract it the second time
    Then the second extraction should use cached result
    And the execution time should be significantly faster

  # ============================================================================
  # Scenario 12: Complex Formula Families
  # ============================================================================

  @complex
  Scenario Outline: Verify polynomial families with parameter ranges
    Given a parameterized polynomial "<template>"
    When I generate instances with "<parameters>"
    Then all instances should be valid polynomials
    And they should follow the template pattern
    And their degrees should be <expected_degree>

    Examples: Linear families
      | template      | parameters           | expected_degree |
      | n*x + c       | n=1..3, c=0..5      | 1               |
      | x + c         | c=-5..5             | 1               |

    Examples: Quadratic families
      | template         | parameters          | expected_degree |
      | n*x^2 + x + 1    | n=1..5             | 2               |
      | x^2 + n*x + 1    | n=-3..3            | 2               |
