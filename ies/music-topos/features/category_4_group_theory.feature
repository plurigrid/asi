Feature: Category 4 - Group Theory Extensions (S₁₂)

  Background:
    Given a symmetric group S₁₂ on 12 pitch classes
    And Cayley graph generators as adjacent transpositions (i, i+1)

  Scenario: Cyclic Group ℤ/12ℤ is a subgroup of S₁₂
    Given the cyclic group Z12
    When I add elements {0, 1, ..., 11}
    And define multiplication as (a + b) mod 12
    Then closure is satisfied: (a + b) mod 12 ∈ Z12
    And associativity is satisfied: (a + b) + c = a + (b + c) mod 12
    And identity exists: 0 such that a + 0 = a
    And every element a has inverse (12 - a) mod 12
    And triangle inequality holds in circular metric

  Scenario: Permutation composition is group multiplication
    Given permutation (0 1) that swaps 0 and 1
    And permutation (1 2) that swaps 1 and 2
    When I compose (0 1) ∘ (0 1)
    Then the result is the identity permutation
    And (0 1) ∘ (0 1) ∘ (0 1) = (0 1)
    And inverse ((0 1))⁻¹ = (0 1)

  Scenario: Cayley graph distance metric in S₁₂
    Given permutations p1, p2, p3 in S₁₂
    When I compute Cayley distance using BFS
    And generators = adjacent transpositions {(0 1), (1 2), ..., (10 11)}
    Then d(identity, (0 1)) = 1
    And d(identity, (0 1)(1 2)) = 2
    And d(p1, p1) = 0
    And d(p1, p2) >= 0
    And d(p1, p2) = d(p2, p1)

  Scenario: Triangle inequality in Cayley distance
    Given three permutations: p_a, p_b, p_c in S₁₂
    When I compute Cayley distances d_ab, d_bc, d_ac
    Then d_ac <= d_ab + d_bc always holds
    And equality holds only when p_b is on shortest path from p_a to p_c

  Scenario: Voice leading under permutation group action
    Given a chord C Major = [C(0), E(4), G(7)]
    And a transposition permutation (0 4) that swaps C and E
    When I apply (0 4) to the chord
    Then the result is [E(4), C(0), G(7)]
    And voice leading distance = |0-4| + |4-0| + |7-7| = 8 semitones

  Scenario: Group axioms in GroupTheoryWorld
    Given a GroupTheoryWorld
    When I add permutations to the world
    And verify group axioms on the subset
    Then closure: composition of two objects stays in world
    And associativity: (p₁ · p₂) · p₃ = p₁ · (p₂ · p₃)
    And identity: identity permutation I exists
    And inverses: every permutation p has p⁻¹ with p · p⁻¹ = I
    And semantic closure: 8/8 dimensions verified

  Scenario: Hamiltonian path in S₁₂ for optimal testing
    Given S₁₂ with |S₁₂| = 479,001,600 permutations
    When I need to test triangle inequality on sample
    Then I use Hamiltonian path in Cayley graph
    And this ensures all edges of graph are traversed exactly once
    And sample efficiency is maximized
    And I test exactly |generators| × |path_length| permutation pairs

  Scenario: BDD test with human interaction for failures
    Given a test that might fail due to implementation complexity
    When the test fails
    Then the system should:
      | Action                              | Trigger         |
      | Report specific assertion failure   | Test fails      |
      | Show expected vs actual values      | Unexpected path |
      | Suggest next debugging step         | Multiple paths  |
      | Allow human to modify test strategy | Complex domain  |
      | Continue with alternative approach  | Human feedback  |

  Scenario: Semantic closure validation for group theory
    Given 8-dimensional semantic closure requirement:
      | Dimension              | Verification                    |
      | pitch_space            | Objects are in ℝ/12ℤ           |
      | chord_space            | Objects form valid chords       |
      | metric_valid           | Triangle inequality satisfied   |
      | appearance             | Objects present in world        |
      | transformations_necessary | Operations preserve structure |
      | consistent             | No contradictions               |
      | existence              | Objects justified by rules      |
      | complete               | Closure under all operations    |
    When I validate a composition with group operations
    Then all 8 dimensions must pass
    And composition exists in the world
