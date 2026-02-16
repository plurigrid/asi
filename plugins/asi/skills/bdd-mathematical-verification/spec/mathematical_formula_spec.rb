#!/usr/bin/env ruby
# -*- coding: utf-8 -*-

"""
RSpec Behavioral Specifications for Mathematical Formula Verification
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

Comprehensive BDD test suite for:
  • Formula extraction from mathematical content
  • Polynomial parsing and AST generation
  • Pattern matching on syntax trees
  • Algebraic equivalence verification
  • Form validation (expanded/factored/simplified)
"""

require 'rspec'
require_relative '../lib/mathematical_formula_extractor'
require_relative '../lib/mathematical_pattern_matching'
require_relative '../lib/mathematical_matchers'

describe 'Mathematical Formula Verification' do

  # ========================================================================
  # Formula Extraction (mathpix-gem Integration)
  # ========================================================================

  describe 'Formula Extraction' do
    let(:extractor) { MathematicalFormulaExtractor.new }

    describe 'Polynomial Formula Parsing' do
      context 'with quadratic polynomial' do
        it 'correctly parses degree and coefficients' do
          ast = extractor.parse_polynomial('x^2 + 2*x + 1')

          expect(ast[:type]).to eq(:polynomial)
          expect(ast[:degree]).to eq(2)
          expect(ast[:coefficients]).to eq([1, 2, 1])
        end

        it 'identifies variables in formula' do
          ast = extractor.parse_polynomial('3*x^2 - 2*y + 5')

          expect(ast[:variables]).to include('x', 'y')
          expect(ast[:variables].size).to eq(2)
        end

        it 'normalizes spacing and operators' do
          formula1 = 'x^2 + 2 x + 1'
          formula2 = 'x^2+2*x+1'

          ast1 = extractor.parse_polynomial(formula1)
          ast2 = extractor.parse_polynomial(formula2)

          expect(ast1[:coefficients]).to eq(ast2[:coefficients])
        end
      end

      context 'with cubic polynomial' do
        it 'correctly identifies higher degree' do
          ast = extractor.parse_polynomial('x^3 - 3*x^2 + 3*x - 1')

          expect(ast[:degree]).to eq(3)
          expect(ast[:terms].count).to eq(4)
        end
      end

      context 'with constant term only' do
        it 'treats constant as degree 0 polynomial' do
          ast = extractor.parse_polynomial('42')

          expect(ast[:degree]).to eq(0)
          expect(ast[:terms].size).to eq(1)
        end
      end
    end

    describe 'Formula Normalization' do
      context 'with LaTeX notation' do
        it 'converts LaTeX macros to standard form' do
          formula = 'x^2 + \\frac{1}{2}x + 1'
          normalized = extractor.normalize_formula(formula)

          expect(normalized).to include('frac')
          expect(normalized).not_to include('\\')
        end

        it 'handles implicit multiplication' do
          formula = '2x + 3y - 5'
          normalized = extractor.normalize_formula(formula)

          expect(normalized).to include('2*x')
          expect(normalized).to include('3*y')
        end
      end

      context 'with whitespace variation' do
        it 'normalizes inconsistent spacing' do
          formula = 'x ^ 2  +  2 * x  +  1'
          normalized = extractor.normalize_formula(formula)

          expect(normalized).not_to include('  ')
          expect(normalized).to match(/\s\+\s/)
        end
      end
    end
  end

  # ========================================================================
  # Pattern Matching on Syntax Trees
  # ========================================================================

  describe 'Mathematical Pattern Matching' do
    let(:matcher) { MathematicalPatternMatching.new }

    describe 'Polynomial Pattern Detection' do
      context 'with standard form pattern' do
        it 'matches "ax^2 + bx + c" structure' do
          formula = 'x^2 + 5*x + 6'
          pattern = 'ax^2 + bx + c'

          expect(matcher.matches_pattern?(formula, pattern)).to be true
        end

        it 'rejects non-matching structure' do
          formula = 'x^3 + 2*x + 1'
          pattern = 'ax^2 + bx + c'

          expect(matcher.matches_pattern?(formula, pattern)).to be false
        end
      end

      context 'with term count matching' do
        it 'verifies exact number of terms' do
          formula = 'x^2 + 3*x - 4'

          expect(matcher.term_count(formula)).to eq(3)
        end

        it 'allows wildcards in pattern' do
          formula = 'x^2 + 2*x + 1'
          pattern = 'x^2 + * + *'

          expect(matcher.matches_pattern?(formula, pattern)).to be true
        end
      end
    end

    describe 'Syntax Tree Traversal' do
      it 'extracts all terms from polynomial' do
        formula = '2*x^3 - 3*x^2 + 4*x - 5'
        terms = matcher.extract_terms(formula)

        expect(terms.count).to eq(4)
        expect(terms[0][:exponent]).to eq(3)
        expect(terms[3][:coefficient]).to eq(-5)
      end

      it 'validates no nested operations for expanded form' do
        expanded = 'x^2 + 2*x + 1'
        nested = '(x + 1)^2'

        expect(matcher.is_expanded?(expanded)).to be true
        expect(matcher.is_expanded?(nested)).to be false
      end
    end
  end

  # ========================================================================
  # Algebraic Equivalence Verification
  # ========================================================================

  describe 'Algebraic Equivalence' do
    let(:verifier) { MathematicalEquivalenceVerifier.new }

    describe 'Canonical Form Comparison' do
      it 'verifies (x+1)^2 ≡ x^2 + 2*x + 1' do
        f1 = '(x + 1)^2'
        f2 = 'x^2 + 2*x + 1'

        expect(verifier.are_equivalent?(f1, f2)).to be true
      end

      it 'verifies commutative property: a+b ≡ b+a' do
        f1 = 'x + 2*y'
        f2 = '2*y + x'

        expect(verifier.are_equivalent?(f1, f2)).to be true
      end

      it 'verifies associative property for polynomials' do
        f1 = '(x + 2) + 3'
        f2 = 'x + (2 + 3)'

        expect(verifier.are_equivalent?(f1, f2)).to be true
      end
    end

    describe 'Simplification Equivalence' do
      it 'recognizes simplified and unsimplified forms as equivalent' do
        unsimplified = 'x + x + x'
        simplified = '3*x'

        expect(verifier.are_equivalent?(unsimplified, simplified)).to be true
      end

      it 'verifies factored and expanded forms' do
        factored = '(x - 2)*(x - 3)'
        expanded = 'x^2 - 5*x + 6'

        expect(verifier.are_equivalent?(factored, expanded)).to be true
      end
    end
  end

  # ========================================================================
  # Form Verification (Expanded/Factored/Simplified)
  # ========================================================================

  describe 'Form Verification' do
    let(:verifier) { MathematicalFormVerifier.new }

    describe 'Expanded Form' do
      it 'recognizes polynomial in expanded form' do
        formula = 'x^2 + 2*x + 1'

        expect(verifier.is_expanded?(formula)).to be true
      end

      it 'rejects polynomial with factored components' do
        formula = '(x + 1)^2'

        expect(verifier.is_expanded?(formula)).to be false
      end

      it 'validates all products are distributed' do
        formula = 'x^2 + x*y + y^2'

        expect(verifier.is_expanded?(formula)).to be true
      end
    end

    describe 'Factored Form' do
      it 'recognizes polynomial in factored form' do
        formula = '(x - 2)*(x - 3)'

        expect(verifier.is_factored?(formula)).to be true
      end

      it 'rejects non-factored polynomial' do
        formula = 'x^2 - 5*x + 6'

        expect(verifier.is_factored?(formula)).to be false
      end
    end

    describe 'Simplified Form' do
      it 'validates no like terms can be combined' do
        formula = '3*x^2 + 2*x + 5'

        expect(verifier.is_simplified?(formula)).to be true
      end

      it 'detects combinable like terms' do
        formula = 'x^2 + 2*x^2 + 3'

        expect(verifier.is_simplified?(formula)).to be false
      end
    end
  end

  # ========================================================================
  # RSpec Custom Matchers
  # ========================================================================

  describe 'RSpec Custom Matchers' do
    context 'when using be_algebraically_equivalent_to' do
      it 'matches equivalent formulas' do
        expect('(x + 1)^2').to be_algebraically_equivalent_to('x^2 + 2*x + 1')
      end

      it 'rejects non-equivalent formulas' do
        expect('x^2 + 1').not_to be_algebraically_equivalent_to('x^2 + 2')
      end
    end

    context 'when using be_in_expanded_form' do
      it 'validates expanded polynomial' do
        expect('x^2 + 2*x + 1').to be_in_expanded_form
      end

      it 'rejects non-expanded form' do
        expect('(x + 1)^2').not_to be_in_expanded_form
      end
    end

    context 'when using be_in_factored_form' do
      it 'validates factored polynomial' do
        expect('(x - 1)*(x - 2)').to be_in_factored_form
      end

      it 'rejects non-factored form' do
        expect('x^2 - 3*x + 2').not_to be_in_factored_form
      end
    end

    context 'when using match_polynomial_pattern' do
      it 'matches polynomial against pattern' do
        expect('x^2 + 5*x + 6').to match_polynomial_pattern('ax^2 + bx + c')
      end

      it 'rejects mismatched patterns' do
        expect('x^3 + 2*x + 1').not_to match_polynomial_pattern('ax^2 + bx + c')
      end
    end
  end

  # ========================================================================
  # Integration: Multiple Features Together
  # ========================================================================

  describe 'Integrated Formula Verification Workflow' do
    let(:extractor) { MathematicalFormulaExtractor.new }
    let(:verifier) { MathematicalEquivalenceVerifier.new }
    let(:form_check) { MathematicalFormVerifier.new }

    it 'extracts, normalizes, and verifies polynomial' do
      # Extract
      raw_formula = 'x ^ 2  +  2x  +  1'
      ast = extractor.parse_polynomial(raw_formula)

      # Verify structure
      expect(ast[:degree]).to eq(2)
      expect(ast[:coefficients]).to eq([1, 2, 1])

      # Verify equivalence
      expanded = 'x^2 + 2*x + 1'
      factored = '(x + 1)^2'
      expect(verifier.are_equivalent?(expanded, factored)).to be true

      # Verify form
      expect(form_check.is_expanded?(expanded)).to be true
      expect(form_check.is_factored?(factored)).to be true
    end

    it 'processes quadratic formula family with parameterized examples' do
      examples = [
        { binomial: '(x + 1)^2', expanded: 'x^2 + 2*x + 1' },
        { binomial: '(x - 2)^2', expanded: 'x^2 - 4*x + 4' },
        { binomial: '(2*x + 1)^2', expanded: '4*x^2 + 4*x + 1' }
      ]

      examples.each do |example|
        expect(verifier.are_equivalent?(
          example[:binomial],
          example[:expanded]
        )).to be true
      end
    end

    it 'validates polynomial in multiple forms' do
      formula_forms = {
        factored: '(x - 1)*(x - 2)',
        expanded: 'x^2 - 3*x + 2',
        simplified: 'x^2 - 3*x + 2'
      }

      # All should be equivalent
      expect(verifier.are_equivalent?(
        formula_forms[:factored],
        formula_forms[:expanded]
      )).to be true

      # Form checks
      expect(form_check.is_factored?(formula_forms[:factored])).to be true
      expect(form_check.is_expanded?(formula_forms[:expanded])).to be true
      expect(form_check.is_simplified?(formula_forms[:simplified])).to be true
    end
  end

  # ========================================================================
  # Error Handling & Edge Cases
  # ========================================================================

  describe 'Error Handling' do
    let(:extractor) { MathematicalFormulaExtractor.new }

    context 'with malformed input' do
      it 'handles empty string gracefully' do
        expect { extractor.parse_polynomial('') }.not_to raise_error
      end

      it 'handles invalid formula syntax' do
        expect { extractor.parse_polynomial('x ++ 2') }.not_to raise_error
      end
    end

    context 'with numeric precision' do
      it 'maintains floating point coefficients' do
        ast = extractor.parse_polynomial('0.5*x^2 + 0.333*x + 0.1')

        expect(ast[:coefficients][0]).to be_within(0.01).of(0.5)
      end
    end
  end

  # ========================================================================
  # Behavior Examples from Gherkin Features
  # ========================================================================

  describe 'Gherkin-Driven Examples' do
    context 'Scenario: Verify quadratic formula in standard form' do
      it 'extracts coefficients for x^2 - 5*x + 6' do
        extractor = MathematicalFormulaExtractor.new
        ast = extractor.parse_polynomial('x^2 - 5*x + 6')

        expect(ast[:coefficients]).to eq([1, -5, 6])
      end

      it 'verifies factorability' do
        verifier = MathematicalEquivalenceVerifier.new
        original = 'x^2 - 5*x + 6'
        factored = '(x - 2)*(x - 3)'

        expect(verifier.are_equivalent?(original, factored)).to be true
      end
    end

    context 'Scenario Outline: Verify binomial expansion' do
      [
        { binomial: '(x + 1)^2', expanded: 'x^2 + 2*x + 1' },
        { binomial: '(a - b)^2', expanded: 'a^2 - 2*a*b + b^2' },
        { binomial: '(2*x + 3)^2', expanded: '4*x^2 + 12*x + 9' }
      ].each do |example|
        it "verifies #{example[:binomial]} expands to #{example[:expanded]}" do
          verifier = MathematicalEquivalenceVerifier.new
          expect(verifier.are_equivalent?(
            example[:binomial],
            example[:expanded]
          )).to be true
        end
      end
    end
  end
end
