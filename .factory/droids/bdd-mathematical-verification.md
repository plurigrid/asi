---
name: bdd-mathematical-verification
description: BDD-Driven Mathematical Content Verification Skill
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# BDD Mathematical Verification Skill

## Overview

This skill enables **Behavior-Driven Development (BDD)** workflows for mathematics, combining:

1. **Gherkin Specifications**: Plain-text scenario definitions
2. **RSpec Implementation**: Executable Ruby verification code
3. **mathpix-gem Integration**: Automatic LaTeX extraction from images
4. **Pattern Matching**: Syntax-tree validation for mathematical expressions
5. **Iterative Discovery**: Cucumber features guide formula exploration

## Core Components

### 1. Feature Specifications (Gherkin)

```gherkin
Feature: Mathematical Formula Extraction and Verification

  Scenario: Extract LaTeX from mathematical image
    Given I have a mathematical image file "quadratic.png"
    When I extract LaTeX using Mathpix
    Then I should get a LaTeX formula matching the pattern "ax^2 + bx + c"
    And the formula should be registered as an artifact

  Scenario: Verify quadratic formula in standard form
    Given a quadratic formula "x^2 - 5*x + 6"
    When I verify it is in standard form
    Then the coefficients should be [1, -5, 6]
    And it should be factorable as "(x - 2)(x - 3)"

  Scenario Outline: Verify binomial expansion
    Given a binomial expression "<binomial>"
    When I expand it using binomial theorem
    Then the result should match "<expanded>"
    And all terms should be present with correct signs

    Examples:
      | binomial  | expanded                    |
      | (x + 1)^2 | x^2 + 2*x + 1              |
      | (a - b)^3 | a^3 - 3*a^2*b + 3*a*b^2 - b^3 |
      | (2*x + 3)^2 | 4*x^2 + 12*x + 9         |
```

### 2. RSpec Implementation Blocks

```ruby
describe "Mathematical Formula Verification" do

  describe "Formula Extraction" do
    context "with valid mathematical image" do
      it "extracts LaTeX representation" do
        # Extraction step
      end

      it "normalizes notation to standard form" do
        # Normalization step
      end
    end

    context "with multi-page document" do
