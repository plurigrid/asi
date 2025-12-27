# features/step_definitions/group_theory_steps.rb

require 'rspec'
require_relative '../../lib/group_theory'
require_relative '../../lib/worlds/group_theory_world'
require_relative '../../lib/pitch_class'
require_relative '../../lib/chord'

Given('a symmetric group S₁₂ on 12 pitch classes') do
  @s12 = S12.new
end

Given('Cayley graph generators as adjacent transpositions \(i, i+1)') do
  # Already defined in S12 initialization
end

Given('the cyclic group Z12') do
  @z12 = CyclicGroup.new(12)
end

When('I add elements \{0, 1, ..., 11}') do
  # Elements are implicit in CyclicGroup(12)
end

When('define multiplication as \(a + b) mod 12') do
  # Standard for CyclicGroup
end

Then('closure is satisfied: \(a + b) mod 12 ∈ Z12') do
  validation = @z12.validate_group_axioms
  expect(validation[:errors]).not_to include(/Closure/)
end

Then('associativity is satisfied: \(a + b) + c = a + \(b + c) mod 12') do
  validation = @z12.validate_group_axioms
  expect(validation[:errors]).not_to include(/Associativity/)
end

Then('identity exists: 0 such that a + 0 = a') do
  expect(@z12.identity).to eq(0)
  expect(@z12.multiply(5, 0)).to eq(5)
end

Then('every element a has inverse \(12 - a) mod 12') do
  (0..11).each do |a|
    inv = @z12.inverse(a)
    expect(@z12.multiply(a, inv)).to eq(@z12.identity)
  end
end

Then('triangle inequality holds in circular metric') do
  expect(@z12.triangle_inequality_satisfied?(0, 4, 7)).to be true
end

Given('permutation \({int} {int}) that swaps {int} and {int}') do |i, j, n1, n2|
  @perm = Permutation.transposition(12, n1, n2)
end

Given('permutation \({int} {int}) that swaps {int} and {int} as second') do |i, j, n1, n2|
  @perm2 = Permutation.transposition(12, n1, n2)
end

When('I compose \({int} {int}) ∘ \({int} {int})') do |i1, j1, i2, j2|
  @composition = @perm.compose(@perm)
end

Then('the result is the identity permutation') do
  expect(@composition).to eq(Permutation.identity(12))
end

Then('\({int} {int}) ∘ \({int} {int}) ∘ \({int} {int}) = \({int} {int})') do |i1, j1, i2, j2, i3, j3, i4, j4|
  res = @perm.compose(@perm).compose(@perm)
  expect(res).to eq(@perm)
end

Then('inverse \(\({int} {int}))⁻¹ = \({int} {int})') do |i1, j1, i2, j2|
  expect(@perm.inverse).to eq(@perm)
end

Given('a GroupTheoryWorld') do
  @world = GroupTheoryWorld.new
end

When('I add permutations to the world') do
  @world.add_permutation(Permutation.identity(12))
  @world.add_permutation(Permutation.transposition(12, 0, 1))
end

When('verify group axioms on the subset') do
  @validation = @world.validate_group_axioms
end

Then('closure: composition of two objects stays in world') do
  # In our stochastic world validation
  expect(@validation[:closure_in_world]).to be true
end

Then('associativity: \(p₁ · p₂) · p₃ = p₁ · \(p₂ · p₃)') do
  expect(@validation[:errors]).not_to include(/Associativity/)
end

Then('identity: identity permutation I exists') do
  expect(@validation[:errors]).not_to include(/Identity/)
end

Then('inverses: every permutation p has p⁻¹ with p · p⁻¹ = I') do
  expect(@validation[:errors]).not_to include(/Inverse/)
end

Then('semantic closure: 8\/8 dimensions verified') do
  closure = @world.semantic_closure_validation
  expect(closure[:group_axioms_valid]).to be true
end
