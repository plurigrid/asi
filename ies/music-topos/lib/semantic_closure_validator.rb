# lib/semantic_closure_validator.rb
require_relative 'ontological_validator'

# Wrapper for backward compatibility with Cucumber steps
class SemanticClosureValidator
  def self.validate(composition)
    OntologicalValidator.semantic_closure(composition)
  end
end
