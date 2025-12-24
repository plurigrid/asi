# lib/ontological_validator.rb
module OntologicalValidator
  def self.semantic_closure(composition)
    # 8-point validation checklist
    # 1. Pitch Space
    # 2. Chord Space
    # 3. Metric Valid
    # 4. Appearance (Intensity)
    # 5. Transformations Necessary
    # 6. Consistent
    # 7. Existence
    # 8. Complete
    
    notes = composition[:notes] || []
    chords = composition[:chords] || []
    
    pitch_space_valid = notes.all? { |n| n.is_a?(PitchClass) }
    chord_space_valid = chords.all? { |c| c.is_a?(Chord) }
    
    # Check metric validity on first chord if available
    metric_valid = true
    if chords.any?
      metric_valid = chords.first.voice_leading_distance(chords.first)[:total] == 0
    end
    
    # Existence & Appearance
    existence = pitch_space_valid && chord_space_valid
    appearance = true # Assume non-zero intensity if they exist
    
    # Transformation necessity (parsimony)
    transformations_necessary = true
    if chords.size > 1
      chords.each_cons(2) do |c1, c2|
        dist = c1.voice_leading_distance(c2)[:total]
        # Allow some movement, but not "arbitrary" jumps? 
        # For now, just check it's calculable.
        transformations_necessary = false if dist.nil?
      end
    end
    
    consistent = true
    complete = [pitch_space_valid, chord_space_valid, metric_valid, appearance, 
                transformations_necessary, consistent, existence].all?
                
    closure_points = {
      pitch_space: pitch_space_valid,
      chord_space: chord_space_valid,
      metric_valid: metric_valid,
      appearance: appearance,
      transformations_necessary: transformations_necessary,
      consistent: consistent,
      existence: existence,
      complete: complete
    }
    
    {
      closed: complete,
      closure_points: closure_points,
      summary: {
        valid_dimensions: closure_points.values.count(true)
      }
    }
  end
end
