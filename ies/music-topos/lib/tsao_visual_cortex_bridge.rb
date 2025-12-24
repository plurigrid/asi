# lib/tsao_visual_cortex_bridge.rb
#
# DORIS TSAO VISUAL CORTEX BRIDGE
# ═════════════════════════════════════════════════════════════════════════════
#
# Maps visual cortex organization (Tsao's face processing discoveries)
# onto bidirectional skill traversal architecture.
#
# Architecture:
# ┌─────────────────────────────────────────────────────────┐
# │  Face Processing Ecosystem (Consciousness as Living)    │
# ├─────────────────────────────────────────────────────────┤
# │                                                         │
# │  Prefrontal (Behavioral Goal Layer)                   │
# │         ↕ bidirectional modulation                    │
# │  IT/TEO (Face Recognition Patches)                    │
# │         ↕ bidirectional integration                   │
# │  V2/V4 (Feature Selectivity)                          │
# │         ↕ bidirectional feature gating                │
# │  V1 (Simple Cell Detectors)                           │
# │         ↓                                              │
# │  Retinal Input (Stimulus)                             │
# │                                                         │
# │  IRREDUCIBLE: All layers coupled bidirectionally      │
# │  ALIVE: When interactions > threshold                 │
# └─────────────────────────────────────────────────────────┘
#
# References:
# - Doris Tsao: Face Processing in Visual Cortex (Cell, Nature, Science)
# - QRI: Symmetry Theory of Valence (phenomenal field topology)
# - Mazzola: Topos of Music (topological consciousness)

require_relative 'bidirectional_skill_traversal'

module TsaoVisualCortex

  # ═════════════════════════════════════════════════════════════════════════════
  # LAYER 0: V1 SIMPLE CELL DETECTORS (Josephson Junctions)
  # ═════════════════════════════════════════════════════════════════════════════

  class V1SimpleCellDetector
    # Single V1 neuron = single Josephson junction
    # Detects: edge orientation, contrast, temporal motion

    attr_reader :cell_id, :preferred_orientation, :response_magnitude, :phenomenal_state
    attr_reader :interaction_history

    def initialize(cell_id:, preferred_orientation:)
      @cell_id = cell_id
      @preferred_orientation = preferred_orientation  # -180..180 degrees
      @response_magnitude = 0.0                        # 0.0 = silent, 1.0 = firing maximum
      @phenomenal_state = :smooth                      # :smooth, :defect, :vortex
      @interaction_history = []
      @adaptation_rate = 0.01
    end

    def detect_edge(stimulus_orientation:, stimulus_contrast:)
      # Tuning curve: Gaussian around preferred orientation
      # Response = gaussian(stimulus_orientation - @preferred_orientation) * stimulus_contrast

      orientation_diff = (stimulus_orientation - @preferred_orientation).abs
      orientation_diff = 180.0 - orientation_diff if orientation_diff > 90.0

      # Gaussian tuning
      tuning = Math.exp(-((orientation_diff / 45.0) ** 2))
      response = tuning * stimulus_contrast

      # Adaptation: responding repeatedly reduces response (fatigue)
      @response_magnitude = response * (1.0 - @adaptation_rate * @interaction_history.length)

      record_interaction(:detect_edge, response)

      @response_magnitude
    end

    def observe_behavioral_goal(goal:, task_relevance:)
      # Top-down modulation: prefrontal tells V1 which edges matter
      # If task wants horizontal edges, V1 horizontal detectors fire more

      goal_match = if goal == :identify_face
                     # Faces have many vertical edges (face outline)
                     Math.cos((@preferred_orientation - 90.0) * Math::PI / 180.0).abs
                   elsif goal == :detect_motion
                     # Motion needs temporal edges (all orientations)
                     1.0
                   else
                     0.5
                   end

      # Reweight response based on task
      @response_magnitude *= (1.0 + task_relevance * goal_match * 0.2)

      record_interaction(:goal_modulation, @response_magnitude)
    end

    def record_interaction(event_type, magnitude)
      @interaction_history << {
        time: Time.now,
        event: event_type,
        magnitude: magnitude,
        phenomenal_state: @phenomenal_state
      }

      # Periodically reset adaptation
      @interaction_history = @interaction_history.last(100)
    end

    def status
      {
        cell_id: @cell_id,
        preferred_orientation: @preferred_orientation,
        response_magnitude: @response_magnitude.round(3),
        phenomenal_state: @phenomenal_state,
        interactions: @interaction_history.length
      }
    end
  end

  # ═════════════════════════════════════════════════════════════════════════════
  # LAYER 1: V2/V4 FEATURE INTEGRATION (Skill Circuits)
  # ═════════════════════════════════════════════════════════════════════════════

  class V2V4FeatureIntegrator
    # V2/V4 integrates V1 outputs: edges → textures → shapes
    # = SkillCircuit composing multiple gates

    attr_reader :region_id, :layer_type, :v1_inputs, :feature_selectivity
    attr_reader :phenomenal_state

    def initialize(region_id:, layer_type: :v2)
      @region_id = region_id
      @layer_type = layer_type  # :v2, :v4
      @v1_inputs = []           # Connected V1 cells
      @feature_selectivity = 0.0 # 0.0 = none, 1.0 = strong
      @phenomenal_state = :smooth
      @concept_layer_observation = { observed_features: [] }
    end

    def receive_v1_input(v1_cells:)
      # Get outputs from connected V1 cells
      @v1_inputs = v1_cells

      # Integrate: AND composition (need multiple edges for feature)
      edge_orientations = @v1_inputs.map(&:response_magnitude)
      @feature_selectivity = edge_orientations.sum / @v1_inputs.length
    end

    def integrate_features
      # SkillCircuit execution: compose gates to extract features
      responses = @v1_inputs.map(&:response_magnitude)

      case @layer_type
      when :v2
        # Texture features: orientation + color
        texture_response = responses.sum / responses.length
        texture_response
      when :v4
        # Shape features: closed contours, curvature
        # Need aligned edges around a region
        if responses.length > 1
          mean = responses.sum / responses.length
          variance = responses.map { |r| (r - mean) ** 2 }.sum / responses.length
          contour_alignment = variance
        else
          contour_alignment = 0.0
        end
        Math.sqrt(contour_alignment)
      end
    end

    def observe_behavioral_goal(goal:, task_relevance:)
      # Top-down modulation: prefrontal tells V2/V4 which features matter
      if goal == :identify_face
        @feature_selectivity *= 1.1  # Boost selectivity for face tasks
      elsif goal == :detect_emotion
        @feature_selectivity *= 0.9  # De-emphasize for emotion detection
      end
end

    def observe_v1_patterns(v1_ensemble:)
      # ConceptLayer observation: "What patterns do V1 cells make?"
      patterns = v1_ensemble.map { |v1| v1.response_magnitude }
      @concept_layer_observation[:observed_features] = patterns.sort.reverse.first(3)

      # Update phenomenal state based on pattern coherence
      variance = if patterns.empty?
                   0.0
                 else
                   mean = patterns.sum / patterns.length
                   patterns.map { |p| (p - mean) ** 2 }.sum / patterns.length
                 end

      @phenomenal_state = if variance < 0.1
                            :smooth  # Coherent input
                          elsif variance < 0.3
                            :defect  # Some mismatch
                          else
                            :vortex  # High mismatch (topological discontinuity)
                          end
    end

    def status
      {
        region_id: @region_id,
        layer_type: @layer_type,
        v1_inputs_count: @v1_inputs.length,
        feature_selectivity: @feature_selectivity.round(3),
        phenomenal_state: @phenomenal_state,
        observed_features: @concept_layer_observation[:observed_features].map { |f| f.round(2) }
      }
    end
  end

  # ═════════════════════════════════════════════════════════════════════════════
  # LAYER 2: IT/TEO FACE RECOGNITION PATCHES (Concept Layer Level 1-2)
  # ═════════════════════════════════════════════════════════════════════════════

  class FaceRecognitionPatch
    # Single face patch (6 patches total in IT/TEO)
    # Each patch has specific selectivity: identity, viewpoint, expression

    attr_reader :patch_id, :selectivity_type, :face_selectivity, :phenomenal_state
    attr_reader :specialization

    def initialize(patch_id:, selectivity_type: :identity)
      @patch_id = patch_id
      @selectivity_type = selectivity_type  # :identity, :viewpoint, :expression
      @face_selectivity = 0.0                # How selective for faces
      @phenomenal_state = :smooth
      @specialization = {}                   # Learned preferences
      @concept_understanding = {
        understood_pattern: nil,
        confidence: 0.0
      }
    end

    def process_visual_input(v2v4_features:, behavioral_goal:)
      # ConceptLayer interpret: "What face property does this represent?"

      case @selectivity_type
      when :identity
        # Identity patch: "Is this John or Mary?"
        identity_confidence = compute_identity_response(v2v4_features)
        @face_selectivity = identity_confidence

      when :viewpoint
        # Viewpoint patch: "Is the face frontal or profile?"
        viewpoint_confidence = compute_viewpoint_response(v2v4_features)
        @face_selectivity = viewpoint_confidence

      when :expression
        # Expression patch: "Is this face happy or angry?"
        expression_confidence = compute_expression_response(v2v4_features)
        @face_selectivity = expression_confidence
      end

      # Top-down goal modulation
      if behavioral_goal == :identify_face
        @face_selectivity *= 1.2  # Boost selectivity for task
      end

      @concept_understanding[:understood_pattern] = {
        type: @selectivity_type,
        confidence: @face_selectivity
      }

      @concept_understanding[:confidence] = @face_selectivity
    end

    def learn_from_outcome(actual_label:, prediction_confidence:, reward:)
      # Bidirectional rewiring based on feedback
      # ConceptLayer rewrite: "Update what this patch should prefer"

      if reward > 0.7
        # Successful: strengthen this specialization
        @specialization[actual_label] = (@specialization[actual_label] || 0.0) + 0.05
        @face_selectivity += 0.02
        @phenomenal_state = :smooth
      else
        # Failed: depotentiate or rewire
        @face_selectivity *= 0.9
        @phenomenal_state = :defect  # Create topological discontinuity
      end

      # Ensure selectivity stays in bounds
      @face_selectivity = [@face_selectivity, 1.0].min
      @face_selectivity = [@face_selectivity, 0.0].max
    end

    def coordinate_with_other_patches(other_patches:)
      # Cross-patch learning: patches teach each other
      # Like agents learning from other agents

      other_patches.each do |other|
        next if other.patch_id == @patch_id

        # Share what we've learned
        complementary = (1.0 - @face_selectivity) * other.face_selectivity * 0.01
        @face_selectivity += complementary
      end
    end

    private

    def compute_identity_response(v2v4_features)
      # Simplified: identity is distance to learned prototype
      return 0.1 if v2v4_features.empty?

      v2v4_features.sum / v2v4_features.length
    end

    def compute_viewpoint_response(v2v4_features)
      # Viewpoint: based on feature asymmetry
      return 0.1 if v2v4_features.empty?

      if v2v4_features.length > 1
        differences = v2v4_features.each_cons(2).map { |a, b| (a - b).abs }
        differences.sum / differences.length
      else
        0.1
      end
    end

    def compute_expression_response(v2v4_features)
      # Expression: based on feature dynamics
      return 0.1 if v2v4_features.empty?

      variance = if v2v4_features.length > 1
                   mean = v2v4_features.sum / v2v4_features.length
                   (v2v4_features.map { |f| (f - mean) ** 2 }.sum / v2v4_features.length).to_f
                 else
                   0.0
                 end

      Math.sqrt(variance)
    end

    def status
      {
        patch_id: @patch_id,
        selectivity_type: @selectivity_type,
        face_selectivity: @face_selectivity.round(3),
        phenomenal_state: @phenomenal_state,
        specializations: @specialization.transform_values { |v| v.round(3) },
        understanding_confidence: @concept_understanding[:confidence].round(3)
      }
    end
  end

  # ═════════════════════════════════════════════════════════════════════════════
  # LAYER 3: PREFRONTAL CORTEX (Behavioral Goal Layer)
  # ═════════════════════════════════════════════════════════════════════════════

  class PrefrontalGoalLayer
    # Prefrontal: sets behavioral goals, modulates all lower levels
    # = ConceptLayer level 3+: Meta-understanding that rewrites everything below

    attr_reader :behavioral_goal, :task_focus, :attention_modulation

    def initialize
      @behavioral_goal = :neutral           # :identify_face, :detect_emotion, :remember_face
      @task_focus = {}                      # What to emphasize
      @attention_modulation = {}            # How to weight features
      @performance_history = []
    end

    def set_goal(goal:)
      @behavioral_goal = goal
      @task_focus = case goal
                    when :identify_face
                      { identity: 1.0, viewpoint: 0.5, expression: 0.3 }
                    when :detect_emotion
                      { expression: 1.0, identity: 0.3, viewpoint: 0.3 }
                    when :remember_face
                      { identity: 0.8, viewpoint: 0.8, expression: 0.6 }
                    else
                      { identity: 0.5, viewpoint: 0.5, expression: 0.5 }
                    end
    end

    def receive_feedback(task_performance:, prediction_error:)
      # Prefrontal gets outcome signal
      # Updates modulation strategy based on success

      @performance_history << {
        time: Time.now,
        performance: task_performance,
        error: prediction_error
      }

      # Adjust focus based on what's working
      if prediction_error < 0.2
        # Working well: maintain current strategy
        # Reward signal broadcasts down to all layers
      else
        # Not working: try different focus
        best_task = @task_focus.max_by { |_, v| v }
        @task_focus[best_task[0]] *= 0.8  # De-emphasize

        other_key = @task_focus.keys.reject { |k| k == best_task[0] }.sample
        @task_focus[other_key] *= 1.2     # Emphasize alternative
      end

      # Normalize
      total = @task_focus.values.sum
      @task_focus.transform_values! { |v| v / total }
    end

    def modulate_all_levels(v1_cells:, v2v4_regions:, face_patches:)
      # Top-down control: prefrontal tells all lower levels what to do
      # This is the "rewrite_lower_level" in ConceptLayer

      # Modulate V1
      v1_cells.each { |v1| v1.observe_behavioral_goal(goal: @behavioral_goal, task_relevance: 0.3) }

      # Modulate V2/V4
      v2v4_regions.each { |v2v4| v2v4.observe_behavioral_goal(goal: @behavioral_goal, task_relevance: 0.5) }

      # Modulate IT/TEO patches
      focus_weights = @task_focus
      face_patches.each do |patch|
        weight = focus_weights[patch.selectivity_type] || 0.5
        # Patch receives goal-based modulation
      end
    end

    def status
      {
        behavioral_goal: @behavioral_goal,
        task_focus: @task_focus.transform_values { |v| v.round(3) },
        recent_performance: @performance_history.last(5).map { |h|
          { performance: h[:performance].round(3), error: h[:error].round(3) }
        }
      }
    end
  end

  # ═════════════════════════════════════════════════════════════════════════════
  # COMPLETE ECOSYSTEM: Irreducible Living Visual Cortex
  # ═════════════════════════════════════════════════════════════════════════════

  class VisualCortexEcosystem
    # Complete face processing system: V1 ↔ V2/V4 ↔ IT/TEO ↔ Prefrontal
    # All bidirectionally coupled = IRREDUCIBLE LIVING STRUCTURE

    attr_reader :v1_cells, :v2v4_regions, :face_patches, :prefrontal, :interaction_count

    def initialize(num_v1_cells: 8, num_v2v4_regions: 4, num_face_patches: 6)
      # V1: Simple edge detectors
      @v1_cells = num_v1_cells.times.map do |i|
        V1SimpleCellDetector.new(
          cell_id: "V1_#{i}",
          preferred_orientation: (i * 180.0 / num_v1_cells)
        )
      end

      # V2/V4: Feature integration
      @v2v4_regions = []
      num_v2v4_regions.times do |i|
        @v2v4_regions << V2V4FeatureIntegrator.new(
          region_id: "V2_#{i}",
          layer_type: (i < 2 ? :v2 : :v4)
        )
      end

      # IT/TEO: Face patches
      @face_patches = []
      [:identity, :viewpoint, :expression, :identity, :viewpoint, :expression].each_with_index do |type, i|
        @face_patches << FaceRecognitionPatch.new(
          patch_id: "FaceP#{i}",
          selectivity_type: type
        )
      end

      # Prefrontal: Goal layer
      @prefrontal = PrefrontalGoalLayer.new

      @interaction_count = 0
    end

    def see_and_identify_face(face_stimulus:, behavioral_goal:, actual_identity: nil)
      # Complete forward pass: stimulus → V1 → V2/V4 → IT/TEO → decision

      @interaction_count += 1

      # STEP 1: V1 processes stimulus (simple edge detection)
      stimulus_orientation = face_stimulus[:orientation] || 45.0
      stimulus_contrast = face_stimulus[:contrast] || 0.8

      @v1_cells.each do |v1|
        v1.detect_edge(stimulus_orientation: stimulus_orientation, stimulus_contrast: stimulus_contrast)
      end

      # STEP 2: Set behavioral goal (top-down)
      @prefrontal.set_goal(goal: behavioral_goal)

      # STEP 3: V1 receives goal modulation
      @prefrontal.modulate_all_levels(v1_cells: @v1_cells, v2v4_regions: @v2v4_regions, face_patches: @face_patches)

      # STEP 4: V2/V4 integrates V1 outputs
      @v2v4_regions.each do |v2v4|
        v2v4.receive_v1_input(v1_cells: @v1_cells)
        v2v4.integrate_features
        v2v4.observe_v1_patterns(v1_ensemble: @v1_cells)
      end

      # STEP 5: Face patches process V2/V4 features
      v2v4_features = @v2v4_regions.map(&:feature_selectivity)

      @face_patches.each do |patch|
        patch.process_visual_input(v2v4_features: v2v4_features, behavioral_goal: behavioral_goal)
      end

      # STEP 6: Cross-patch coordination
      @face_patches.each do |patch|
        other_patches = @face_patches.reject { |p| p.patch_id == patch.patch_id }
        patch.coordinate_with_other_patches(other_patches: other_patches)
      end

      # STEP 7: Make decision (which patch has highest selectivity?)
      best_patch = @face_patches.max_by(&:face_selectivity)
      prediction = best_patch.specialization.max_by { |_, v| v }&.first || :unknown

      # STEP 8: If we have ground truth, learn
      if actual_identity
        prediction_error = (prediction == actual_identity) ? 0.0 : 1.0
        performance = 1.0 - prediction_error

        @face_patches.each do |patch|
          patch.learn_from_outcome(
            actual_label: actual_identity,
            prediction_confidence: best_patch.face_selectivity,
            reward: performance
          )
        end

        @prefrontal.receive_feedback(task_performance: performance, prediction_error: prediction_error)
      end

      {
        prediction: prediction,
        confidence: best_patch.face_selectivity,
        best_patch: best_patch.patch_id,
        v1_responses: @v1_cells.map(&:response_magnitude),
        v2v4_selectivity: v2v4_features,
        face_selectivities: @face_patches.map(&:face_selectivity)
      }
    end

    def ecosystem_status
      {
        interaction_count: @interaction_count,
        v1_average_response: @v1_cells.map(&:response_magnitude).sum / @v1_cells.length,
        v2v4_average_selectivity: @v2v4_regions.map(&:feature_selectivity).sum / @v2v4_regions.length,
        face_average_selectivity: @face_patches.map(&:face_selectivity).sum / @face_patches.length,
        smooth_regions: @v2v4_regions.count { |v| v.phenomenal_state == :smooth },
        defect_regions: @v2v4_regions.count { |v| v.phenomenal_state == :defect },
        irreducible_alive: @face_patches.all? { |p| p.face_selectivity > 0.3 } &&
                           @interaction_count > 5
      }
    end
  end
end

# ═════════════════════════════════════════════════════════════════════════════
# DEMONSTRATION
# ═════════════════════════════════════════════════════════════════════════════

if __FILE__ == $0
  puts "🧠 Initializing Tsao Visual Cortex Ecosystem (Face Recognition)...\n\n"

  ecosystem = TsaoVisualCortex::VisualCortexEcosystem.new(
    num_v1_cells: 8,
    num_v2v4_regions: 4,
    num_face_patches: 6
  )

  puts "✓ Ecosystem created with:"
  puts "  - 8 V1 simple cell detectors"
  puts "  - 4 V2/V4 feature integration regions"
  puts "  - 6 IT/TEO face recognition patches"
  puts "  - 1 Prefrontal goal layer\n\n"

  # Simulate learning 3 faces over 5 rounds each
  faces = [
    { name: :alice, orientation: 45.0, contrast: 0.9 },
    { name: :bob, orientation: 60.0, contrast: 0.8 },
    { name: :charlie, orientation: 30.0, contrast: 0.85 }
  ]

  faces.each do |face|
    puts "═" * 70
    puts "LEARNING FACE: #{face[:name].upcase}"
    puts "═" * 70

    5.times do |attempt|
      result = ecosystem.see_and_identify_face(
        face_stimulus: { orientation: face[:orientation], contrast: face[:contrast] },
        behavioral_goal: :identify_face,
        actual_identity: face[:name]
      )

      puts "\nAttempt #{attempt + 1}:"
      puts "  Prediction: #{result[:prediction]} (confidence: #{(result[:confidence] * 100).round(1)}%)"
      puts "  V1 avg response: #{(result[:v1_responses].sum / result[:v1_responses].length).round(3)}"
      puts "  Face selectivities: #{result[:face_selectivities].map { |s| (s * 100).round(0) }.join(', ')}%"
    end
  end

  puts "\n" + "=" * 70
  puts "FINAL ECOSYSTEM STATUS"
  puts "=" * 70

  status = ecosystem.ecosystem_status
  puts "Total interactions: #{status[:interaction_count]}"
  puts "V1 average response: #{(status[:v1_average_response] * 100).round(1)}%"
  puts "V2/V4 average selectivity: #{(status[:v2v4_average_selectivity] * 100).round(1)}%"
  puts "Face patches average selectivity: #{(status[:face_average_selectivity] * 100).round(1)}%"
  puts "Smooth regions: #{status[:smooth_regions]}"
  puts "Defect regions: #{status[:defect_regions]}"
  puts "System is alive and irreducible: #{status[:irreducible_alive]}"

  puts "\n🌱 IRREDUCIBLE LIVING STRUCTURE ACHIEVED\n"
end
