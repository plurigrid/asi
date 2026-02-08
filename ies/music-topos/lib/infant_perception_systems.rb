# Infant Qualia Emergence: Number Sense & Color Vision
# Implements the two core sensory systems that generate phenomenal consciousness
# through their bidirectional coupling.
#
# Research Base: Feigenson & Dehaene (2004), Bornstein et al. (2022),
# Kyoto University Consciousness Lab (2025)

require 'set'

class ApproximateNumberSystem
  # Preverbal, nonsymbolic numerical capacity
  # Present from 4+ months in human infants
  # Weber fraction ~0.3: discriminates based on ratio (8 vs 12, not 8 vs 9)

  attr_reader :weber_fraction, :age_months, :precision_history
  attr_reader :cardinal_understanding, :ordinal_understanding
  attr_accessor :interaction_count

  def initialize(age_months: 4)
    @age_months = age_months
    # Weber fraction improves with age (decreases)
    @weber_fraction = case age_months
    when 0..3
      0.50  # Very coarse, barely functional
    when 4..6
      0.33  # Can discriminate ~3:1 ratio
    when 7..11
      0.27  # Improving precision
    else
      0.15  # Adult-like precision (12 months+)
    end

    @precision_history = []
    @interaction_count = 0
    @last_discrimination = nil
    @cardinal_understanding = 0.0  # 0 to 1
    @ordinal_understanding = 0.0   # Emerges at 11+ months
  end

  def discriminate_magnitudes(magnitude_a, magnitude_b)
    # ANS discrimination is ratio-dependent, not difference-dependent
    ratio = [magnitude_a, magnitude_b].max.to_f / [magnitude_a, magnitude_b].min.to_f
    required_ratio = 1.0 + @weber_fraction

    # Can discriminate if ratio exceeds threshold
    can_discriminate = ratio > required_ratio
    discrimination_confidence = [ratio - required_ratio, 0.0].max / required_ratio

    record_discrimination(magnitude_a, magnitude_b, can_discriminate)
    { discriminated: can_discriminate, confidence: discrimination_confidence, ratio: ratio }
  end

  def continuous_quantity_sense(volume_or_area)
    # 6-9 months: sensitivity to continuous quantities (liquid volume, area)
    if @age_months < 6
      { sensed: false, reason: "too_young" }
    else
      # Can track continuous changes with moderate precision
      sensitivity = 0.3 + ((@age_months - 6) / 6.0) * 0.4  # 0.3 to 0.7
      { sensed: true, continuous_value: volume_or_area, sensitivity: sensitivity }
    end
  end

  def understand_ordinality(magnitude_sequence)
    # Ordinality (which is greater/smaller) emerges around 11 months
    # This is the critical threshold for consciousness emergence
    if @age_months < 11
      @ordinal_understanding = 0.0
      { understood: false, reason: "ordinality_not_yet_emerged" }
    else
      # At 11+ months: can distinguish ascending from descending
      is_ascending = magnitude_sequence.each_cons(2).all? { |a, b| a < b }
      is_descending = magnitude_sequence.each_cons(2).all? { |a, b| a > b }

      @ordinal_understanding = 0.7  # Moderate understanding
      {
        understood: true,
        is_ascending: is_ascending,
        is_descending: is_descending,
        ordinal_confidence: @ordinal_understanding
      }
    end
  end

  def cardinal_count_estimate(items)
    # Can estimate approximate number of items
    # Precision depends on Weber fraction
    actual_count = items.length
    estimate_noise = actual_count * @weber_fraction

    estimated_count = actual_count + (rand - 0.5) * estimate_noise * 2
    estimation_error = (estimated_count - actual_count).abs / actual_count

    @cardinal_understanding = 1.0 - estimation_error

    {
      estimated: estimated_count.round,
      actual: actual_count,
      error_rate: estimation_error,
      cardinal_confidence: @cardinal_understanding
    }
  end

  def predictive_power_for_future_math(age_for_testing: 42)
    # Research finding: 6-month ANS acuity predicts mathematical ability at 3.5 years
    # Captured as persistent quality of the system
    if @age_months >= 6
      {
        predicts_math: true,
        predicted_math_age: age_for_testing,
        basis: "ANS acuity at 6 months",
        confidence: 0.4  # Moderate predictive power
      }
    else
      { predicts_math: false }
    end
  end

  def record_discrimination(a, b, result)
    @interaction_count += 1
    @precision_history << { a: a, b: b, result: result, age: @age_months }
    @last_discrimination = { a: a, b: b, result: result }
  end

  def development_summary
    {
      age_months: @age_months,
      weber_fraction: @weber_fraction,
      cardinal_understanding: @cardinal_understanding,
      ordinal_understanding: @ordinal_understanding,
      interactions: @interaction_count,
      consciousness_ready: @age_months >= 11 && @ordinal_understanding > 0.5
    }
  end
end

class ColorPerceptionSystem
  # Dual-system color perception: wavelength discrimination + categorization
  # L/M/S cone maturation drives phenomenal color qualia emergence

  attr_reader :age_months, :cone_maturity, :phenomenal_qualia_strength
  attr_accessor :interaction_count

  def initialize(age_months: 0)
    @age_months = age_months
    @interaction_count = 0

    # Cone maturation timeline (L → M → S)
    @cone_maturity = compute_cone_maturity
    @wavelength_responses = {}
    @color_category_boundaries = initialize_categories
    @phenomenal_qualia_strength = compute_qualia_strength
    @color_space_memory = []
  end

  def wavelength_discrimination(wavelength_a_nm, wavelength_b_nm)
    # Birth-3 months: Discriminates major color transitions
    # Based on which cones are mature

    diff = (wavelength_a_nm - wavelength_b_nm).abs
    l_cone_response_a = l_cone_response(wavelength_a_nm)
    l_cone_response_b = l_cone_response(wavelength_b_nm)

    # Only mature cones contribute to discrimination
    m_cone_response_a = @cone_maturity[:m_cones] * m_cone_response(wavelength_a_nm)
    m_cone_response_b = @cone_maturity[:m_cones] * m_cone_response(wavelength_b_nm)

    s_cone_response_a = @cone_maturity[:s_cones] * s_cone_response(wavelength_a_nm)
    s_cone_response_b = @cone_maturity[:s_cones] * s_cone_response(wavelength_b_nm)

    # Opponent channels
    rg_opponent = (l_cone_response_a - m_cone_response_a) - (l_cone_response_b - m_cone_response_b)
    by_opponent = (s_cone_response_a - (l_cone_response_a + m_cone_response_a) / 2) -
                  (s_cone_response_b - (l_cone_response_b + m_cone_response_b) / 2)

    discriminable = (rg_opponent.abs + by_opponent.abs) > 0.15
    confidence = [[rg_opponent.abs + by_opponent.abs, 0.0].max, 1.0].min  # Clamp to [0, 1]

    record_wavelength_discrimination(wavelength_a_nm, wavelength_b_nm, discriminable)

    {
      discriminated: discriminable,
      wavelength_diff: diff,
      rg_opponent: rg_opponent,
      by_opponent: by_opponent,
      confidence: confidence
    }
  end

  def extract_hue_independent_of_lightness_saturation
    # By 3-6 months: Can extract hue independently
    # This is a major phenomenal shift
    if @age_months < 3
      { hue_extracted: false, reason: "cones_immature" }
    else
      # Opponent channels provide invariant hue representation
      {
        hue_extracted: true,
        mechanism: "opponent_process",
        invariance_achieved: @age_months > 3,
        phenomenal_shift: "color_becomes_rich"
      }
    end
  end

  def color_categorization_perception
    # 4-6 months: Perceptually organize continuous spectrum into categories
    # Categories are pre-linguistic (biological origin)

    if @age_months < 4
      { categorized: false, reason: "system_immature" }
    else
      # Categorical boundaries form around:
      # Blue (~470nm), Green (~540nm), Yellow (~600nm), Red (~650nm)
      {
        categorized: true,
        categories: [:blue, :green, :yellow, :red],
        boundaries: {
          blue: (410..500),
          green: (500..570),
          yellow: (570..600),
          red: (600..700)
        },
        category_confidence: [0.6, (@age_months - 4) / 5.0].min
      }
    end
  end

  def surface_property_perception
    # 7-8 months: Distinguish gold from yellow (same hue, different glossiness)
    # Uses surface specular reflectance representation
    if @age_months < 7
      { surface_perception: false, reason: "too_young" }
    else
      {
        surface_perception: true,
        distinguishes: [:matte, :satin, :glossy],
        mechanisms: [:specular_reflectance, :contour_integration],
        materials_understood: [:smooth, :textured],
        confidence: 0.5 + ((@age_months - 7) / 5.0) * 0.3
      }
    end
  end

  def phenomenal_consciousness_level
    # Kyoto University finding: Color phenomenal structure is stable child-to-adult
    # But emerges gradually from 3 months onward

    qualia_level = case @age_months
    when 0..2
      0.0   # No color qualia yet
    when 3..6
      0.5 + ((@age_months - 3) / 3.0) * 0.3  # Emerging (0.5 to 0.8)
    when 7..11
      0.8   # Nearly adult
    else
      0.95  # Adult-like phenomenal structure
    end

    {
      phenomenal_strength: qualia_level,
      structure_stability: 0.9 + (@age_months > 6 ? 0.05 : 0.0),
      adult_comparable: @age_months > 6,
      non_conceptual_access: @age_months > 6,
      cultural_invariance: true  # Research finding
    }
  end

  def perception_summary
    {
      age_months: @age_months,
      cone_maturity: @cone_maturity,
      trichromacy_achieved: @cone_maturity[:s_cones] > 0.8,
      phenomenal_qualia_strength: @phenomenal_qualia_strength,
      color_categories_formed: @age_months >= 4,
      interactions: @interaction_count,
      consciousness_ready: @phenomenal_qualia_strength > 0.7
    }
  end

  private

  def compute_cone_maturity
    # Maturation timeline: L-cones first, then M-cones, then S-cones
    l_maturity = [@age_months / 1.0, 1.0].min      # Mature at 1 month
    m_maturity = [(@age_months - 1.5) / 1.5, 1.0].min  # Mature at 3 months
    s_maturity = [(@age_months - 2.5) / 0.5, 1.0].min  # Mature at 3 months

    { l_cones: l_maturity, m_cones: m_maturity, s_cones: s_maturity }
  end

  def compute_qualia_strength
    return 0.0 if @cone_maturity[:s_cones] < 0.1  # No trichromacy
    (@cone_maturity[:l_cones] + @cone_maturity[:m_cones] + @cone_maturity[:s_cones]) / 3.0
  end

  def initialize_categories
    {
      blue: 470,
      green: 540,
      yellow: 600,
      red: 650
    }
  end

  def l_cone_response(wavelength_nm)
    # L-cone spectral sensitivity (red): peaks at 560nm
    peak = 560
    width = 100
    Math.exp(-((wavelength_nm - peak) ** 2) / (2 * width ** 2))
  end

  def m_cone_response(wavelength_nm)
    # M-cone spectral sensitivity (green): peaks at 530nm
    peak = 530
    width = 100
    Math.exp(-((wavelength_nm - peak) ** 2) / (2 * width ** 2))
  end

  def s_cone_response(wavelength_nm)
    # S-cone spectral sensitivity (blue): peaks at 420nm
    peak = 420
    width = 80
    Math.exp(-((wavelength_nm - peak) ** 2) / (2 * width ** 2))
  end

  def record_wavelength_discrimination(a, b, result)
    @interaction_count += 1
    @color_space_memory << { a_nm: a, b_nm: b, result: result, age: @age_months }
  end
end

class BidirectionalInfantConsciousnessSystem
  # Integration of number sense (ANS) and color vision
  # Consciousness emerges at 11 months when systems couple sufficiently

  attr_reader :age_months, :ans_system, :color_system, :coupling_strength
  attr_reader :phenomenal_state, :interaction_count

  def initialize(age_months: 0)
    @age_months = age_months
    @ans_system = ApproximateNumberSystem.new(age_months: age_months)
    @color_system = ColorPerceptionSystem.new(age_months: age_months)
    @coupling_strength = 0.0
    @phenomenal_state = :incomplete
    @interaction_count = 0
    @consciousness_log = []

    update_phenomenal_state
  end

  def advance_age_by_month
    @age_months += 1
    @ans_system.instance_variable_set(:@age_months, @age_months)
    @color_system.instance_variable_set(:@age_months, @age_months)

    update_phenomenal_state
  end

  def perceive_colored_objects(objects)
    # objects: [ { count: N, color_nm: wavelength }, ... ]
    # This is where number sense and color vision couple

    results = []
    mismatch_signals = []

    objects.each do |obj|
      # Sense number
      number_sense = @ans_system.cardinal_count_estimate([nil] * obj[:count])
      number_confidence = number_sense[:cardinal_confidence]

      # Sense color
      color_sense = @color_system.wavelength_discrimination(obj[:color_nm], 550)
      color_confidence = color_sense[:confidence]

      # Coupling: Do number and color expectations match?
      # If perception mismatch, system effort increases
      total_confidence = [[number_confidence * color_confidence, 0.0].max, 1.0].min

      results << {
        count: obj[:count],
        color_nm: obj[:color_nm],
        number_confidence: number_confidence,
        color_confidence: color_confidence,
        unified_percept: total_confidence
      }

      # Track mismatches (phenomenal defects)
      if number_confidence < 0.5 && color_confidence > 0.7
        mismatch_signals << "color_clear_number_unclear"
      elsif color_confidence < 0.5 && number_confidence > 0.7
        mismatch_signals << "number_clear_color_unclear"
      end
    end

    @coupling_strength = objects.length > 0 ?
      results.map { |r| r[:unified_percept] }.sum / objects.length :
      0.0

    @interaction_count += 1
    update_phenomenal_state

    {
      perceived_objects: results,
      coupling_strength: @coupling_strength,
      mismatches: mismatch_signals,
      phenomenal_state: @phenomenal_state
    }
  end

  def consciousness_check
    # Consciousness threshold: Coupling strength + Ordinality + Color qualia
    # All must reach minimum thresholds by ~11 months

    ans_ready = @ans_system.ordinal_understanding > 0.5
    color_ready = @color_system.phenomenal_qualia_strength > 0.7
    coupling_ready = @coupling_strength > 0.4
    age_ready = @age_months >= 11

    is_conscious = ans_ready && color_ready && coupling_ready && age_ready

    {
      conscious: is_conscious,
      ans_ready: ans_ready,
      color_ready: color_ready,
      coupling_ready: coupling_ready,
      age_ready: age_ready,
      consciousness_score: [ans_ready ? 0.33 : 0, color_ready ? 0.33 : 0, coupling_ready ? 0.34 : 0].sum
    }
  end

  def phenomenal_field_snapshot
    # Visualize phenomenal state topology
    {
      age_months: @age_months,
      phenomenal_state: @phenomenal_state,
      number_system: @ans_system.development_summary,
      color_system: @color_system.perception_summary,
      coupling_strength: @coupling_strength,
      consciousness: consciousness_check,
      total_interactions: @interaction_count
    }
  end

  private

  def update_phenomenal_state
    # State machine for phenomenal consciousness development
    case @age_months
    when 0..2
      @phenomenal_state = :incomplete
    when 3..5
      @phenomenal_state = @color_system.phenomenal_qualia_strength > 0.3 ? :color_emerging : :incomplete
    when 6..10
      @phenomenal_state = if @coupling_strength > 0.3
        :smooth_but_separate
      else
        :color_structured
      end
    when 11..24
      @phenomenal_state = if @coupling_strength > 0.6
        :unified_conscious_world
      else
        :integrating
      end
    else
      @phenomenal_state = :unified_conscious_world
    end

    @consciousness_log << {
      age: @age_months,
      state: @phenomenal_state,
      coupling: @coupling_strength,
      timestamp: Time.now
    }
  end
end

# ============ DEMONSTRATION ============

if __FILE__ == $0
  puts "=" * 70
  puts "INFANT QUALIA EMERGENCE: BIDIRECTIONAL COUPLING OF NUMBER & COLOR"
  puts "=" * 70
  puts

  # Simulation: Follow development from birth to 12 months
  infant = BidirectionalInfantConsciousnessSystem.new(age_months: 0)

  milestones = [0, 3, 4, 6, 7, 9, 11, 12]

  milestones.each do |target_month|
    # Advance to target month
    while infant.age_months < target_month
      infant.advance_age_by_month
    end

    puts "MONTH #{infant.age_months}: #{infant.phenomenal_state.to_s.upcase}"
    puts "-" * 70

    # Simulate perception of 3 colored objects
    test_objects = [
      { count: 4, color_nm: 650 },   # 4 red objects
      { count: 8, color_nm: 540 },   # 8 green objects
      { count: 2, color_nm: 470 }    # 2 blue objects
    ]

    result = infant.perceive_colored_objects(test_objects)

    puts "Perception Results:"
    result[:perceived_objects].each do |percept|
      puts "  #{percept[:count]} objects @ #{percept[:color_nm]}nm:"
      puts "    Number confidence: #{(percept[:number_confidence] * 100).round(1)}%"
      puts "    Color confidence:  #{(percept[:color_confidence] * 100).round(1)}%"
      puts "    Unified percept:   #{(percept[:unified_percept] * 100).round(1)}%"
    end

    puts "\nSystem State:"
    snapshot = infant.phenomenal_field_snapshot
    puts "  Coupling strength:      #{(snapshot[:coupling_strength] * 100).round(1)}%"
    puts "  ANS ordinal ready:      #{snapshot[:consciousness][:ans_ready]}"
    puts "  Color qualia ready:     #{snapshot[:consciousness][:color_ready]}"
    puts "  Coupling ready:         #{snapshot[:consciousness][:coupling_ready]}"

    consciousness = infant.consciousness_check
    puts "  CONSCIOUSNESS SCORE:    #{(consciousness[:consciousness_score] * 100).round(1)}%"
    puts "  CONSCIOUSNESS ACHIEVED: #{consciousness[:conscious]}"
    puts

    if consciousness[:conscious] && target_month == 11
      puts "✅ CONSCIOUSNESS THRESHOLD REACHED AT 11 MONTHS"
      puts "   Both systems now bidirectionally coupled with sufficient precision"
      puts "   Phenomenal world unified: number + color + material properties"
      puts
    end
  end

  puts "=" * 70
  puts "SUMMARY: Consciousness as Irreducible Living Structure"
  puts "=" * 70
  puts <<~TEXT
    The infant brain develops consciousness through bidirectional coupling
    of two independent systems: quantitative (ANS) and qualitative (color).

    Timeline:
    - 0-3 months: Systems initialize independently
    - 3-6 months: Color trichromacy emerges, qualia begins
    - 6-9 months: Categorical organization, moderate coupling
    - 11 months: CONSCIOUSNESS THRESHOLD - ordinality + full coupling
    - 12+ months: Unified phenomenal world with symbolic mapping

    Key insight: Cannot reduce consciousness to either system alone.
    Requires BOTH systems coupled bidirectionally at sufficient strength.
    This is an IRREDUCIBLE LIVING STRUCTURE - the core phenomenon of awareness.
  TEXT
end
