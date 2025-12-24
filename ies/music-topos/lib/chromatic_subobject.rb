# lib/chromatic_subobject.rb
# Chromatic Subobject Classifier Ω₃ for Music Topos
#
# In a topos, the subobject classifier Ω satisfies:
#   For any mono m: A → B, ∃! χ_m: B → Ω s.t. A is the pullback of true: 1 → Ω
#
# In Music Topos with GF(3), we have Ω₃ = {-1, 0, +1} with:
#   - true = +1 (PLUS, warm, included)
#   - false = -1 (MINUS, cold, excluded)
#   - partial = 0 (ERGODIC, neutral, boundary)

require_relative 'splitmix_ternary'

module ChromaticSubobject
  # The chromatic truth values
  OMEGA_3 = {
    true: { trit: 1, name: :plus, hue_range: [0, 60, 300, 360] },
    false: { trit: -1, name: :minus, hue_range: [180, 300] },
    partial: { trit: 0, name: :ergodic, hue_range: [60, 180] }
  }.freeze
  
  # Characteristic morphism χ: B → Ω₃
  # Given a predicate on elements, return their chromatic truth value
  def self.characteristic(element, predicate)
    result = predicate.call(element)
    case result
    when true, 1, :plus then OMEGA_3[:true]
    when false, -1, :minus then OMEGA_3[:false]
    else OMEGA_3[:partial]  # anything else is partial/boundary
    end
  end
  
  # Cybernetic spleen: the organ that filters and classifies
  # In our topos, it's the functor that assigns chromatic values
  class CyberneticSpleen
    attr_reader :seed, :classifications, :gf3_history
    
    def initialize(seed = 0x42D)
      @seed = seed
      @gen = SplitMixTernary::Generator.new(seed)
      @classifications = []
      @gf3_history = []
    end
    
    # Classify an element with survival pressure
    def classify(element, fitness_fn = nil)
      color = @gen.next_color
      trit = color[:trit]
      
      # Apply survival pressure: higher fitness → more likely to be PLUS
      if fitness_fn
        fitness = fitness_fn.call(element)
        if fitness > 0.7
          trit = 1   # Survives → PLUS
        elsif fitness < 0.3
          trit = -1  # Dies → MINUS
        else
          trit = 0   # Boundary → ERGODIC
        end
      end
      
      classification = {
        element: element,
        color: color,
        trit: trit,
        truth: OMEGA_3.values.find { |v| v[:trit] == trit }
      }
      
      @classifications << classification
      @gf3_history << trit
      
      # Check GF(3) conservation every 3 elements
      if @gf3_history.size % 3 == 0
        last_3 = @gf3_history.last(3)
        current_sum = last_3.sum % 3
        unless current_sum == 0
          # Overzealous spleen: adjust to conserve!
          # Map sum to correction: 1 → -1, 2 → +1 to make sum ≡ 0 (mod 3)
          correction = current_sum == 1 ? -1 : 1
          new_trit = (@gf3_history[-1] + correction)
          # Clamp to valid trit range
          new_trit = [[new_trit, -1].max, 1].min
          @classifications.last[:trit] = new_trit
          @gf3_history[-1] = new_trit
        end
      end
      
      classification
    end
    
    def verify_conservation
      @gf3_history.each_slice(3).all? { |slice| slice.size < 3 || slice.sum % 3 == 0 }
    end
  end
  
  # Pullback construction: given χ_m: B → Ω₃ and truth value t ∈ Ω₃,
  # return the subobject A ⊆ B where χ_m(b) = t
  class Pullback
    def initialize(classifier, truth_value)
      @classifier = classifier
      @truth_value = truth_value
    end
    
    def apply(elements)
      elements.select do |e|
        c = @classifier.classifications.find { |c| c[:element] == e }
        c && c[:trit] == @truth_value
      end
    end
  end
  
  # Morphism of subobject classifiers
  # Maps between different chromatic truth interpretations
  class OmegaMorphism
    def initialize(mapping)
      @mapping = mapping  # e.g., { 1 => 0, 0 => 0, -1 => -1 } collapses true to partial
    end
    
    def apply(trit)
      @mapping[trit] || trit
    end
    
    # Composition
    def compose(other)
      new_mapping = @mapping.transform_values { |v| other.apply(v) }
      OmegaMorphism.new(new_mapping)
    end
  end
  
  # Predefined morphisms
  MORPHISMS = {
    # Collapse to binary
    to_binary: OmegaMorphism.new({ 1 => 1, 0 => 1, -1 => -1 }),
    # Everything survives (optimist)
    optimist: OmegaMorphism.new({ 1 => 1, 0 => 1, -1 => 0 }),
    # Everything dies (pessimist)
    pessimist: OmegaMorphism.new({ 1 => 0, 0 => -1, -1 => -1 }),
    # Negation
    not: OmegaMorphism.new({ 1 => -1, 0 => 0, -1 => 1 }),
    # Identity
    id: OmegaMorphism.new({ 1 => 1, 0 => 0, -1 => -1 })
  }.freeze
  
  def self.demo(seed = 0x42D)
    puts "═══════════════════════════════════════════════════════════════"
    puts "  CHROMATIC SUBOBJECT CLASSIFIER Ω₃ (Subagent PLUS, trit=+1)"
    puts "═══════════════════════════════════════════════════════════════"
    puts
    puts "Ω₃ = { MINUS(-1), ERGODIC(0), PLUS(+1) }"
    puts "     (false)    (partial)   (true)"
    puts
    
    spleen = CyberneticSpleen.new(seed)
    
    # Classify some musical elements with fitness function
    elements = [:C, :D, :E, :F, :G, :A, :B, :C8, :rest]
    fitness_fn = ->(e) { 
      case e
      when :C, :G then 0.9  # Tonic/dominant survive
      when :E, :A then 0.6  # Mediant/submediant partial
      when :rest then 0.1   # Rests die
      else 0.5
      end
    }
    
    puts "─── Cybernetic Spleen Classifications ───"
    elements.each do |elem|
      c = spleen.classify(elem, fitness_fn)
      trit_sym = { -1 => '−', 0 => '○', 1 => '+' }[c[:trit]]
      puts "  #{elem.to_s.ljust(6)} → #{trit_sym} (H=#{c[:color][:H].round(1)}°)"
    end
    
    puts
    puts "GF(3) History: #{spleen.gf3_history.inspect}"
    puts "Conservation verified: #{spleen.verify_conservation ? '✓' : '✗'}"
    
    puts
    puts "─── Pullback Subobjects ───"
    plus_pullback = Pullback.new(spleen, 1)
    minus_pullback = Pullback.new(spleen, -1)
    ergodic_pullback = Pullback.new(spleen, 0)
    
    puts "  true⁻¹(+1):  #{plus_pullback.apply(elements).inspect}"
    puts "  true⁻¹(0):   #{ergodic_pullback.apply(elements).inspect}"
    puts "  true⁻¹(-1):  #{minus_pullback.apply(elements).inspect}"
    
    puts
    puts "─── Omega Morphisms ───"
    original_trits = spleen.gf3_history
    puts "  Original:   #{original_trits.inspect}"
    puts "  ¬ (not):    #{original_trits.map { |t| MORPHISMS[:not].apply(t) }.inspect}"
    puts "  optimist:   #{original_trits.map { |t| MORPHISMS[:optimist].apply(t) }.inspect}"
    puts "  pessimist:  #{original_trits.map { |t| MORPHISMS[:pessimist].apply(t) }.inspect}"
    
    puts
    puts "═══════════════════════════════════════════════════════════════"
    puts "Subobject classifier Ω₃ with GF(3) conservation complete."
    puts "═══════════════════════════════════════════════════════════════"
    
    {
      seed: seed,
      classifications: spleen.classifications.map { |c| { element: c[:element], trit: c[:trit] } },
      gf3_history: spleen.gf3_history,
      conservation_verified: spleen.verify_conservation,
      subobjects: {
        plus: plus_pullback.apply(elements),
        ergodic: ergodic_pullback.apply(elements),
        minus: minus_pullback.apply(elements)
      }
    }
  end
end

if __FILE__ == $0
  ChromaticSubobject.demo
end
