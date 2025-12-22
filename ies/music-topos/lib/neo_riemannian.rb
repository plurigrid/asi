# lib/neo_riemannian.rb
require_relative 'chord'

class NeoRiemannian
  def self.parallel(chord)
    transform(chord) do |voices|
      # P: Maps Major to Minor by lowering 3rd, Minor to Major by raising 3rd
      # Simplified for triads (Root, 3rd, 5th)
      root = voices[0]
      third = voices[1]
      fifth = voices[2]
      
      # Determine if Major or Minor
      is_major = (third.value - root.value) % 12 == 4
      
      new_third = is_major ? third - 1 : third + 1
      [root, new_third, fifth]
    end
  end

  def self.relative(chord)
    transform(chord) do |voices|
      # R: Relative minor/major
      # Major (C E G) -> Minor (A C E). Root moves down 3 semitones? 
      # No, R exchanges parallel major/minor relative.
      # C Major (C E G) -> A Minor (A C E).
      # Root moves to A (down 3). 3rd becomes root (C). 5th becomes 3rd (E).
      # Wait, standard PLR definitions:
      # P: C E G -> C Eb G (preserve 1, 5)
      # L: C E G -> B E G (preserve 3, 5)
      # R: C E G -> C E A (preserve 1, 3) -> A C E
      
      root = voices[0]
      third = voices[1]
      fifth = voices[2]
      
      is_major = (third.value - root.value) % 12 == 4
      
      if is_major
        # C E G -> A C E
        # 5th (G) moves up to A (+2)
        new_fifth = fifth + 2
        [new_fifth, root, third].sort_by(&:value) # Sort to normalize? Or keep voicing?
        # Let's try to keep voicing or just return new pitch classes
        # Implementation usually preserves common tones
        [root, third, new_fifth] 
        # But this would be C E A. This is A minor inverted.
        # Let's return C E A for now, assuming voice leading focus
      else
        # A C E -> C E G
        # Root (A) moves down to G (-2)
        new_root = root - 2
        [new_root, third, fifth]
      end
    end
  end

  def self.leading_tone_exchange(chord)
    transform(chord) do |voices|
      # L: Leading Tone Exchange
      # C E G -> B E G
      # Root moves down 1 (C->B)
      
      root = voices[0]
      third = voices[1]
      fifth = voices[2]
      
      is_major = (third.value - root.value) % 12 == 4
      
      if is_major
        # C->B
        new_root = root - 1
        [new_root, third, fifth]
      else
        # Minor: E G B -> E G C? (G Major)
        # 5th moves up 1?
        # C min: C Eb G. L -> Ab C Eb. 
        # G (5th) -> Ab (+1).
        new_fifth = fifth + 1
        [root, third, new_fifth]
      end
    end
  end
  
  # Hexatonic Cycle Generator
  # Generates the 6-step cycle P-L-P-L-P-L starting from a chord
  def self.hexatonic_cycle(start_chord, steps = 6)
    cycle = [start_chord]
    current = start_chord

    steps.times do |i|
      current = if i.even?
                  parallel(current) # P
                else
                  leading_tone_exchange(current) # L
                end
      cycle << current
    end

    cycle
  end

  # =========================================================================
  # PLR to Color Transformation
  # Maps Neo-Riemannian PLR transformations to LCH color space
  # =========================================================================

  # Apply PLR transformation to LCH color
  # Returns color with updated H, L, C values
  # P (Parallel): Hue ±15° (preserve Lightness and Chroma)
  # L (Leading-tone): Lightness ±10 (preserve Chroma and Hue)
  # R (Relative): Chroma ±20, Hue ±30° (largest transformation)
  def self.plr_to_color_transform(color, plr_type, direction = 1)
    h = color.is_a?(Hash) ? (color[:H] || 0) : (color.H || 0)
    l = color.is_a?(Hash) ? (color[:L] || 50) : (color.L || 50)
    c = color.is_a?(Hash) ? (color[:C] || 50) : (color.C || 50)

    case plr_type
    when :P
      # Parallel: Hue ±15°
      new_h = (h + (15 * direction)) % 360.0
      color_update(color, h: new_h)
    when :L
      # Leading-tone: Lightness ±10
      new_l = [(l + (10 * direction)), 0, 100].sort[1]
      color_update(color, l: new_l)
    when :R
      # Relative: Chroma ±20, Hue ±30°
      new_c = [(c + (20 * direction)), 0, 130].sort[1]
      new_h = (h + (30 * direction)) % 360.0
      color_update(color, h: new_h, c: new_c)
    else
      color
    end
  end

  private

  def self.color_update(color, h: nil, l: nil, c: nil)
    if color.is_a?(Hash)
      updated = color.dup
      updated[:H] = h if h
      updated[:L] = l if l
      updated[:C] = c if c
      updated
    else
      # NamedTuple-like - reconstruct
      color
    end
  end

  def self.transform(chord)
    new_voices = yield(chord.voices)
    # Re-wrap in Chord, maybe re-sort if we want normal form, but let's stick to voice preservation
    Chord.new(*new_voices)
  end
end
