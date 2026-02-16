# ХРОМАТИЧЕСКИЙ ПЕПТИД САМОВАР
# /xrəʊˈmætɪk ˈpɛptaɪd ˈsaməvar/
# Braille: ⠭⠏⠎

module ChromaticPeptideSamovar
  AMINO_TRITS = {
    'A' => 0,  'R' => 1,  'N' => -1, 'D' => -1, 'C' => 0,
    'Q' => 0,  'E' => -1, 'G' => 0,  'H' => 1,  'I' => 1,
    'L' => 1,  'K' => 1,  'M' => 0,  'F' => 1,  'P' => 0,
    'S' => -1, 'T' => -1, 'V' => -1, 'W' => 1,  'Y' => 0
  }.freeze

  AMINO_IPA = {
    'A' => '/ˈælə/',  'R' => '/ˈɑːdʒ/', 'N' => '/ˈæsn/',  'D' => '/ˈæsp/',
    'C' => '/sɪs/',   'Q' => '/ɡlʌn/',  'E' => '/ɡluː/',  'G' => '/ɡlaɪ/',
    'H' => '/hɪs/',   'I' => '/aɪl/',   'L' => '/luː/',   'K' => '/laɪs/',
    'M' => '/mɛt/',   'F' => '/fiː/',   'P' => '/prəʊ/',  'S' => '/sɛr/',
    'T' => '/θriː/',  'V' => '/væl/',   'W' => '/trɪp/',  'Y' => '/taɪr/'
  }.freeze

  VOWELS = %w[ɑ æ e i ɪ ə ʊ u ɔ o ʌ a].freeze
  CONSONANTS = { -1 => %w[b d g v z], 0 => %w[m n ŋ l r], 1 => %w[p t k f s] }.freeze

  # SplitMix64 constants
  GOLDEN = 0x9E3779B97F4A7C15
  MIX1 = 0xBF58476D1CE4E5B9
  MIX2 = 0x94D049BB133111EB
  MASK64 = 0xFFFFFFFFFFFFFFFF

  class Generator
    def initialize(seed)
      @state = seed & MASK64
    end

    def next_u64
      @state = (@state + GOLDEN) & MASK64
      z = @state
      z = ((z ^ (z >> 30)) * MIX1) & MASK64
      z = ((z ^ (z >> 27)) * MIX2) & MASK64
      z ^ (z >> 31)
    end

    def next_float
      next_u64.to_f / MASK64.to_f
    end

    def color_at(index)
      # Deterministic: reset and skip to index
      temp = self.class.new(@state)
      index.times { temp.next_u64 }
      
      l = 10 + temp.next_float * 85
      c = temp.next_float * 100
      h = temp.next_float * 360
      
      trit = case h
             when 0...60, 300...360 then 1
             when 60...180 then 0
             else -1
             end

      { L: l, C: c, H: h, trit: trit, hex: oklch_to_hex(l, c, h) }
    end

    private

    def oklch_to_hex(l, c, h)
      # Simplified OkLCH → RGB
      h_rad = h * Math::PI / 180
      a = c * Math.cos(h_rad) / 100
      b = c * Math.sin(h_rad) / 100
      l_norm = l / 100.0

      # OkLab → linear RGB (approximate)
      l_ = l_norm + 0.3963377774 * a + 0.2158037573 * b
      m_ = l_norm - 0.1055613458 * a - 0.0638541728 * b
      s_ = l_norm - 0.0894841775 * a - 1.2914855480 * b

      l3, m3, s3 = l_**3, m_**3, s_**3

      r = 4.0767416621 * l3 - 3.3077115913 * m3 + 0.2309699292 * s3
      g = -1.2684380046 * l3 + 2.6097574011 * m3 - 0.3413193965 * s3
      b = -0.0041960863 * l3 - 0.7034186147 * m3 + 1.7076147010 * s3

      to_byte = ->(x) { [[0, (x * 255).to_i].max, 255].min }
      format('#%02X%02X%02X', to_byte.call(r), to_byte.call(g), to_byte.call(b))
    end
  end

  def self.brew(peptide_sequence, seed: 0x5A00000)
    gen = Generator.new(seed)

    peptide_sequence.upcase.chars.map.with_index do |aa, i|
      next nil unless AMINO_TRITS.key?(aa)

      trit = AMINO_TRITS[aa]
      color = gen.color_at(i)
      phoneme = color_to_phoneme(color, trit, i)

      {
        position: i,
        amino_acid: aa,
        trit: trit,
        color: color,
        ipa: AMINO_IPA[aa],
        phoneme: phoneme,
        braille: trit_to_braille(trit)
      }
    end.compact
  end

  def self.express_phonetically(chain)
    '/' + chain.map { |c| c[:phoneme] }.join('.') + '/'
  end

  def self.express_braille(chain)
    chain.map { |c| c[:braille] }.join
  end

  def self.gf3_balanced?(peptide)
    sum = peptide.upcase.chars.sum { |aa| AMINO_TRITS[aa] || 0 }
    sum % 3 == 0
  end

  def self.find_balanced_suffix(peptide)
    sum = peptide.upcase.chars.sum { |aa| AMINO_TRITS[aa] || 0 }
    needed = (-sum) % 3
    needed = needed == 2 ? -1 : needed

    AMINO_TRITS.find { |_, v| v == needed }&.first
  end

  private_class_method def self.trit_to_braille(trit)
    case trit
    when -1 then '⠁'
    when 0  then '⠂'
    when 1  then '⠄'
    end
  end

  private_class_method def self.color_to_phoneme(color, trit, index)
    vowel_idx = (color[:H] / 30).to_i % 12
    consonant = CONSONANTS[trit][index % 5]
    consonant + VOWELS[vowel_idx]
  end
end

# CLI interface
if __FILE__ == $0
  require 'yaml'
  
  peptide = ARGV[0] || 'GALS'
  
  puts "☕ САМОВАР brewing: #{peptide}"
  puts "   /xrəʊˈmætɪk ˈpɛptaɪd ˈsaməvar/"
  puts

  chain = ChromaticPeptideSamovar.brew(peptide)
  
  puts "Position | AA | Trit | Color   | Phoneme | Braille"
  puts "---------|----|----- |---------|---------|--------"
  
  chain.each do |c|
    printf "%-8d | %s  | %+d   | %s | %-7s | %s\n",
           c[:position], c[:amino_acid], c[:trit], 
           c[:color][:hex], c[:phoneme], c[:braille]
  end
  
  sum = chain.sum { |c| c[:trit] }
  balanced = sum % 3 == 0
  
  puts
  puts "GF(3): #{chain.map { |c| c[:trit] }.join(' + ')} = #{sum} #{balanced ? '✓ BALANCED' : '✗ UNBALANCED'}"
  puts "IPA:     #{ChromaticPeptideSamovar.express_phonetically(chain)}"
  puts "Braille: #{ChromaticPeptideSamovar.express_braille(chain)}"
  
  unless balanced
    fix = ChromaticPeptideSamovar.find_balanced_suffix(peptide)
    puts "Fix:     Add '#{fix}' to balance → #{peptide}#{fix}"
  end
end
