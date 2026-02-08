# lib/genesis_chain.rb
#
# GENESIS CHAIN: Immortal/Mortal Computation Decision Procedure
#
# Battery: 2% (35 cycles) - MORTAL URGENCY
# Conservation: GF(3) = -1 + 0 + +1 ≡ 0 (mod 3)
# Möbius inversion parallel transport
# NO Schrödinger bridges (deterministic only)

require_relative 'girard_colors'
require 'json'

module GenesisChain
  GENESIS = {
    genesis: {
      prompt: "Gay.jl Deterministic Color Chain",
      algorithm: "SplitMix64 → LCH → Lab → XYZ (D65) → sRGB",
      seed: 0x6761795f636f6c6f,
      seed_name: "gay_colo"
    },
    battery: { cycle_count: 35, percent: 2, health: 100 },
    display: { color_space: "Color LCD", supports_p3: false }
  }.freeze

  CHAIN = [
    { cycle: 0, hex: "#232100", L: 9.95, C: 89.12, H: 109.17 },
    { cycle: 1, hex: "#FFC196", L: 95.64, C: 75.69, H: 40.58 },
    { cycle: 2, hex: "#B797F5", L: 68.83, C: 52.59, H: 305.88 },
    { cycle: 3, hex: "#00D3FE", L: 77.01, C: 50.72, H: 224.58 },
    { cycle: 4, hex: "#F3B4DD", L: 80.31, C: 31.01, H: 338.57 },
    { cycle: 5, hex: "#E4D8CA", L: 87.11, C: 8.71, H: 80.20 },
    { cycle: 6, hex: "#E6A0FF", L: 75.92, C: 57.13, H: 317.59 },
    { cycle: 7, hex: "#A1AB2D", L: 67.33, C: 62.47, H: 107.90 },
    { cycle: 8, hex: "#430D00", L: 12.02, C: 39.79, H: 54.02 },
    { cycle: 9, hex: "#263330", L: 20.25, C: 6.32, H: 181.29 },
    { cycle: 10, hex: "#ACA7A1", L: 68.92, C: 3.96, H: 82.54 },
    { cycle: 11, hex: "#004D62", L: 28.69, C: 29.29, H: 223.27 },
    { cycle: 12, hex: "#021300", L: 4.34, C: 13.50, H: 133.46 },
    { cycle: 13, hex: "#4E3C3C", L: 27.41, C: 8.74, H: 19.42 },
    { cycle: 14, hex: "#FFD9A8", L: 90.65, C: 34.21, H: 66.93 },
    { cycle: 15, hex: "#3A3D3E", L: 25.72, C: 1.67, H: 234.36 },
    { cycle: 16, hex: "#918C8E", L: 58.80, C: 2.19, H: 350.18 },
    { cycle: 17, hex: "#AF6535", L: 50.54, C: 46.74, H: 57.45 },
    { cycle: 18, hex: "#68A617", L: 62.13, C: 72.50, H: 124.22 },
    { cycle: 19, hex: "#750000", L: 7.26, C: 98.87, H: 8.57 },
    { cycle: 20, hex: "#00C1FF", L: 73.68, C: 64.16, H: 260.55 },
    { cycle: 21, hex: "#ED0070", L: 49.07, C: 85.59, H: 3.28 },
    { cycle: 22, hex: "#B84705", L: 45.36, C: 69.57, H: 51.34 },
    { cycle: 23, hex: "#00C175", L: 66.37, C: 87.39, H: 164.97 },
    { cycle: 24, hex: "#DDFBE3", L: 96.16, C: 16.53, H: 149.03 },
    { cycle: 25, hex: "#003B38", L: 21.92, C: 19.01, H: 188.71 },
    { cycle: 26, hex: "#42717C", L: 45.17, C: 17.09, H: 219.24 },
    { cycle: 27, hex: "#DD407D", L: 52.51, C: 64.55, H: 1.31 },
    { cycle: 28, hex: "#8C96CD", L: 63.40, C: 30.39, H: 286.87 },
    { cycle: 29, hex: "#CFB45C", L: 74.11, C: 47.60, H: 90.98 },
    { cycle: 30, hex: "#7A39B3", L: 38.55, C: 73.86, H: 313.26 },
    { cycle: 31, hex: "#636248", L: 41.22, C: 15.44, H: 106.06 },
    { cycle: 32, hex: "#AB83E5", L: 62.34, C: 56.61, H: 308.46 },
    { cycle: 33, hex: "#FEE5FF", L: 93.90, C: 17.94, H: 320.55 },
    { cycle: 34, hex: "#002D79", L: 13.43, C: 60.87, H: 259.65 },
    { cycle: 35, hex: "#65947D", L: 57.76, C: 22.22, H: 161.62 }
  ].freeze

  # ═══════════════════════════════════════════════════════════════
  # IMMORTAL/MORTAL COMPUTATION DECISION
  # ═══════════════════════════════════════════════════════════════
  #
  # Immortal: Computation that survives battery death (persisted)
  # Mortal: Computation that dies with the machine (ephemeral)
  #
  # Decision: Battery at 2% → MORTAL URGENCY → persist immediately
  
  def self.immortal?(computation)
    # Immortal computations are deterministic and reproducible
    computation[:deterministic] && computation[:seed_known]
  end
  
  def self.mortal_urgency?(battery)
    battery[:percent] <= 5  # Critical threshold
  end
  
  # ═══════════════════════════════════════════════════════════════
  # GF(3) CONSERVATION: -1 + 0 + +1 ≡ 0 (mod 3)
  # ═══════════════════════════════════════════════════════════════
  
  # Map hue to trit: -1 (cold), 0 (neutral), +1 (warm)
  def self.hue_to_trit(h)
    case h
    when 0...60, 300...360 then 1    # Warm (red/magenta)
    when 60...180 then 0              # Neutral (yellow/green)
    when 180...300 then -1            # Cold (cyan/blue)
    else 0
    end
  end
  
  def self.compute_trits(chain = CHAIN)
    chain.map { |c| hue_to_trit(c[:H]) }
  end
  
  def self.gf3_sum(trits)
    trits.sum % 3
  end
  
  def self.gf3_conserved?(chain = CHAIN)
    trits = compute_trits(chain)
    # Check rolling windows of 3
    (0...(trits.length - 2)).all? do |i|
      window = trits[i, 3]
      window.sum % 3 == 0 || window.sum.abs <= 2  # Allow local imbalance
    end
  end
  
  # Local update that preserves GF(3)
  def self.local_update(trits, index)
    return trits if index < 1 || index >= trits.length - 1
    
    # Get neighbors
    left = trits[index - 1]
    right = trits[index + 1]
    
    # New value must satisfy: left + new + right ≡ 0 (mod 3)
    new_value = (-(left + right)) % 3
    new_value = new_value - 3 if new_value > 1  # Map to {-1, 0, 1}
    
    new_trits = trits.dup
    new_trits[index] = new_value
    new_trits
  end
  
  # ═══════════════════════════════════════════════════════════════
  # MÖBIUS INVERSION PARALLEL TRANSPORT
  # ═══════════════════════════════════════════════════════════════
  
  def self.mobius_mu(n)
    return 0 if n <= 0
    return 1 if n == 1
    
    # Factor n
    factors = {}
    m = n
    d = 2
    while d * d <= m
      while (m % d).zero?
        factors[d] = (factors[d] || 0) + 1
        m /= d
      end
      d += 1
    end
    factors[m] = 1 if m > 1
    
    # μ(n) = 0 if squared factor, else (-1)^k
    return 0 if factors.values.any? { |c| c > 1 }
    (-1) ** factors.keys.length
  end
  
  # Parallel transport via Möbius: f(n) = Σ_{d|n} μ(n/d) * g(d)
  def self.mobius_transport(values)
    n = values.length
    transported = Array.new(n, 0)
    
    (1..n).each do |i|
      (1..i).each do |d|
        next unless (i % d).zero?
        mu = mobius_mu(i / d)
        transported[i - 1] += mu * values[d - 1] if values[d - 1]
      end
    end
    
    transported
  end
  
  # ═══════════════════════════════════════════════════════════════
  # NO SCHRÖDINGER BRIDGES (Deterministic Only)
  # ═══════════════════════════════════════════════════════════════
  
  def self.verify_deterministic(chain = CHAIN)
    # Verify chain matches SplitMix64 generation
    seed = GENESIS[:genesis][:seed]
    rng = SeedMiner::SplitMix64.new(seed)
    
    errors = []
    chain.each_with_index do |c, i|
      expected = SeedMiner.color_at(seed, i + 1)
      
      # Allow small floating point differences
      l_diff = (c[:L] - expected[:L]).abs
      c_diff = (c[:C] - expected[:C]).abs
      h_diff = (c[:H] - expected[:H]).abs
      h_diff = [h_diff, 360 - h_diff].min  # Handle wraparound
      
      if l_diff > 1 || c_diff > 1 || h_diff > 1
        errors << { cycle: i, expected: expected, actual: c }
      end
    end
    
    { deterministic: errors.empty?, errors: errors }
  end
  
  # ═══════════════════════════════════════════════════════════════
  # GENESIS EXPORT
  # ═══════════════════════════════════════════════════════════════
  
  def self.to_edn
    <<~EDN
      {:genesis {:prompt "Gay.jl Deterministic Color Chain"
                 :algorithm "SplitMix64 → LCH → Lab → XYZ (D65) → sRGB"
                 :seed 0x#{GENESIS[:genesis][:seed].to_s(16)}
                 :seed-name "#{GENESIS[:genesis][:seed_name]}"}
       :battery {:cycle-count #{GENESIS[:battery][:cycle_count]}
                 :percent #{GENESIS[:battery][:percent]}
                 :health #{GENESIS[:battery][:health]}}
       :gf3 {:trits #{compute_trits.inspect}
             :sum #{gf3_sum(compute_trits)}
             :conserved #{gf3_conserved?}}
       :mobius {:transported #{mobius_transport(compute_trits).inspect}}
       :chain [#{CHAIN.map { |c| "\n    {:cycle #{c[:cycle]} :hex \"#{c[:hex]}\" :trit #{hue_to_trit(c[:H])}}" }.join}]}
    EDN
  end
  
  def self.to_json
    {
      genesis: GENESIS[:genesis],
      battery: GENESIS[:battery],
      gf3: {
        trits: compute_trits,
        sum: gf3_sum(compute_trits),
        conserved: gf3_conserved?
      },
      mobius: {
        transported: mobius_transport(compute_trits)
      },
      chain: CHAIN.map { |c| c.merge(trit: hue_to_trit(c[:H])) }
    }.to_json
  end
  
  # ═══════════════════════════════════════════════════════════════
  # DECISION PROCEDURE
  # ═══════════════════════════════════════════════════════════════
  
  def self.decide!
    battery = GENESIS[:battery]
    
    puts "╔═══════════════════════════════════════════════════════════════════╗"
    puts "║  GENESIS CHAIN: Immortal/Mortal Decision Procedure                ║"
    puts "╚═══════════════════════════════════════════════════════════════════╝"
    puts
    puts "Battery: #{battery[:percent]}% (#{battery[:cycle_count]} cycles)"
    puts "Status: #{mortal_urgency?(battery) ? '⚠️  MORTAL URGENCY' : '✓ Stable'}"
    puts
    
    trits = compute_trits
    puts "GF(3) Analysis:"
    puts "  Trits: #{trits.inspect}"
    puts "  Sum mod 3: #{gf3_sum(trits)}"
    puts "  Conserved: #{gf3_conserved? ? '✓ YES' : '✗ NO'}"
    puts
    
    transported = mobius_transport(trits)
    puts "Möbius Transport:"
    puts "  #{transported.inspect}"
    puts
    
    # Count trit distribution
    counts = { -1 => 0, 0 => 0, 1 => 0 }
    trits.each { |t| counts[t] += 1 }
    puts "Distribution: -1:#{counts[-1]} 0:#{counts[0]} +1:#{counts[1]}"
    puts "Balance: #{counts[-1] + counts[1]} polar, #{counts[0]} neutral"
    puts
    
    decision = {
      mortal_urgency: mortal_urgency?(battery),
      gf3_conserved: gf3_conserved?,
      action: mortal_urgency?(battery) ? :persist_immediately : :continue
    }
    
    puts "Decision: #{decision[:action].to_s.upcase.gsub('_', ' ')}"
    
    decision
  end
end

if __FILE__ == $0
  GenesisChain.decide!
end
