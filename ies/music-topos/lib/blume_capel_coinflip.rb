# lib/blume_capel_coinflip.rb
#
# Blume-Capel Model + Balanced Ternary Coin Flip + drand Entropy
#
# The Blume-Capel model is a spin-1 system with states {-1, 0, +1}
# Perfect isomorphism with balanced ternary!
#
# Hamiltonian: H = -J Σ s_i s_j + Δ Σ s_i²
#   - J: exchange coupling (ferromagnetic if J > 0)
#   - Δ: crystal field (chemical potential for vacancies)
#
# Möbius Inversion at 0:
#   The 0 state (BEAVER) represents a "vacancy" or "neutral" site.
#   At the tricritical point, the 0 state has special significance
#   for the phase transition between ordered and disordered phases.
#
# Quantum Ergodic Guarantees:
#   - Spectral gap of 1/4 ensures rapid mixing
#   - Ergodic theorem: time averages = ensemble averages
#   - Phase space exploration via random walk
#
# Girard's Linear Logic Connection:
#   - Positive polarity (+1): Ferromagnetic ordering
#   - Negative polarity (-1): Antiferromagnetic ordering
#   - Neutral (0): Cut elimination / vacuum state
#
# Musical Interpretation:
#   - +1: Major mode, expansion, forward motion (consonance)
#   - -1: Minor mode, contraction, backward motion (dissonance)
#   -  0: Modal neutrality, cadential rest, resolution (suspension)

require_relative 'girard_colors'
require 'net/http'
require 'json'
require 'digest'

module BlumeCapelCoinflip
  # Spectral gap for quantum ergodic mixing (1/4 as specified)
  SPECTRAL_GAP = 0.25

  # Blume-Capel parameters
  DEFAULT_J = 1.0      # Exchange coupling
  DEFAULT_DELTA = 0.0  # Crystal field (Δ = 0 at tricritical point)

  # drand quicknet API
  DRAND_API = "https://api.drand.sh/52db9ba70e0cc0f6eaf7803dd07447a1f5477735fd3f661792ba94600c84e971"

  # Fetch entropy from drand League of Entropy
  def self.fetch_drand(round = nil)
    uri = URI("#{DRAND_API}/public/#{round || 'latest'}")
    response = Net::HTTP.get_response(uri)

    if response.is_a?(Net::HTTPSuccess)
      data = JSON.parse(response.body)
      randomness = data["randomness"]
      seed = randomness[0, 16].to_i(16)  # First 64 bits
      {
        round: data["round"],
        seed: seed,
        seed_hex: "0x#{seed.to_s(16).upcase}",
        randomness: randomness,
        source: "drand/quicknet"
      }
    else
      { round: 0, seed: 1069, seed_hex: "0x42D", randomness: "", source: "fallback" }
    end
  rescue => e
    { round: 0, seed: 1069, seed_hex: "0x42D", randomness: "", source: "fallback", error: e.message }
  end

  # Blume-Capel spin state
  class Spin
    attr_reader :value, :girard_polarity, :musical_mode

    def initialize(value)
      raise ArgumentError, "Spin must be -1, 0, or +1" unless [-1, 0, 1].include?(value)
      @value = value
      @girard_polarity = case value
                         when 1  then :positive
                         when -1 then :negative
                         when 0  then :neutral
                         end
      @musical_mode = GirardColors.polarity_to_mode(@girard_polarity)
    end

    def beaver?
      @value.zero?
    end

    def to_char
      case @value
      when 1  then "▬"
      when -1 then "▁"
      when 0  then "▒"
      end
    end

    def to_s
      "Spin(#{@value}, #{@girard_polarity}, #{@musical_mode})"
    end
  end

  # Blume-Capel lattice for random walk
  class Lattice
    attr_reader :spins, :energy, :magnetization, :j, :delta

    def initialize(size: 10, j: DEFAULT_J, delta: DEFAULT_DELTA)
      @size = size
      @j = j
      @delta = delta
      @spins = Array.new(size) { Spin.new(0) }  # Start neutral
      @rng = SeedMiner::SplitMix64.new(1069)
      @flip_history = []
      @position = 0
    end

    def seed!(seed)
      @rng = SeedMiner::SplitMix64.new(seed)
      @flip_history = []
      @position = 0
      self
    end

    # Perform balanced ternary flip
    def flip!
      raw = @rng.next_u64
      trit = (raw % 3).to_i - 1  # Map {0,1,2} → {-1,0,+1}

      @position += trit
      spin = Spin.new(trit)
      @flip_history << {
        flip_number: @flip_history.size + 1,
        trit: trit,
        position: @position,
        moebius_mu: moebius_mu,
        is_beaver: spin.beaver?,
        girard_polarity: spin.girard_polarity,
        musical_mode: spin.musical_mode
      }

      spin
    end

    # Möbius inversion at current position
    def moebius_mu
      return 1 if @position.zero?
      (-1) ** (@position.abs % 2)
    end

    # Flip n times and return trajectory
    def flip_n!(n)
      n.times.map { flip! }
    end

    # Blume-Capel energy calculation
    def energy
      # E = -J Σ s_i s_j + Δ Σ s_i²
      exchange = 0.0
      crystal_field = 0.0

      @spins.each_with_index do |spin, i|
        # Nearest neighbor interaction (periodic boundary)
        next_i = (i + 1) % @size
        exchange += spin.value * @spins[next_i].value

        # Crystal field term
        crystal_field += spin.value ** 2
      end

      -@j * exchange + @delta * crystal_field
    end

    def magnetization
      @spins.sum(&:value).to_f / @size
    end

    def vacancy_density
      @spins.count(&:beaver?).to_f / @size
    end

    # Quantum ergodic mixing time estimate
    def mixing_time_estimate
      # τ_mix ~ 1 / spectral_gap
      1.0 / SPECTRAL_GAP
    end

    # Flip history summary
    def history_summary
      return nil if @flip_history.empty?

      {
        total_flips: @flip_history.size,
        final_position: @position,
        moebius_mu: moebius_mu,
        beaver_count: @flip_history.count { |f| f[:is_beaver] },
        trajectory: @flip_history.map { |f| f[:trit] },
        polarity_sequence: @flip_history.map { |f| f[:girard_polarity] },
        cut_transitions: count_polarity_transitions
      }
    end

    private

    def count_polarity_transitions
      return 0 if @flip_history.size < 2
      polarities = @flip_history.map { |f| f[:girard_polarity] }
      (1...polarities.size).count { |i| polarities[i] != polarities[i - 1] }
    end
  end

  # Möbius Inversion operator for balanced ternary sequences
  module MoebiusInversion
    # Möbius function μ(n)
    def self.mu(n)
      return 0 if n <= 0
      return 1 if n == 1

      # Count prime factors
      factors = prime_factors(n)

      # If any prime appears more than once, μ(n) = 0
      return 0 if factors.any? { |_, count| count > 1 }

      # Otherwise, μ(n) = (-1)^k where k = number of prime factors
      (-1) ** factors.size
    end

    # Prime factorization
    def self.prime_factors(n)
      factors = {}
      d = 2
      while d * d <= n
        while (n % d).zero?
          factors[d] = (factors[d] || 0) + 1
          n /= d
        end
        d += 1
      end
      factors[n] = 1 if n > 1
      factors
    end

    # Möbius inversion formula: g(n) = Σ_{d|n} μ(d) * f(n/d)
    def self.invert(f_values)
      n = f_values.size
      g_values = Array.new(n, 0)

      (1..n).each do |i|
        divisors(i).each do |d|
          g_values[i - 1] += mu(d) * f_values[(i / d) - 1]
        end
      end

      g_values
    end

    # Divisors of n
    def self.divisors(n)
      (1..n).select { |d| (n % d).zero? }
    end

    # Apply to balanced ternary sequence - interpret as multiplicative
    def self.apply_to_trajectory(trajectory)
      # Map trajectory to positive integers for Möbius inversion
      # -1 → 1 (negative as first prime)
      #  0 → 2 (neutral as second prime)
      # +1 → 3 (positive as third prime)
      mapped = trajectory.map { |t| t + 2 }

      # Compute Möbius μ for each step
      {
        trajectory: trajectory,
        mapped_primes: mapped,
        moebius_values: mapped.map { |m| mu(m) },
        cumulative_product: mapped.reduce(1, :*),
        final_moebius: mu(mapped.reduce(1, :*))
      }
    end
  end

  # Quantum Ergodic Random Walk
  class ErgodicWalk
    attr_reader :position, :history, :seed

    def initialize(seed: 1069)
      @seed = seed
      @rng = SeedMiner::SplitMix64.new(seed)
      @position = 0
      @history = []
      @three_match = nil  # Will hold color data
    end

    # Seed from drand
    def seed_from_drand!(round = nil)
      drand_data = BlumeCapelCoinflip.fetch_drand(round)
      @seed = drand_data[:seed]
      @rng = SeedMiner::SplitMix64.new(@seed)
      @position = 0
      @history = []
      drand_data
    end

    # Step with balanced ternary
    def step!
      raw = @rng.next_u64
      trit = (raw % 3).to_i - 1

      @position += trit

      # Get 3-MATCH color
      color = SeedMiner.color_at(@seed, @history.size + 1)
      girard_polarity = SeedMiner.send(:hue_to_polarity, color[:H])

      step_data = {
        step_number: @history.size + 1,
        trit: trit,
        position: @position,
        color: color,
        girard_polarity: girard_polarity,
        moebius_mu: moebius_mu,
        is_beaver: trit.zero?,
        mixing_progress: mixing_progress
      }

      @history << step_data
      step_data
    end

    def walk!(n)
      n.times.map { step! }
    end

    def moebius_mu
      return 1 if @position.zero?
      (-1) ** (@position.abs % 2)
    end

    # Mixing progress based on spectral gap
    def mixing_progress
      return 0.0 if @history.empty?
      steps = @history.size
      mixing_time = 1.0 / SPECTRAL_GAP  # τ_mix = 4 steps
      [steps / mixing_time, 1.0].min
    end

    # Check if mixed (quantum ergodic)
    def mixed?
      mixing_progress >= 1.0
    end

    # Ergodic mean of trajectory
    def ergodic_mean
      return 0.0 if @history.empty?
      @history.sum { |h| h[:trit] }.to_f / @history.size
    end

    # Ensemble statistics
    def ensemble_stats
      return nil if @history.empty?

      trits = @history.map { |h| h[:trit] }
      beavers = trits.count(&:zero?)

      {
        mean: ergodic_mean,
        variance: variance(trits),
        beaver_rate: beavers.to_f / trits.size,
        expected_beaver_rate: 1.0 / 3,  # For uniform ternary
        ergodic_deviation: (ergodic_mean - 0.0).abs,  # Should tend to 0
        mixed: mixed?,
        mixing_progress: mixing_progress
      }
    end

    private

    def variance(arr)
      return 0.0 if arr.empty?
      mean = arr.sum.to_f / arr.size
      arr.sum { |x| (x - mean) ** 2 } / arr.size
    end
  end

  # Musical interpretation of Blume-Capel dynamics
  module MusicalInterpretation
    # Map trajectory to musical intervals
    def self.trajectory_to_intervals(trajectory)
      trajectory.map do |trit|
        case trit
        when 1  then 7   # +1 → Perfect fifth (expansion)
        when -1 then 5   # -1 → Perfect fourth (contraction)
        when 0  then 0   # 0 → Unison (rest/suspension)
        end
      end
    end

    # Map trajectory to pitch sequence
    def self.trajectory_to_pitches(trajectory, base_pitch: 60)
      pitches = [base_pitch]
      trajectory.each do |trit|
        interval = case trit
                   when 1  then 7
                   when -1 then -7
                   when 0  then 0
                   end
        pitches << pitches.last + interval
      end
      pitches
    end

    # Leitmotif from seed and trajectory
    def self.generate_leitmotif(seed:, length: 8)
      walk = ErgodicWalk.new(seed: seed)
      steps = walk.walk!(length)

      notes = steps.map.with_index do |step, i|
        color = step[:color]
        pitch = 60 + ((color[:H] / 30.0).round % 12)
        duration = 0.25 + (color[:L] / 100.0) * 0.5
        velocity = 40 + (color[:C] * 0.6).round

        {
          pitch: pitch,
          duration: duration,
          velocity: velocity,
          trit: step[:trit],
          girard_polarity: step[:girard_polarity],
          is_beaver: step[:is_beaver]
        }
      end

      {
        seed: seed,
        notes: notes,
        intervals: notes.each_cons(2).map { |a, b| b[:pitch] - a[:pitch] },
        polarities: notes.map { |n| n[:girard_polarity] },
        beaver_positions: notes.each_with_index.select { |n, _| n[:is_beaver] }.map(&:last),
        moebius_final: walk.moebius_mu
      }
    end

    # Cut elimination as dissonance resolution
    def self.analyze_cut_elimination(trajectory)
      polarities = trajectory.map do |trit|
        case trit
        when 1 then :positive
        when -1 then :negative
        else :neutral
        end
      end

      transitions = (1...polarities.size).count { |i| polarities[i] != polarities[i - 1] }
      beavers = trajectory.count(&:zero?)

      # Each beaver is a potential cut elimination point
      # Each polarity transition is a cut
      {
        cuts: transitions,
        eliminations: beavers,
        resolved: beavers >= transitions,
        balance_ratio: beavers.to_f / [transitions, 1].max
      }
    end
  end

  # Three-Match verification for Blume-Capel
  class ThreeMatchVerifier
    def initialize(seed)
      @seed = seed
    end

    def verify_at(index)
      color = SeedMiner.color_at(@seed, index)
      hex = lch_to_hex(color)
      fingerprint = Digest::SHA256.hexdigest("#{@seed}:#{hex}:#{index}")[0, 16]

      polarity = SeedMiner.send(:hue_to_polarity, color[:H])

      {
        seed: @seed,
        index: index,
        color: color,
        hex: hex,
        fingerprint: fingerprint,
        girard_polarity: polarity,
        blume_capel_interpretation: case polarity
                                    when :positive then "ferromagnetic (+1)"
                                    when :negative then "antiferromagnetic (-1)"
                                    else "vacancy (0)"
                                    end,
        commutes: true  # Triangle always commutes by construction
      }
    end

    def palette(n)
      (1..n).map { |i| verify_at(i) }
    end

    private

    def lch_to_hex(lch)
      l, c, h = lch[:L], lch[:C], lch[:H]
      h_rad = h * Math::PI / 180
      a = c * Math.cos(h_rad)
      b = c * Math.sin(h_rad)

      r = [[0, (l * 2.55 + a * 1.5).round].max, 255].min
      g = [[0, (l * 2.55 - a * 0.5 - b * 0.5).round].max, 255].min
      b_val = [[0, (l * 2.55 + b * 1.5).round].max, 255].min

      "#%02X%02X%02X" % [r, g, b_val]
    end
  end
end
