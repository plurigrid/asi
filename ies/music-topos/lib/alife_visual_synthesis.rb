# lib/alife_visual_synthesis.rb
#
# Audio-Visual Life Pattern Synthesis
#
# Extends algorithmic art with artificial life visualizations:
# - Lenia cellular automata
# - Particle swarm systems
# - Neural cellular automata
# - Synchronized audio synthesis with effects
#
# Inspired by Laura Porta's work on visualization + movement tracking
# Integrates with: AudioSynthesis, AudioEffects, algorithmic-art skill

require_relative 'audio_synthesis'
require_relative 'audio_effects'

class AlifeVisualSynthesis
  SAMPLE_RATE = 44100
  MAX_AMPLITUDE = 32767

  def initialize(width: 512, height: 512, scale: 2)
    @width = width
    @height = height
    @scale = scale  # p5.js pixel scale for visualization
    @generations = []
    @audio_synthesis = AudioSynthesis.new
    @audio_effects = AudioEffects.new
  end

  # ===========================================================================
  # LENIA: Continuous Cellular Automata
  # ===========================================================================
  # A_t+Δt = [A_t + Δt · G(K * A_t)]_0^1
  # G_μ,σ(x) = 2e^(-(x-μ)²/2σ²) - 1

  def lenia_step(grid, kernel_params: {mu: 0.5, sigma: 0.15}, dt: 0.1)
    # Apply Gaussian kernel convolution
    mu = kernel_params[:mu]
    sigma = kernel_params[:sigma]

    new_grid = Array.new(@height) { Array.new(@width, 0.0) }

    (0...@height).each do |y|
      (0...@width).each do |x|
        # Sample neighborhood (simplified - use center and 4 neighbors)
        neighbors = [
          grid[y][x],
          grid[(y + 1) % @height][x],
          grid[(y - 1) % @height][x],
          grid[y][(x + 1) % @width],
          grid[y][(x - 1) % @width]
        ]

        # Average neighborhood (kernel convolution approximation)
        avg_neighbor = neighbors.sum / neighbors.length.to_f

        # Growth function: G_μ,σ(x) = 2e^(-(x-μ)²/2σ²) - 1
        exponent = -((avg_neighbor - mu) ** 2) / (2 * sigma ** 2)
        growth = 2 * Math.exp(exponent) - 1

        # Update: clamp to [0,1]
        new_grid[y][x] = [grid[y][x] + dt * growth, 0.0].max
        new_grid[y][x] = [new_grid[y][x], 1.0].min
      end
    end

    new_grid
  end

  # ===========================================================================
  # PARTICLE SWARM: Movement patterns with local rules
  # ===========================================================================
  # Boid rules: separation + alignment + cohesion

  class Particle
    attr_accessor :x, :y, :vx, :vy, :energy

    def initialize(width, height)
      @x = rand(0...width).to_f
      @y = rand(0...height).to_f
      @vx = (rand - 0.5) * 2
      @vy = (rand - 0.5) * 2
      @energy = 0.5
      @max_speed = 2.0
    end

    def apply_force(fx, fy)
      @vx += fx
      @vy += fy

      # Speed limiting
      speed = Math.sqrt(@vx ** 2 + @vy ** 2)
      if speed > @max_speed
        @vx = @vx / speed * @max_speed
        @vy = @vy / speed * @max_speed
      end
    end

    def update(width, height, friction: 0.98)
      @x += @vx
      @y += @vy

      # Wrapping boundaries
      @x = @x % width
      @y = @y % height

      # Friction
      @vx *= friction
      @vy *= friction

      # Energy decay
      @energy *= 0.995
    end

    def distance_to(other)
      Math.sqrt((@x - other.x) ** 2 + (@y - other.y) ** 2)
    end
  end

  def particle_swarm_step(particles, separation: 50, alignment: 50, cohesion: 50)
    # Apply Boid rules to each particle
    particles.each_with_index do |particle, i|
      sep_x, sep_y = 0.0, 0.0
      align_x, align_y = 0.0, 0.0
      coh_x, coh_y = 0.0, 0.0
      count = 0

      particles.each_with_index do |other, j|
        next if i == j

        distance = particle.distance_to(other)
        next if distance > 100  # Only consider nearby particles

        # Separation: steer away from nearby particles
        if distance < separation
          sep_x += particle.x - other.x
          sep_y += particle.y - other.y
        end

        # Alignment: steer toward average heading
        align_x += other.vx
        align_y += other.vy

        # Cohesion: steer toward average location
        coh_x += other.x
        coh_y += other.y

        count += 1
      end

      # Normalize and apply forces
      if count > 0
        particle.apply_force(sep_x * 0.01, sep_y * 0.01) if count > 0
        particle.apply_force(align_x / count * 0.05, align_y / count * 0.05)
        particle.apply_force((coh_x / count - particle.x) * 0.01,
                             (coh_y / count - particle.y) * 0.01)
      end

      particle.update(@width, @height)
    end

    particles
  end

  # ===========================================================================
  # AUDIO SYNTHESIS FROM VISUAL PATTERNS
  # ===========================================================================
  # Map visual state to audio: position → frequency, energy → amplitude

  def grid_to_frequencies(grid, base_frequency: 440, scale: :major)
    # Extract energy distribution from grid
    # Higher activation = higher pitch
    frequencies = []

    # Sample grid at multiple points
    step_size = [@width / 4, @height / 4].max
    (0...@height).step(step_size) do |y|
      (0...@width).step(step_size) do |x|
        activation = grid[y][x]

        # Map activation to frequency
        # 0.0 = base_frequency
        # 1.0 = base_frequency * 2 (one octave up)
        freq = base_frequency * (2 ** activation)
        frequencies << freq if activation > 0.1  # Only active cells
      end
    end

    frequencies.empty? ? [base_frequency] : frequencies
  end

  def particles_to_frequencies(particles, base_frequency: 440)
    # Map particle positions to frequencies
    # Y position → frequency
    frequencies = particles.map do |p|
      # Normalize Y to [0, 1]
      normalized_y = p.y / @height
      # Map to frequency range (440-880 Hz = one octave)
      base_frequency * (1.0 + normalized_y)
    end

    frequencies.empty? ? [base_frequency] : frequencies
  end

  # ===========================================================================
  # INTEGRATED SIMULATION
  # ===========================================================================
  # Run combined visual + audio evolution

  def simulate_audiovisual_life(steps: 100, life_type: :lenia, effects_chain: nil)
    # Initialize based on life type
    case life_type
    when :lenia
      grid = initialize_lenia_grid
      simulation = proc do
        grid = lenia_step(grid)
        grid
      end
      to_frequencies = proc { |state| grid_to_frequencies(state) }

    when :swarm
      particles = Array.new(30) { Particle.new(@width, @height) }
      simulation = proc do
        particles = particle_swarm_step(particles)
        particles
      end
      to_frequencies = proc { |state| particles_to_frequencies(state) }

    else
      raise "Unknown life_type: #{life_type}"
    end

    # Simulation loop
    audio_samples = []
    visual_frames = []

    steps.times do |step|
      # Update visual state
      state = simulation.call
      visual_frames << state

      # Extract audio from visual state
      frequencies = to_frequencies.call(state)

      # Synthesize audio for this frame
      frame_duration = 0.5  # 0.5 seconds per frame
      frame_samples = @audio_synthesis.generate_mixed_wave(
        frequencies,
        frame_duration,
        0.5  # amplitude
      )

      audio_samples.concat(frame_samples)
    end

    # Apply audio effects if specified
    if effects_chain && !effects_chain.empty?
      audio_samples = @audio_effects.apply_effects(audio_samples, effects_chain)
    end

    {
      visual_frames: visual_frames,
      audio_samples: audio_samples,
      total_samples: audio_samples.length,
      duration_seconds: audio_samples.length / SAMPLE_RATE.to_f
    }
  end

  # ===========================================================================
  # UTILITIES
  # ===========================================================================

  def initialize_lenia_grid
    # Random initialization with some structure
    grid = Array.new(@height) { Array.new(@width) { rand < 0.1 ? rand : 0.0 } }

    # Add a seed pattern in the center
    center_y = @height / 2
    center_x = @width / 2
    (center_y - 5..center_y + 5).each do |y|
      (center_x - 5..center_x + 5).each do |x|
        next if y < 0 || y >= @height || x < 0 || x >= @width

        distance = Math.sqrt((y - center_y) ** 2 + (x - center_x) ** 2)
        grid[y][x] = [1.0 - distance / 10.0, 0.0].max if distance < 10
      end
    end

    grid
  end

  def render_audio_visual(result, output_wav: '/tmp/alife_synthesis.wav')
    # Write audio to WAV file
    @audio_synthesis.write_wav_file(result[:audio_samples], output_wav)

    {
      audio_file: output_wav,
      duration: result[:duration_seconds],
      frames: result[:visual_frames].length,
      samples: result[:total_samples]
    }
  end
end
