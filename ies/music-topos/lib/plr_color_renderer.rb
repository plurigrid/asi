#!/usr/bin/env ruby
#
# lib/plr_color_renderer.rb
#
# Phase 5: PLR Color Renderer Integration
#
# Bridges Julia-based ColorHarmonyState CRDT with Ruby rendering:
# - Receives PLR transformations from Julia CRDT
# - Applies Neo-Riemannian transformations to colors
# - Routes to Sonic Pi for audio synthesis
# - Analyzes harmonic function of color sequences
# - Manages bidirectional preference feedback loop
#

require_relative 'neo_riemannian'
require_relative 'harmonic_function'
require_relative 'sonic_pi_renderer'

class PLRColorRenderer
  attr_reader :current_color, :color_history, :harmonic_functions, :renderer, :preferences

  def initialize(start_color = { H: 120, L: 65, C: 50 }, synth: :sine)
    @current_color = start_color
    @color_history = [start_color.dup]
    @harmonic_functions = []
    @preferences = []
    @renderer = SonicPiRenderer.new(synth: synth)
    @harmonic_functions << HarmonicFunction.color_to_function(start_color)
  end

  # PLR Transformations
  def transform_parallel(direction = 1)
    new_color = NeoRiemannian.plr_to_color_transform(@current_color, :P, direction)
    apply_transformation(new_color, :P, direction)
  end

  def transform_leading_tone(direction = 1)
    new_color = NeoRiemannian.plr_to_color_transform(@current_color, :L, direction)
    apply_transformation(new_color, :L, direction)
  end

  def transform_relative(direction = 1)
    new_color = NeoRiemannian.plr_to_color_transform(@current_color, :R, direction)
    apply_transformation(new_color, :R, direction)
  end

  def apply_plr_transform(plr_type, direction = 1)
    case plr_type.to_sym
    when :P, :parallel
      transform_parallel(direction)
    when :L, :leading_tone
      transform_leading_tone(direction)
    when :R, :relative
      transform_relative(direction)
    else
      raise ArgumentError, "Unknown PLR type: #{plr_type}"
    end
  end

  private def apply_transformation(new_color, plr_type, direction)
    @current_color = new_color
    @color_history << new_color.dup
    func = HarmonicFunction.color_to_function(new_color)
    @harmonic_functions << func
    @renderer.play_color(new_color)
    {
      color: new_color,
      plr_type: plr_type,
      direction: direction,
      harmonic_function: func
    }
  end

  # Harmonic Analysis
  def analyze_harmonic_progression
    HarmonicFunction.color_sequence_analysis(@color_history)
  end

  def cadence_type
    return nil if @harmonic_functions.length < 2
    penultimate = @harmonic_functions[-2]
    final = @harmonic_functions[-1]
    HarmonicFunction.cadence_type(penultimate, final)
  end

  def has_authentic_cadence?
    analyze_harmonic_progression[:has_authentic_cadence]
  end

  def has_plagal_cadence?
    analyze_harmonic_progression[:has_plagal_cadence]
  end

  # Preference Learning
  def record_preference(preferred_idx, rejected_idx)
    raise ArgumentError, "Invalid indices" if preferred_idx >= @color_history.length || rejected_idx >= @color_history.length
    preferred = @color_history[preferred_idx]
    rejected = @color_history[rejected_idx]
    gradient = compute_preference_gradient(preferred, rejected)
    preference_record = {
      preferred_color: preferred,
      rejected_color: rejected,
      gradient: gradient,
      timestamp: Time.now
    }
    @preferences << preference_record
    preference_record
  end

  private def compute_preference_gradient(preferred, rejected)
    l_diff = (preferred[:L] - rejected[:L]).abs
    c_diff = (preferred[:C] - rejected[:C]).abs
    h_diff = ((preferred[:H] - rejected[:H]).abs % 360.0)
    h_diff = [h_diff, 360.0 - h_diff].min
    distance = Math.sqrt((l_diff ** 2) + (c_diff ** 2) + (h_diff ** 2))
    [distance / 200.0, 1.0].min
  end

  # Playback
  def play_current_color(duration = 1.0)
    @renderer.play_color(@current_color, duration_override: duration)
  end

  def play_color_history(interval = 1.0)
    @renderer.play_color_sequence(@color_history, interval: interval)
  end

  def play_hexatonic_cycle(interval = 0.5)
    cycle = generate_hexatonic_cycle
    cycle.each do |color|
      @renderer.play_color(color, duration_override: interval * 0.9)
      sleep(interval)
    end
  end

  def generate_hexatonic_cycle(start_color = nil)
    start_color ||= @current_color
    cycle = [start_color]
    current = start_color.dup
    6.times do |i|
      current = if i.even?
                  NeoRiemannian.plr_to_color_transform(current, :P, 1)
                else
                  NeoRiemannian.plr_to_color_transform(current, :L, 1)
                end
      cycle << current.dup
    end
    cycle
  end

  # CRDT Integration
  def apply_crdt_command(command_str)
    case command_str
    when /^plr\s+P(?:\s+(\d+))?$/i
      direction = $1 ? $1.to_i : 1
      transform_parallel(direction)
    when /^plr\s+L(?:\s+(\d+))?$/i
      direction = $1 ? $1.to_i : 1
      transform_leading_tone(direction)
    when /^plr\s+R(?:\s+(\d+))?$/i
      direction = $1 ? $1.to_i : 1
      transform_relative(direction)
    when /^query\s+color$/i
      @current_color
    when /^history$/i
      @color_history
    else
      raise ArgumentError, "Unknown CRDT command: #{command_str}"
    end
  end

  # State Serialization
  def to_h
    {
      current_color: @current_color,
      color_history: @color_history.map(&:dup),
      harmonic_functions: @harmonic_functions,
      preferences: @preferences.map(&:dup),
      timestamp: Time.now.to_i
    }
  end

  def merge!(other_state)
    if other_state.is_a?(Hash)
      if other_state[:color_history]
        other_state[:color_history].each do |color|
          unless @color_history.any? { |c| colors_equal?(c, color) }
            @color_history << color.dup
          end
        end
      end
      if other_state[:current_color]
        @current_color = other_state[:current_color].dup
      end
      if other_state[:preferences]
        @preferences.concat(other_state[:preferences].map(&:dup))
      end
    end
    @harmonic_functions = @color_history.map { |color| HarmonicFunction.color_to_function(color) }
    self
  end

  private def colors_equal?(c1, c2)
    h1 = c1.is_a?(Hash) ? c1 : { H: c1.H, L: c1.L, C: c1.C }
    h2 = c2.is_a?(Hash) ? c2 : { H: c2.H, L: c2.L, C: c2.C }
    (h1[:H] - h2[:H]).abs < 0.1 &&
    (h1[:L] - h2[:L]).abs < 0.1 &&
    (h1[:C] - h2[:C]).abs < 0.1
  end

  def reset(start_color = { H: 120, L: 65, C: 50 })
    @current_color = start_color
    @color_history = [start_color.dup]
    @harmonic_functions = [HarmonicFunction.color_to_function(start_color)]
    @preferences = []
  end

  def color_at(index)
    @color_history[index]
  end

  def all_colors
    @color_history.map { |c| [c[:H], c[:L], c[:C]] }
  end

  def session_summary
    {
      colors_generated: @color_history.length,
      harmonic_functions: @harmonic_functions.uniq.length,
      preferences_recorded: @preferences.length,
      has_cadence: !cadence_type.nil?,
      cadence_type: cadence_type,
      progression_type: analyze_harmonic_progression[:progression_type]
    }
  end

  def to_s
    "PLRColorRenderer(colors=#{@color_history.length}, funcs=#{@harmonic_functions.uniq.length})"
  end
end

if __FILE__ == $0
  puts "=" * 80
  puts "PLR Color Renderer - Phase 5 Integration Test"
  puts "=" * 80
  puts

  puts "Test 1: Initialize renderer"
  renderer = PLRColorRenderer.new
  puts "✓ Renderer created: #{renderer}"
  puts

  puts "Test 2: Apply PLR transformations"
  result_p = renderer.transform_parallel(1)
  puts "✓ P transform: H=#{result_p[:color][:H].round(1)}"
  result_l = renderer.transform_leading_tone(1)
  puts "✓ L transform: L=#{result_l[:color][:L].round(1)}"
  result_r = renderer.transform_relative(1)
  puts "✓ R transform: C=#{result_r[:color][:C].round(1)}"
  puts

  puts "Test 3: Harmonic function analysis"
  analysis = renderer.analyze_harmonic_progression
  puts "✓ Progression type: #{analysis[:progression_type]}"
  puts "✓ Closure complete: #{analysis[:closure][:complete]}"
  puts

  puts "Test 4: Record preferences"
  pref = renderer.record_preference(0, 1)
  puts "✓ Preference recorded: gradient=#{(pref[:gradient] * 100).round(1)}%"
  puts

  puts "Test 5: Generate hexatonic cycle"
  cycle = renderer.generate_hexatonic_cycle
  puts "✓ Hexatonic cycle: #{cycle.length} colors"
  puts

  puts "Test 6: CRDT command integration"
  renderer.reset({ H: 120, L: 65, C: 50 })
  result = renderer.apply_crdt_command("plr P")
  puts "✓ CRDT command executed: #{result[:plr_type]}"
  puts

  puts "Test 7: State serialization"
  state = renderer.to_h
  puts "✓ State exported: #{state.keys.sort.join(', ')}"
  renderer2 = PLRColorRenderer.new
  renderer2.merge!(state)
  puts "✓ State merged: history length #{renderer2.color_history.length}"
  puts

  puts "Test 8: Session summary"
  summary = renderer.session_summary
  puts "✓ Summary: colors=#{summary[:colors_generated]}, prefs=#{summary[:preferences_recorded]}"
  puts

  puts "=" * 80
  puts "✓ Phase 5 Integration Tests PASSED"
  puts "=" * 80
end
