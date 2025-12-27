#!/usr/bin/env ruby
# bin/pattern_runs_on_matter.rb
#
# Unified curriculum runner using Free Monad / Cofree Comonad architecture
#
# Based on Libkind & Spivak's "Pattern Runs on Matter" (ACT 2024):
# - Pattern (Free monad) = the musical score as a decision tree
# - Matter (Cofree comonad) = the performer/synthesizer environment
# - Module action = Pattern runs on Matter
#
# Usage:
#   ruby bin/pattern_runs_on_matter.rb --mode realtime --tempo 90
#   ruby bin/pattern_runs_on_matter.rb --mode batch --output /tmp/curriculum.wav

require 'optparse'
require 'socket'

$LOAD_PATH.unshift(File.expand_path('../lib', __dir__))

require 'free_monad'
require 'cofree_comonad'
require 'runs_on'
require 'score_event'
require 'audio_synthesis'
require 'quantum_industrial_patterns'
require 'quantum_aphex_autechre'
require 'maximum_dynamism'
require 'jungle_involution'
require 'gay_neverending'
require 'opn/transcendental'

# ============================================================================
# COMMAND LINE PARSING
# ============================================================================

options = {
  mode: 'realtime',
  tempo: 90,
  output: '/tmp/curriculum.wav',
  world: 'initial',
  verbose: false,
  style: 'dark'  # dark, virtuoso, quantum
}

OptionParser.new do |opts|
  opts.banner = "Usage: #{$0} [options]"
  
  opts.on('-m', '--mode MODE', %w[realtime batch], 
          'Mode: realtime (OSC) or batch (WAV)') do |m|
    options[:mode] = m
  end
  
  opts.on('-t', '--tempo BPM', Integer, 'Tempo in BPM (default: 90)') do |t|
    options[:tempo] = t
  end
  
  opts.on('-o', '--output FILE', 'Output WAV file (batch mode)') do |o|
    options[:output] = o
  end
  
  opts.on('-w', '--world WORLD', %w[initial terminal full virtuoso aphex autechre quantum-electronic max-dynamism max-aphex max-autechre jungle jungle-quick neverending gay-drone gay-ambient gay-idm gay-jungle gay-industrial opn-transcendental opn-garden opn-rplus7 opn-ageof],
          'World: ..., opn-transcendental, opn-garden, opn-rplus7, opn-ageof') do |w|
    options[:world] = w
  end
  
  opts.on('-s', '--style STYLE', %w[dark virtuoso quantum],
          'Style: dark (Mica Levi/Xenakis), virtuoso (Avery/James/MachineGirl), quantum (Coecke)') do |s|
    options[:style] = s
  end
  
  opts.on('-v', '--verbose', 'Verbose output') do
    options[:verbose] = true
  end
  
  opts.on('-h', '--help', 'Show this help') do
    puts opts
    exit
  end
end.parse!

# ============================================================================
# PATTERN BUILDERS (Free Monad)
# ============================================================================

class PatternBuilder
  extend FreeMonad::DSL
  
  # ============================================================================
  # DARK / INDUSTRIAL PATTERNS
  # Inspired by: Mica Levi, Xenakis, Monolake
  # ============================================================================
  
  # Dissonant intervals (semitones)
  MINOR_2ND = 1
  MAJOR_7TH = 11
  TRITONE = 6
  MINOR_9TH = 13
  
  # Build Initial World pattern - DARK VERSION
  def self.initial_world
    sequence!(
      # Section 1: The Void - low drone with beating frequencies
      section_marker("THE VOID"),
      the_void,
      rest!(0.3),
      
      # Section 2: Emergence - clusters rising from darkness
      section_marker("EMERGENCE"),
      emergence,
      rest!(0.2),
      
      # Section 3: Dissonant Functions - T→S→D corrupted
      section_marker("CORRUPTED FUNCTIONS"),
      corrupted_harmonic_functions,
      rest!(0.3),
      
      # Section 4: Spiral - tritone cycle descending
      section_marker("SPIRAL"),
      tritone_spiral
    )
  end
  
  # Build Terminal World pattern - INDUSTRIAL
  def self.terminal_world
    sequence!(
      section_marker("MACHINE I"),
      machine_pulse,
      rest!(0.2),
      
      section_marker("STOCHASTIC CLOUD"),
      stochastic_cloud,
      rest!(0.3),
      
      section_marker("MACHINE II"),
      machine_grind,
      rest!(0.2),
      
      section_marker("COLLAPSE"),
      collapse
    )
  end
  
  # Build full curriculum - XENAKIS MODE
  def self.full_curriculum
    sequence!(
      section_marker("=== PART I: DESCENT ==="),
      initial_world,
      rest!(0.5),
      
      section_marker("=== PART II: INDUSTRY ==="),
      terminal_world,
      rest!(0.5),
      
      section_marker("=== PART III: OBLITERATION ==="),
      obliteration
    )
  end
  
  private
  
  def self.section_marker(name)
    FreeMonad::Pure.new(name)
  end
  
  # ============================================================================
  # DARK PATTERNS
  # ============================================================================
  
  # Low drone with close frequencies that beat against each other
  def self.the_void
    sequence!(
      # Sub-bass drone with beating (Monolake-style)
      parallel!(
        play_note!(24, 4.0, 0.4),      # C0 - fundamental
        play_note!(25, 4.0, 0.25),     # C#0 - minor 2nd creates beating
        play_note!(36, 4.0, 0.15)      # C1 - octave reinforcement
      ),
      # Distant high pitch - Mica Levi style
      rest!(0.5),
      play_note!(96, 2.0, 0.08),       # C7 - piercing high
      play_note!(97, 1.5, 0.06),       # C#7 - dissonant
      rest!(0.3)
    )
  end
  
  # Clusters emerging from low register
  def self.emergence
    sequence!(
      # Chromatic cluster in bass
      play_chord!([36, 37, 38, 39], 1.2, 0.3),
      rest!(0.15),
      # Wider cluster
      play_chord!([40, 41, 46, 47], 1.0, 0.25),
      rest!(0.1),
      # Spreading outward
      play_chord!([35, 42, 48, 53], 1.5, 0.3),
      rest!(0.2),
      # Xenakis-style pointillistic bursts
      *stochastic_points(8, 0.08, 0.15)
    )
  end
  
  # Harmonic functions but wrong - tritone substitutions, minor 9ths
  def self.corrupted_harmonic_functions
    sequence!(
      # "Tonic" - but with added minor 9th
      play_chord!([36, 40, 43, 49], 1.2, 0.3),
      rest!(0.1),
      # "Subdominant" - tritone away  
      play_chord!([42, 46, 49, 55], 1.2, 0.28),
      rest!(0.1),
      # "Dominant" - cluster
      play_chord!([43, 44, 49, 50, 55], 1.5, 0.32),
      rest!(0.15),
      # "Resolution" - but it's not
      play_chord!([35, 36, 42, 48], 2.0, 0.35)
    )
  end
  
  # Descending tritone spiral
  def self.tritone_spiral
    notes = []
    pitch = 72  # Start high
    8.times do |i|
      duration = 0.3 + (i * 0.1)  # Getting longer
      notes << play_note!(pitch, duration, 0.2 + (i * 0.02))
      notes << rest!(0.05)
      pitch -= TRITONE  # Descend by tritone
      pitch += 12 if pitch < 30  # Wrap around
    end
    # Final low cluster
    notes << play_chord!([24, 30, 36, 42], 3.0, 0.4)
    sequence!(*notes)
  end
  
  # ============================================================================
  # INDUSTRIAL PATTERNS
  # ============================================================================
  
  # Mechanical pulse (Monolake)
  def self.machine_pulse
    pulses = []
    16.times do |i|
      # Irregular accents
      amp = (i % 4 == 0) ? 0.4 : ((i % 2 == 0) ? 0.2 : 0.1)
      pitch = (i % 3 == 0) ? 36 : 48
      pulses << play_note!(pitch, 0.1, amp)
      pulses << rest!((i % 5 == 0) ? 0.15 : 0.1)
    end
    sequence!(*pulses)
  end
  
  # Xenakis-style stochastic cloud
  def self.stochastic_cloud
    srand(42)  # Deterministic randomness
    events = []
    20.times do
      pitch = rand(40..90)
      duration = rand(0.05..0.3)
      amplitude = rand(0.05..0.25)
      rest_time = rand(0.02..0.15)
      events << play_note!(pitch, duration, amplitude)
      events << rest!(rest_time)
    end
    sequence!(*events)
  end
  
  # Industrial grind
  def self.machine_grind
    sequence!(
      # Low grinding clusters
      parallel!(
        play_chord!([30, 31, 36, 37], 0.8, 0.35),
        sequence!(
          rest!(0.4),
          play_chord!([42, 43, 48, 49], 0.4, 0.2)
        )
      ),
      rest!(0.1),
      # Rhythmic hits
      play_chord!([24, 36], 0.15, 0.5),
      rest!(0.2),
      play_chord!([24, 36], 0.15, 0.5),
      rest!(0.1),
      play_chord!([25, 37], 0.15, 0.45),
      rest!(0.3),
      # Scraping texture
      *stochastic_points(6, 0.05, 0.12),
      play_chord!([24, 30, 36], 1.5, 0.4)
    )
  end
  
  # Final collapse
  def self.collapse
    sequence!(
      # Everything at once, then silence
      parallel!(
        play_chord!([24, 25, 30, 31, 36, 37], 0.5, 0.5),
        play_chord!([48, 49, 54, 55, 60, 61], 0.5, 0.3),
        play_chord!([72, 73, 78, 79, 84, 85], 0.5, 0.15)
      ),
      rest!(0.8),
      # Echoes
      play_note!(36, 0.3, 0.15),
      rest!(0.4),
      play_note!(37, 0.2, 0.08),
      rest!(0.6),
      play_note!(24, 0.15, 0.05),
      rest!(1.0),
      # Final sub-bass
      play_note!(24, 4.0, 0.3)
    )
  end
  
  # Complete destruction
  def self.obliteration
    sequence!(
      # Dense cluster attack
      parallel!(
        sequence!(*stochastic_points(15, 0.04, 0.3)),
        sequence!(
          rest!(0.2),
          *stochastic_points(12, 0.06, 0.25)
        ),
        sequence!(
          rest!(0.4),
          *stochastic_points(10, 0.08, 0.2)
        )
      ),
      rest!(0.3),
      # Slow descent into nothing
      play_chord!([24, 25, 26], 2.0, 0.4),
      rest!(0.2),
      play_chord!([24, 25], 2.5, 0.3),
      rest!(0.3),
      play_note!(24, 4.0, 0.25),
      rest!(1.0),
      # Silence
      rest!(2.0)
    )
  end
  
  # Helper: generate stochastic point events
  def self.stochastic_points(count, max_duration, max_amplitude)
    srand(count * 7)  # Deterministic seed
    events = []
    count.times do
      pitch = rand(36..96)
      duration = rand(0.02..max_duration)
      amplitude = rand(0.02..max_amplitude)
      events << play_note!(pitch, duration, amplitude)
      events << rest!(rand(0.01..0.08))
    end
    events
  end
end

# ============================================================================
# MATTER (Cofree Comonad Environment)
# ============================================================================

def create_matter(options, play_fn: nil)
  CofreeComonad::MusicalMatter.new(
    tempo: options[:tempo],
    timbre: :sine,
    volume: 0.5,
    play_fn: play_fn || ->(pitches, dur, amp) {
      if options[:verbose]
        pitches = [pitches] unless pitches.is_a?(Array)
        notes = pitches.map { |p| midi_to_note_name(p) }.join(',')
        puts "  ♪ #{notes} (#{dur} beats, amp=#{amp.round(2)})"
      end
    }
  )
end

def midi_to_note_name(midi)
  notes = %w[C C# D D# E F F# G G# A A# B]
  octave = (midi / 12) - 1
  "#{notes[midi % 12]}#{octave}"
end

# ============================================================================
# OSC SENDER (for realtime mode)
# ============================================================================

class OscSender
  def initialize(host: '127.0.0.1', port: 57110)
    @socket = UDPSocket.new
    @host = host
    @port = port
    @node_id = 1000
  end
  
  def play_event(event)
    return unless event[:audio]
    
    freqs = event[:audio][:frequencies]
    amp = event[:audio][:amplitude] || 0.3
    dur = event[:dur] || 1.0
    
    freqs.each do |freq|
      @node_id += 1
      send_s_new('sine', @node_id, freq, amp / freqs.length, dur)
    end
  end
  
  def send_s_new(synth, node_id, freq, amp, dur)
    # Build OSC message for /s_new
    path = '/s_new'
    args = [synth, node_id, 1, 0, 'freq', freq, 'amp', amp, 'sustain', dur]
    message = build_osc_message(path, *args)
    @socket.send(message, 0, @host, @port)
  end
  
  private
  
  def build_osc_message(path, *args)
    # Simple OSC message builder
    message = osc_string(path)
    
    # Type tag
    type_tag = ','
    args.each do |arg|
      case arg
      when String then type_tag += 's'
      when Integer then type_tag += 'i'
      when Float then type_tag += 'f'
      end
    end
    message += osc_string(type_tag)
    
    # Arguments
    args.each do |arg|
      case arg
      when String then message += osc_string(arg)
      when Integer then message += [arg].pack('N')
      when Float then message += [arg].pack('g')
      end
    end
    
    message
  end
  
  def osc_string(s)
    s += "\0"
    s += "\0" * (4 - (s.length % 4)) unless (s.length % 4).zero?
    s
  end
end

# ============================================================================
# MAIN
# ============================================================================

puts "🎵 Pattern Runs On Matter"
puts "   Based on Libkind & Spivak (ACT 2024)"
puts "=" * 50

# Select pattern based on world and style
pattern = case options[:world]
          when 'initial' then PatternBuilder.initial_world
          when 'terminal' then PatternBuilder.terminal_world
          when 'full' then PatternBuilder.full_curriculum
          when 'virtuoso' then QuantumIndustrialPatterns::Intermixer.virtuoso_showcase
          when 'aphex' then QuantumAphexAutechre::Showcase.aphex_showcase
          when 'autechre' then QuantumAphexAutechre::Showcase.autechre_showcase
          when 'quantum-electronic' then QuantumAphexAutechre::Showcase.quantum_electronic_showcase
          when 'max-dynamism' then MaximumDynamism::Showcase.maximum_dynamism_demo
          when 'max-aphex', 'max-autechre' then nil  # Handled specially below
          when 'jungle' then JungleInvolution::Showcase.jungle_involution_showcase
          when 'jungle-quick' then JungleInvolution::Showcase.quick_jungle(duration: 8.0)
          when 'neverending' then GayNeverending::Showcase.neverending_showcase(seed: 42)
          when 'gay-drone' then GayNeverending::Showcase.single_style(duration: 64.0, seed: 42, style: :drone)
          when 'gay-ambient' then GayNeverending::Showcase.single_style(duration: 48.0, seed: 42, style: :ambient)
          when 'gay-idm' then GayNeverending::Showcase.single_style(duration: 32.0, seed: 42, style: :idm)
          when 'gay-jungle' then GayNeverending::Showcase.single_style(duration: 24.0, seed: 42, style: :jungle)
          when 'gay-industrial' then GayNeverending::Showcase.single_style(duration: 32.0, seed: 42, style: :industrial)
          when 'opn-transcendental', 'opn-garden', 'opn-rplus7', 'opn-ageof' then nil  # Handled specially
          end

puts "World: #{options[:world]}"
puts "Tempo: #{options[:tempo]} BPM"
puts "Mode: #{options[:mode]}"
puts

# Special handling for OPN modes
if options[:world]&.start_with?('opn-')
  puts "▶ Generating OPN TRANSCENDENTAL patterns..."
  
  events = case options[:world]
  when 'opn-transcendental'
    OPN::Transcendental.transcendental_piece(seed: 42, duration: 90.0)
  when 'opn-garden'
    OPN::Transcendental.garden_of_delete(duration: 60.0)
  when 'opn-rplus7'
    OPN::Transcendental.r_plus_seven(duration: 90.0)
  when 'opn-ageof'
    OPN::Transcendental.age_of(duration: 60.0)
  end
  
  # Convert to score format
  score_events = events.map do |e|
    pitches = e[:pitches] || [e[:pitch]]
    {
      id: "opn-#{e[:at].round(3)}",
      at: e[:at],
      dur: e[:dur] || 0.5,
      world_object: { world: :pitch_space, type: :note, value: pitches },
      audio: {
        frequencies: pitches.map { |p| 440.0 * (2.0 ** ((p - 69) / 12.0)) },
        amplitude: e[:amp] || 0.3,
        synth: 'sine'
      }
    }
  end
  
  puts "  Generated #{score_events.length} events"
  
  if options[:mode] == 'batch'
    puts "▶ Rendering to #{options[:output]}..."
    synth = AudioSynthesis.new(output_file: options[:output])
    synth.render_score(score_events, tempo: options[:tempo])
    puts "✓ Rendered to #{options[:output]}"
    system("afplay #{options[:output]}")
  end
  exit
end

# Special handling for maximum dynamism modes
if options[:world] == 'max-aphex' || options[:world] == 'max-autechre'
  puts "▶ Generating with MAXIMUM DYNAMISM (every DOF derangeable)..."
  
  result = if options[:world] == 'max-aphex'
    MaximumDynamism::PatternDerangers.maximum_aphex(duration: 8.0)
  else
    MaximumDynamism::PatternDerangers.maximum_autechre(duration: 8.0)
  end
  
  events = result[:events]
  stats = result[:stats]
  
  puts "  Generated #{events.length} deranged events"
  puts "  Stats: #{stats[:pitch_changes]} pitch changes, #{stats[:duration_changes]} duration changes"
  puts
  
  if options[:mode] == 'batch'
    puts "▶ Rendering to #{options[:output]}..."
    synth = AudioSynthesis.new(output_file: options[:output])
    synth.render_score(events, tempo: options[:tempo])
    puts "✓ Rendered to #{options[:output]}"
    system("afplay #{options[:output]}")
  else
    puts "▶ Playing in realtime..."
    start_time = Process.clock_gettime(Process::CLOCK_MONOTONIC)
    events.each do |event|
      next unless event[:audio]
      target = event[:at] * 60.0 / options[:tempo]
      now = Process.clock_gettime(Process::CLOCK_MONOTONIC) - start_time
      sleep(target - now) if target > now
      freqs = event[:audio][:frequencies].map { |f| f.round(1) }
      puts "  #{event[:at].round(2)}s: #{freqs} Hz"
    end
  end
  exit
end

case options[:mode]
when 'realtime'
  puts "▶ Running pattern on matter (realtime via OSC)..."
  
  osc = OscSender.new
  matter = create_matter(options)
  
  # Run with real timing
  events = RunsOn.run_realtime(pattern, matter) do |event|
    osc.play_event(event)
  end
  
  puts "\n✓ Playback complete (#{events.length} events)"
  
when 'batch'
  puts "▶ Compiling pattern to score events..."
  
  matter = create_matter(options)
  events = RunsOn.to_score_events(pattern, matter)
  
  puts "  Generated #{events.length} events"
  
  puts "▶ Rendering to #{options[:output]}..."
  
  synth = AudioSynthesis.new(output_file: options[:output])
  synth.render_score(events, tempo: options[:tempo])
  
  puts "✓ Rendered to #{options[:output]}"
  
  # Play the result
  puts "▶ Playing..."
  system("afplay #{options[:output]}")
end
