#!/usr/bin/env ruby
# Unified curriculum runner for music-topos
# Plays curriculum in realtime (OSC→SuperCollider) or batch (→WAV)

require 'optparse'

$LOAD_PATH.unshift File.expand_path('../lib', __dir__)

require 'curriculum'
require 'score_event'
require 'event_scheduler'
require 'audio_synthesis'

module MusicTopos
  class CurriculumRunner
    DEFAULT_TEMPO = 90
    DEFAULT_WAV_PATH = '/tmp/curriculum.wav'

    def initialize(mode:, tempo:, world:)
      @mode = mode
      @tempo = tempo
      @world = world
    end

    def run
      events = compile_events
      puts "🎵 Curriculum: #{@world} world (#{events.size} events, tempo=#{@tempo})"
      puts "   Mode: #{@mode}"
      puts

      case @mode
      when :realtime
        play_realtime(events)
      when :batch
        render_batch(events)
      end
    end

    private

    def compile_events
      case @world
      when :initial
        Curriculum.compile_initial_world
      when :terminal
        Curriculum.compile_terminal_world
      when :full
        Curriculum.compile_full_curriculum
      else
        raise ArgumentError, "Unknown world: #{@world}"
      end
    end

    def play_realtime(events)
      scheduler = EventScheduler.new(
        tempo: @tempo,
        play_event: method(:play_event_osc)
      )

      event_hashes = events.map { |e| score_event_to_hash(e) }
      
      puts "▶ Playing via OSC to SuperCollider (port 57110)..."
      puts

      scheduler.run(event_hashes)
      scheduler.close

      puts
      puts "✓ Playback complete"
    end

    def play_event_osc(event)
      section = event.dig(:meta, :section) || :unknown
      freqs = event.dig(:audio, :frequencies) || []
      freq_str = freqs.map { |f| f.round(1) }.join(', ')
      
      puts "  [#{section}] #{event[:id]} → #{freq_str} Hz"

      send_osc_note(event)
    end

    def send_osc_note(event)
      @socket ||= UDPSocket.new
      audio = event[:audio] || {}
      freqs = audio[:frequencies] || [440]
      amp = audio[:amplitude] || 0.3
      dur = event[:dur_seconds] || 0.5

      freqs.each do |freq|
        message = encode_s_new('sine', -1, 0, 1, {
          'freq' => freq.to_f,
          'amp' => amp.to_f / freqs.size,
          'dur' => dur.to_f
        })
        @socket.send(message, 0, '127.0.0.1', 57110)
      end
    end

    def encode_s_new(synth_name, node_id, add_action, target, params)
      args = [synth_name, node_id, add_action, target]
      params.each { |k, v| args << k << v }
      encode_osc_message('/s_new', args)
    end

    def encode_osc_message(path, args)
      path_padded = osc_string(path)
      type_tag = ',' + args.map { |a| osc_type_tag(a) }.join
      type_tag_padded = osc_string(type_tag)
      data = args.map { |a| encode_osc_arg(a) }.join
      path_padded + type_tag_padded + data
    end

    def osc_string(str)
      padded_length = ((str.bytesize + 1) / 4.0).ceil * 4
      str + "\0" * (padded_length - str.bytesize)
    end

    def osc_type_tag(arg)
      case arg
      when Integer then 'i'
      when Float then 'f'
      when String then 's'
      else 's'
      end
    end

    def encode_osc_arg(arg)
      case arg
      when Integer then [arg].pack('N')
      when Float then [arg].pack('g')
      when String then osc_string(arg)
      else osc_string(arg.to_s)
      end
    end

    def render_batch(events)
      synth = AudioSynthesis.new(output_file: DEFAULT_WAV_PATH)
      event_hashes = events.map { |e| score_event_to_hash(e) }

      puts "▶ Rendering to #{DEFAULT_WAV_PATH}..."
      
      sections = event_hashes.group_by { |e| e.dig(:meta, :section) }
      sections.each do |section, section_events|
        puts "  [#{section}] #{section_events.size} events"
      end

      output = synth.render_score(event_hashes, tempo: @tempo)

      puts
      puts "✓ Rendered to: #{output}"
      
      duration_beats = events.map { |e| e.at + e.dur }.max
      duration_secs = (60.0 / @tempo) * duration_beats
      puts "  Duration: #{duration_secs.round(1)}s"
    end

    def score_event_to_hash(event)
      {
        id: event.id,
        at: event.at,
        dur: event.dur,
        dur_seconds: event.dur_seconds(@tempo),
        audio: {
          frequencies: event.audio&.frequencies || [],
          amplitude: event.audio&.amplitude || 0.3,
          synth: event.audio&.synth || :default
        },
        meta: event.meta || {}
      }
    end
  end
end

if __FILE__ == $0
  options = {
    mode: :realtime,
    tempo: MusicTopos::CurriculumRunner::DEFAULT_TEMPO,
    world: :initial
  }

  OptionParser.new do |opts|
    opts.banner = "Usage: #{$0} [options]"

    opts.on('--mode MODE', [:realtime, :batch], 'Mode: realtime or batch') do |m|
      options[:mode] = m
    end

    opts.on('--tempo TEMPO', Integer, "Tempo in BPM (default: #{options[:tempo]})") do |t|
      options[:tempo] = t
    end

    opts.on('--world WORLD', [:initial, :terminal, :full], 'World: initial, terminal, or full') do |w|
      options[:world] = w
    end

    opts.on('-h', '--help', 'Show this help') do
      puts opts
      exit
    end
  end.parse!

  runner = MusicTopos::CurriculumRunner.new(**options)
  runner.run
end
