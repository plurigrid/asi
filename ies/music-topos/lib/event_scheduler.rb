# lib/event_scheduler.rb
require 'socket'

class EventScheduler
  DEFAULT_SC_PORT = 57110
  DEFAULT_SC_HOST = '127.0.0.1'

  attr_reader :tempo, :play_event

  def initialize(tempo:, play_event: nil, sc_host: DEFAULT_SC_HOST, sc_port: DEFAULT_SC_PORT)
    @tempo = tempo.to_f
    @play_event = play_event || method(:default_play_event)
    @sc_host = sc_host
    @sc_port = sc_port
    @socket = UDPSocket.new
  end

  def run(score_events)
    return if score_events.nil? || score_events.empty?

    sorted = score_events.sort_by { |e| e[:at] || 0 }
    start_time = monotonic_now

    sorted.each do |event|
      target_beats = event[:at] || 0
      target_seconds = beats_to_seconds(target_beats)
      target_time = start_time + target_seconds

      sleep_until(target_time)
      play_event.call(event)
    end
  end

  def send_osc(path, *args)
    message = encode_osc_message(path, args)
    @socket.send(message, 0, @sc_host, @sc_port)
  end

  def score_event_to_s_new(event)
    audio = event[:audio] || {}
    synth_name = audio[:synth] || 'default'
    node_id = audio[:node_id] || -1
    add_action = audio[:add_action] || 0
    target = audio[:target] || 1

    args = [synth_name, node_id, add_action, target]

    (audio[:params] || {}).each do |key, value|
      args << key.to_s
      args << value
    end

    ['/s_new', *args]
  end

  def play_via_osc(event)
    osc_msg = score_event_to_s_new(event)
    send_osc(*osc_msg)
  end

  def close
    @socket.close if @socket && !@socket.closed?
  end

  private

  def monotonic_now
    Process.clock_gettime(Process::CLOCK_MONOTONIC)
  end

  def beats_to_seconds(beats)
    beats * 60.0 / @tempo
  end

  def sleep_until(target_time)
    loop do
      remaining = target_time - monotonic_now
      break if remaining <= 0
      sleep([remaining, 0.001].min)
    end
  end

  def default_play_event(event)
    puts "[#{monotonic_now}] Playing: #{event.inspect}"
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
    when Integer
      [arg].pack('N')
    when Float
      [arg].pack('g')
    when String
      osc_string(arg)
    else
      osc_string(arg.to_s)
    end
  end
end
