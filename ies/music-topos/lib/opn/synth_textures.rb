# lib/opn/synth_textures.rb
# OPN Component 10: Synthesizer Textures
# Inspired by: Zones Without People, Russian Mind

module OPN
  module SynthTextures
    # PWM pad simulation
    def self.pwm_pad(root: 48, duration: 8.0)
      events = []
      
      # Multiple detuned layers
      detunes = [-0.1, -0.05, 0, 0.05, 0.1]
      
      detunes.each do |d|
        events << {
          at: rand * 0.1,
          pitch: root + d,
          dur: duration,
          amp: 0.15
        }
        
        # Fifth
        events << {
          at: rand * 0.1,
          pitch: root + 7 + d,
          dur: duration,
          amp: 0.12
        }
      end
      
      events
    end
    
    # FM bell
    def self.fm_bell(pitch, duration: 2.0)
      events = []
      
      # Carrier
      events << { at: 0, pitch: pitch, dur: duration, amp: 0.4 }
      
      # Modulator harmonics (inharmonic for bell)
      [1.4, 2.76, 5.4].each do |ratio|
        harm_pitch = pitch + (12 * Math.log2(ratio)).round
        events << {
          at: 0,
          pitch: harm_pitch.clamp(24, 96),
          dur: duration * 0.7,
          amp: 0.15 / ratio
        }
      end
      
      events
    end
    
    # Supersaw
    def self.supersaw(pitches, duration: 4.0)
      events = []
      
      pitches.each do |pitch|
        7.times do |i|
          detune = (i - 3) * 0.08
          events << {
            at: 0,
            pitch: pitch + detune,
            dur: duration,
            amp: 0.08
          }
        end
      end
      
      events
    end
    
    # Analog drift
    def self.analog_drift(events, max_drift: 0.3)
      drift = 0
      
      events.map do |e|
        drift += (rand - 0.5) * 0.1
        drift = drift.clamp(-max_drift, max_drift)
        e.merge(pitch: e[:pitch] + drift)
      end
    end
    
    # Noise sweep (simulated with pitch extremes)
    def self.noise_sweep(direction: :up, duration: 4.0)
      events = []
      steps = (duration / 0.02).to_i
      
      steps.times do |i|
        progress = i.to_f / steps
        progress = 1 - progress if direction == :down
        
        pitch = 24 + progress * 72
        
        events << {
          at: i * 0.02,
          pitch: pitch.round,
          dur: 0.03,
          amp: 0.1 + rand * 0.1
        }
      end
      
      events
    end
  end
end
