// BANUKA Phase Scheduler Sonification Synth Definitions
// SuperCollider SynthDef Instruments for Overtone Integration
// 2026-02-03

(
// =============================================================================
// Synth 1: Main Phase Sonification Synth
// Maps computational phases to timbral characteristics
// =============================================================================

SynthDef(\banuka_synth, {
  |freq=440, amp=0.3, attack=0.1, decay=0.2, sustain=0.5, release=0.3,
   dur=1.0, waveform=0, brightness=0.5|

  // Waveform selection: 0=sine, 1=triangle, 2=sawtooth
  var osc = Select.ar(waveform, [
    SinOsc.ar(freq),                                    // Sine wave
    LFTri.ar(freq),                                     // Triangle wave
    LFSaw.ar(freq)                                      // Sawtooth wave
  ]);

  // Add harmonic overtones based on brightness
  var harmonics = Mix.ar([
    osc * (1 - brightness),
    SinOsc.ar(freq * 2) * brightness * 0.3,
    SinOsc.ar(freq * 3) * brightness * 0.15,
    SinOsc.ar(freq * 4) * brightness * 0.075
  ]);

  // ADSR envelope
  var env = EnvGen.kr(
    Env.adsr(attack, decay, sustain, release),
    doneAction: 2
  );

  // Resonant filter for timbral coloration
  var filtered = MoogFF.ar(harmonics, freq * (1 + brightness * 3), brightness);

  // Output with amplitude envelope
  Out.ar(0, (filtered * env * amp * 0.5) ! 2);
}).add;

// =============================================================================
// Synth 2: Phase Transition Synth
// Creates smooth glissando between phases
// =============================================================================

SynthDef(\banuka_transition, {
  |from_freq=220, to_freq=440, dur=0.5, amp=0.3|

  // Frequency glissando using XLine
  var freq = XLine.kr(from_freq, to_freq, dur);

  // Sine wave with smooth frequency transition
  var osc = SinOsc.ar(freq);

  // Envelope for the transition
  var env = EnvGen.kr(
    Env.perc(0.05, dur - 0.05),
    doneAction: 2
  );

  // Add subtle chorus effect
  var modulated = osc + (SinOsc.ar(freq + SinOsc.kr(3) * 5) * 0.1);

  Out.ar(0, (modulated * env * amp * 0.5) ! 2);
}).add;

// =============================================================================
// Synth 3: Resource Utilization Indicator
// Density of grain cloud represents resource usage
// =============================================================================

SynthDef(\banuka_resource_cloud, {
  |freq=400, density=10, dur=2.0, amp=0.2|

  // Granular synthesis with density modulation
  var grain_freq = Rand(freq * 0.9, freq * 1.1);
  var grain_dur = 0.05;
  var grain_density = density * 10; // 10 to 100 grains per second

  var trigger = Dust.kr(grain_density);

  var grain = TGrains.ar(
    numChannels: 2,
    trigger: trigger,
    bufnum: 0, // Placeholder: requires buffer
    rate: 1.0,
    centerPos: TRand.kr(0.0, 1.0, trigger),
    dur: grain_dur,
    pan: WhiteNoise.kr(0.5),
    amp: 0.1
  );

  // Modulation based on phase frequency
  var modulated = grain * SinOsc.kr(0.5 + (density * 0.05));

  // Envelope
  var env = EnvGen.kr(
    Env.linen(0.1, dur - 0.2, 0.1),
    doneAction: 2
  );

  Out.ar(0, (modulated * env * amp) ! 2);
}).add;

// =============================================================================
// Synth 4: Phase Completion Signal
// Rising pitch indicates completion; falling indicates failure
// =============================================================================

SynthDef(\banuka_completion, {
  |freq_start=440, freq_end=880, duration=0.3, completion_type=0, amp=0.3|

  // completion_type: 0=success (rising), 1=failure (falling)
  var freq_curve = Select.kr(completion_type, [
    XLine.kr(freq_start, freq_end, duration),        // Rising for success
    XLine.kr(freq_end, freq_start, duration)          // Falling for failure
  ]);

  var osc = SinOsc.ar(freq_curve);

  // Sharp attack, smooth release
  var env = EnvGen.kr(
    Env.perc(0.02, duration - 0.02, curve: -4),
    doneAction: 2
  );

  // Add brief chime effect with harmonics
  var harmonics = Mix.ar([
    osc * 0.7,
    SinOsc.ar(freq_curve * 1.5) * 0.2,
    SinOsc.ar(freq_curve * 2) * 0.1
  ]);

  Out.ar(0, (harmonics * env * amp * 0.5) ! 2);
}).add;

// =============================================================================
// Synth 5: Background Ambient Phase Field
// Continuous sonification of overall scheduler state
// =============================================================================

SynthDef(\banuka_ambient, {
  |freq=110, phase_energy=0.5, dur=30.0, amp=0.2|

  // Complex harmonic pad
  var base = SinOsc.ar(freq);
  var harmonic_1 = SinOsc.ar(freq * 1.5) * 0.3;
  var harmonic_2 = SinOsc.ar(freq * 2) * 0.2;
  var harmonic_3 = SinOsc.ar(freq * 3) * 0.1;

  var harmonics = Mix.ar([base, harmonic_1, harmonic_2, harmonic_3]);

  // Slow modulation based on phase energy
  var mod = SinOsc.kr(0.5 + (phase_energy * 0.5)) * 0.3 + 0.7;

  // Filtered for smooth ambient texture
  var filtered = MoogFF.ar(harmonics * mod, freq * 2, 0.3);

  // Very smooth envelope
  var env = EnvGen.kr(
    Env.linen(0.5, dur - 1.0, 0.5),
    doneAction: 2
  );

  Out.ar(0, (filtered * env * amp * 0.3) ! 2);
}).add;

// =============================================================================
// Synth 6: Error/Alert Signal
// Dissonant sound for scheduler errors or anomalies
// =============================================================================

SynthDef(\banuka_alert, {
  |freq=880, duration=0.2, alert_type=0, amp=0.3|

  // alert_type: 0=warning, 1=critical, 2=blocked
  var num_partials = Select.ir(alert_type, [3, 5, 2]);

  var partials = Array.fill(num_partials, {|i|
    var partial_freq = freq * (i + 1) * (1 + (i * 0.15));
    var partial_width = 0.05 + (i * 0.02);
    var partial_amp = 1.0 / (i + 1);
    Pulse.ar(partial_freq, partial_width) * partial_amp
  });

  var osc = Mix.ar(partials);

  // Fast attack, quick decay
  var env = EnvGen.kr(
    Env.perc(0.01, duration - 0.01, curve: -6),
    doneAction: 2
  );

  Out.ar(0, (osc * env * amp * 0.5) ! 2);
}).add;

"BANUKA Synth Definitions Loaded".postln;
)
