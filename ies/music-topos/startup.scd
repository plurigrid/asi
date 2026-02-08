// Music Topos: SuperCollider Server Configuration
// Place this file in: Platform.userConfigDir +/+ "startup.scd"
// For macOS: ~/.local/share/SuperCollider/startup.scd

// Enable multi-client support
Server.local.options.maxLogins = 4;

// Define the sine synth for Music Topos
SynthDef("sine", {|freq=440, amp=0.3, sustain=1|
    var env = EnvGen.kr(
        Env([0, 1, 1, 0], [0.01, sustain, 0.01], 'lin'),
        doneAction: Done.freeSelf
    );
    Out.ar(0, env * amp * SinOsc.ar(freq));
}).send(Server.local);

(
    "═════════════════════════════════════".postln;
    "🎵 Music Topos Configuration Loaded".postln;
    "═════════════════════════════════════".postln;
    "• Multi-client support enabled (maxLogins=4)".postln;
    "• Sine synth defined and ready".postln;
    "".postln;
).value;
