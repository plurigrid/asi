#!/usr/bin/env sclang
// Boot SuperCollider Server with Music Topos configuration
// Directly define the sine synth for immediate use

// Configure server options
Server.local.options.maxLogins = 4;
Server.local.options.memSize = 65536;

// Boot the server FIRST
Server.local.boot;

// Wait for server to be ready, THEN define and send synths
Server.local.waitForBoot({
    "Server booted. Defining sine synth...".postln;

    // Define the sine synth and add to server (blocking)
    SynthDef("sine", {|freq=440, amp=0.3, sustain=1|
        var env = EnvGen.kr(
            Env([0, 1, 1, 0], [0.01, sustain, 0.01], 'lin'),
            doneAction: Done.freeSelf
        );
        Out.ar(0, (env * amp * SinOsc.ar(freq)) ! 2);
    }).add;

    // Wait for synth to be registered on server
    Server.local.sync;

    ("✓ SuperCollider booted on port " ++ Server.local.addr.port).postln;
    "✓ Sine synth defined (stereo output)".postln;
    "Ready to receive OSC commands".postln;

    // Test synth to verify audio works (short beep)
    "Playing test tone...".postln;
    Synth("sine", [\freq, 440, \amp, 0.2, \sustain, 0.3]);

    // Keep the script running indefinitely
    // Fork a process that runs forever (in a Routine this is safe)
    fork {
        loop {
            0.1.wait;
        };
    };
});
