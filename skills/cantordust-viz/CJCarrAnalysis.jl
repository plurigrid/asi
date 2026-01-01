#!/usr/bin/env julia
# CJCarrAnalysis.jl - Audio Representations for Diffusion
#
# CJ Carr's strategies for linearizing the ineffable into music:
# 1. STFT (Short-Time Fourier Transform) - time × frequency
# 2. Mel Spectrogram - perceptually-weighted bands
# 3. MFCC - cepstral coefficients for timbre
# 4. Chromagram - pitch class distribution
# 5. Phase reconstruction (Griffin-Lim)
#
# Inspired by Zaf-Julia (github.com/zafarrafii/Zaf-Julia)

using Pkg
Pkg.activate(@__DIR__)

using WAV
using FFTW
using Statistics
using Printf
using LinearAlgebra

# =============================================================================
# CORE DSP FUNCTIONS
# =============================================================================

"""
    hamming(N, type=:symmetric)

Compute Hamming window.
"""
function hamming(N::Int; periodic::Bool=false)
    if periodic
        n = 0:N-1
        0.54 .- 0.46 .* cos.(2π .* n ./ N)
    else
        n = 0:N-1
        0.54 .- 0.46 .* cos.(2π .* n ./ (N-1))
    end
end

"""
    stft(signal, window, hop)

Short-Time Fourier Transform - CJ Carr's primary representation.
Returns complex spectrogram (n_fft÷2+1 × n_frames).
"""
function stft(signal::Vector{Float64}, window::Vector{Float64}, hop::Int)
    n_fft = length(window)
    n_samples = length(signal)
    n_frames = (n_samples - n_fft) ÷ hop + 1
    
    # Pad signal
    padded = vcat(signal, zeros(n_fft))
    
    # Allocate output
    spectrogram = zeros(ComplexF64, n_fft ÷ 2 + 1, n_frames)
    
    for frame in 1:n_frames
        start = (frame - 1) * hop + 1
        segment = padded[start:start+n_fft-1] .* window
        spectrum = fft(segment)
        spectrogram[:, frame] = spectrum[1:n_fft÷2+1]
    end
    
    spectrogram
end

"""
    istft(spectrogram, window, hop)

Inverse STFT with overlap-add.
"""
function istft(spectrogram::Matrix{ComplexF64}, window::Vector{Float64}, hop::Int)
    n_fft = length(window)
    n_frames = size(spectrogram, 2)
    n_samples = (n_frames - 1) * hop + n_fft
    
    signal = zeros(n_samples)
    window_sum = zeros(n_samples)
    
    for frame in 1:n_frames
        start = (frame - 1) * hop + 1
        
        # Reconstruct full spectrum (mirror)
        half = spectrogram[:, frame]
        full = vcat(half, conj(reverse(half[2:end-1])))
        
        # IFFT
        segment = real(ifft(full)) .* window
        
        signal[start:start+n_fft-1] .+= segment
        window_sum[start:start+n_fft-1] .+= window.^2
    end
    
    # Normalize by window sum
    valid = window_sum .> 1e-10
    signal[valid] ./= window_sum[valid]
    
    signal
end

"""
    mel_filterbank(sr, n_fft, n_mels; fmin=0, fmax=sr/2)

Compute mel filterbank matrix.
"""
function mel_filterbank(sr::Int, n_fft::Int, n_mels::Int; fmin::Float64=0.0, fmax::Float64=sr/2.0)
    # Mel scale conversion
    hz_to_mel(f) = 2595 * log10(1 + f / 700)
    mel_to_hz(m) = 700 * (10^(m / 2595) - 1)
    
    mel_min = hz_to_mel(fmin)
    mel_max = hz_to_mel(fmax)
    
    # Mel points
    mel_points = range(mel_min, mel_max, length=n_mels + 2)
    hz_points = mel_to_hz.(mel_points)
    
    # FFT bin indices
    bin_points = round.(Int, hz_points .* (n_fft / sr)) .+ 1
    
    # Create filterbank
    n_freqs = n_fft ÷ 2 + 1
    filterbank = zeros(n_mels, n_freqs)
    
    for m in 1:n_mels
        left = bin_points[m]
        center = bin_points[m + 1]
        right = bin_points[m + 2]
        
        # Rising slope
        for k in left:center
            if k >= 1 && k <= n_freqs
                filterbank[m, k] = (k - left) / max(1, center - left)
            end
        end
        
        # Falling slope
        for k in center:right
            if k >= 1 && k <= n_freqs
                filterbank[m, k] = (right - k) / max(1, right - center)
            end
        end
    end
    
    filterbank
end

"""
    mel_spectrogram(signal, sr; n_fft, hop, n_mels)

Compute mel spectrogram - CJ Carr's diffusion representation.
"""
function mel_spectrogram(signal::Vector{Float64}, sr::Int; 
                          n_fft::Int=2048, hop::Int=512, n_mels::Int=128)
    window = hamming(n_fft; periodic=true)
    spec = stft(signal, window, hop)
    mag = abs.(spec)
    
    fb = mel_filterbank(sr, n_fft, n_mels)
    mel_spec = fb * mag
    
    # Log scale (as used in diffusion)
    log_mel = log10.(mel_spec .+ 1e-10)
    
    (mel=mel_spec, log_mel=log_mel, magnitude=mag, filterbank=fb)
end

"""
    chromagram(signal, sr; n_fft, hop, n_chroma)

Compute chromagram - pitch class distribution.
"""
function chromagram(signal::Vector{Float64}, sr::Int;
                    n_fft::Int=4096, hop::Int=512, n_chroma::Int=12)
    window = hamming(n_fft; periodic=true)
    spec = stft(signal, window, hop)
    mag = abs.(spec)
    
    # Frequency bins to pitch classes
    n_freqs = size(mag, 1)
    freqs = (0:n_freqs-1) .* (sr / n_fft)
    
    # Pitch class from frequency
    chroma_filter = zeros(n_chroma, n_freqs)
    for k in 2:n_freqs  # Skip DC
        if freqs[k] > 0
            midi = 12 * log2(freqs[k] / 440) + 69
            pc = mod(round(Int, midi), 12) + 1
            chroma_filter[pc, k] = 1
        end
    end
    
    # Normalize
    for pc in 1:n_chroma
        s = sum(chroma_filter[pc, :])
        if s > 0
            chroma_filter[pc, :] ./= s
        end
    end
    
    chroma = chroma_filter * mag
    chroma
end

"""
    spectral_features(magnitude)

Compute spectral features for CJ Carr-style analysis.
"""
function spectral_features(mag::Matrix{Float64})
    n_freqs, n_frames = size(mag)
    
    centroids = Float64[]
    flatness = Float64[]
    rolloff = Float64[]
    
    for frame in 1:n_frames
        m = mag[:, frame]
        total = sum(m) + 1e-10
        
        # Centroid (brightness)
        centroid = sum((1:n_freqs) .* m) / total
        push!(centroids, centroid)
        
        # Flatness (noise vs tone)
        log_m = log.(m .+ 1e-10)
        geo_mean = exp(mean(log_m))
        arith_mean = mean(m)
        push!(flatness, geo_mean / (arith_mean + 1e-10))
        
        # Rolloff (85% energy point)
        cumulative = cumsum(m)
        threshold = 0.85 * total
        rolloff_idx = findfirst(x -> x >= threshold, cumulative)
        push!(rolloff, isnothing(rolloff_idx) ? n_freqs : rolloff_idx)
    end
    
    (centroid=centroids, flatness=flatness, rolloff=rolloff)
end

"""
    envelope(signal; hop)

Compute amplitude envelope (RMS).
"""
function envelope(signal::Vector{Float64}; hop::Int=512)
    n = length(signal)
    env = Float64[]
    
    for i in 1:hop:n
        chunk = signal[i:min(i+hop-1, n)]
        rms = sqrt(mean(chunk.^2))
        push!(env, rms)
    end
    
    env
end

"""
    zero_crossing_rate(signal; hop)

Compute zero-crossing rate (texture/noisiness).
"""
function zero_crossing_rate(signal::Vector{Float64}; hop::Int=512)
    n = length(signal)
    zcr = Float64[]
    
    for i in 1:hop:n-1
        chunk = signal[i:min(i+hop-1, n)]
        crossings = sum(chunk[1:end-1] .* chunk[2:end] .< 0)
        push!(zcr, crossings / length(chunk))
    end
    
    zcr
end

# =============================================================================
# CJ CARR LINEARIZATION STRATEGIES
# =============================================================================

"""
    LinearizationStrategy

Strategy for converting audio to diffusion-ready representation.
"""
@enum LinearizationStrategy begin
    NOISE_DOMINANT      # Use mel-spectrogram + phase reconstruction
    HARMONIC_BRIGHT     # Use chromagram + STFT magnitude
    TONAL_PURE          # Use pitch tracking + envelope
    COMPLEX_FULL        # Full STFT with phase, for diffusion
end

"""
    determine_strategy(features)

Determine best linearization strategy based on spectral features.
"""
function determine_strategy(features)
    avg_flatness = mean(features.flatness)
    avg_centroid = mean(features.centroid)
    
    if avg_flatness > 0.3
        NOISE_DOMINANT
    elseif avg_centroid > 100
        HARMONIC_BRIGHT
    elseif avg_flatness < 0.05
        TONAL_PURE
    else
        COMPLEX_FULL
    end
end

"""
    diffusion_representation(signal, sr; n_mels)

Prepare audio for CJ Carr-style diffusion model.
Returns image-like representation suitable for U-Net.
"""
function diffusion_representation(signal::Vector{Float64}, sr::Int; n_mels::Int=128)
    result = mel_spectrogram(signal, sr; n_mels=n_mels)
    
    # Normalize to [0, 1] for image-like representation
    log_mel = result.log_mel
    min_val, max_val = extrema(log_mel)
    normalized = (log_mel .- min_val) ./ (max_val - min_val + 1e-10)
    
    (
        image = normalized,           # Ready for diffusion
        log_mel = log_mel,            # For audio reconstruction
        magnitude = result.magnitude, # For Griffin-Lim
        shape = size(normalized),     # (n_mels, n_frames)
        sr = sr
    )
end

# =============================================================================
# FILE ANALYSIS
# =============================================================================

"""
    analyze_wav(path)

Full CJ Carr-style analysis of a WAV file.
"""
function analyze_wav(path::String)
    # Read WAV
    signal, sr = wavread(path)
    
    # Convert to mono
    if ndims(signal) > 1
        signal = vec(mean(signal, dims=2))
    else
        signal = vec(signal)
    end
    
    sr = Int(sr)
    duration = length(signal) / sr
    
    # Compute representations
    n_fft = 2048
    hop = 512
    window = hamming(n_fft; periodic=true)
    
    spec = stft(signal, window, hop)
    mag = abs.(spec)
    
    mel_result = mel_spectrogram(signal, sr; n_fft=n_fft, hop=hop)
    chroma = chromagram(signal, sr)
    features = spectral_features(mag)
    env = envelope(signal; hop=hop)
    zcr = zero_crossing_rate(signal; hop=hop)
    
    strategy = determine_strategy(features)
    diffusion = diffusion_representation(signal, sr)
    
    (
        path = path,
        duration = duration,
        sr = sr,
        n_samples = length(signal),
        
        # Spectral
        stft_shape = size(spec),
        mel_shape = size(mel_result.mel),
        chroma_shape = size(chroma),
        
        # Features
        avg_centroid = mean(features.centroid),
        avg_flatness = mean(features.flatness),
        avg_rolloff = mean(features.rolloff),
        avg_envelope = mean(env),
        max_envelope = maximum(env),
        avg_zcr = mean(zcr),
        
        # Strategy
        strategy = strategy,
        
        # Diffusion ready
        diffusion_shape = diffusion.shape,
        
        # Raw data for further use
        magnitude = mag,
        mel = mel_result.log_mel,
        chroma = chroma,
        envelope = env
    )
end

"""
    print_analysis(result)

Pretty-print CJ Carr analysis results.
"""
function print_analysis(result)
    name = basename(result.path)
    
    println()
    println("=" ^ 60)
    println("📊 $name")
    println("=" ^ 60)
    @printf("  Duration: %.2fs @ %d Hz\n", result.duration, result.sr)
    @printf("  Samples: %d\n", result.n_samples)
    
    println()
    println("  CJ Carr Representations:")
    @printf("  ├─ STFT: %d × %d (freq × time)\n", result.stft_shape...)
    @printf("  ├─ Mel Spectrogram: %d × %d\n", result.mel_shape...)
    @printf("  ├─ Chromagram: %d × %d\n", result.chroma_shape...)
    @printf("  └─ Diffusion Image: %d × %d\n", result.diffusion_shape...)
    
    println()
    println("  Spectral Features:")
    @printf("  ├─ Centroid: %.1f (brightness)\n", result.avg_centroid)
    @printf("  ├─ Flatness: %.4f (tonality)\n", result.avg_flatness)
    @printf("  ├─ Rolloff: %.1f (spectral shape)\n", result.avg_rolloff)
    @printf("  └─ ZCR: %.4f (texture)\n", result.avg_zcr)
    
    println()
    println("  Amplitude:")
    @printf("  ├─ Avg RMS: %.4f\n", result.avg_envelope)
    @printf("  └─ Max RMS: %.4f\n", result.max_envelope)
    
    println()
    strategy_desc = Dict(
        NOISE_DOMINANT => "NOISE-DOMINANT: Mel-spectrogram + phase reconstruction",
        HARMONIC_BRIGHT => "HARMONIC-BRIGHT: Chromagram + STFT magnitude",
        TONAL_PURE => "TONAL-PURE: Pitch tracking + envelope",
        COMPLEX_FULL => "COMPLEX: Full STFT with phase (diffusion)"
    )
    println("  Linearization Strategy:")
    println("  → $(strategy_desc[result.strategy])")
end

# =============================================================================
# DEMO
# =============================================================================

function demo()
    println()
    println("🎛️ CJ Carr Audio Artifact Analysis")
    println("Linearizing the Ineffable into Music")
    println("=" ^ 60)
    
    files = [
        "game_chord.wav",
        "imagination_tower.wav",
        "mentalize_coincidence.wav",
        "parallel_chord.wav",
        "poem_chain.wav",
        "poem_distilled.wav",
        "sonification_techniques.wav",
        "strange_midi_tower.wav"
    ]
    
    results = []
    
    for f in files
        path = joinpath(@__DIR__, f)
        if isfile(path)
            result = analyze_wav(path)
            print_analysis(result)
            push!(results, result)
        else
            println("⚠️  Not found: $f")
        end
    end
    
    # Summary
    println()
    println("=" ^ 60)
    println("📋 SUMMARY: Linearization Strategies")
    println("=" ^ 60)
    println()
    @printf("%-28s %8s %8s %s\n", "File", "Centroid", "Flatness", "Strategy")
    println("-" ^ 60)
    
    for r in results
        name = basename(r.path)
        short_name = length(name) > 26 ? name[1:23] * "..." : name
        strat = string(r.strategy)
        @printf("%-28s %8.1f %8.4f %s\n", short_name, r.avg_centroid, r.avg_flatness, strat)
    end
    
    println()
    println("=" ^ 60)
    println("🔬 CJ Carr Diffusion Pipeline:")
    println("  1. Audio → STFT (2048 FFT, 512 hop)")
    println("  2. STFT → Mel-spectrogram (128 bands)")
    println("  3. Mel → Log-scale normalization")
    println("  4. Log-mel → Image for U-Net diffusion")
    println("  5. Denoise iteratively (50-1000 steps)")
    println("  6. Reconstructed mel → Griffin-Lim → Audio")
    println("=" ^ 60)
    
    results
end

# =============================================================================
# CLI
# =============================================================================

function main(args)
    if isempty(args)
        println("🎛️ CJCarrAnalysis.jl - Audio Representations for Diffusion")
        println()
        println("Usage:")
        println("  julia CJCarrAnalysis.jl demo         Analyze all WAV files")
        println("  julia CJCarrAnalysis.jl <file.wav>   Analyze specific file")
        return
    end
    
    cmd = args[1]
    
    if cmd == "demo"
        demo()
    elseif endswith(cmd, ".wav")
        if isfile(cmd)
            result = analyze_wav(cmd)
            print_analysis(result)
        else
            println("File not found: $cmd")
        end
    else
        demo()
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    main(ARGS)
end
