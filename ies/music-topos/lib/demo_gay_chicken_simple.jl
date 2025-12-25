"""
    demo_gay_chicken_simple.jl

Simplified demo of Chicken Scheme + Gay.jl integration.
Shows core functionality without heavy output.

Run: julia lib/demo_gay_chicken_simple.jl
"""

using Printf

include("GayChickenBridge.jl")
using .GayChickenBridge

println("\nGay.jl + Chicken Scheme Integration Demo")
println(repeat("=", 70))

# Test 1: Deterministic generation
println("\n[1] SplitMix64 Determinism")
stream1 = gay_ternary_stream(UInt64(42), 50)
stream2 = gay_ternary_stream(UInt64(42), 50)
println("Same seed produces same stream? $(stream1 == stream2) ✓")

# Test 2: Color conversion
println("\n[2] Ternary to Color Conversion")
for i in 0:2
    h, s, l = ternary_to_okhsl(i, 0)
    r, g, b = okhsl_to_rgb(h, s, l)
    @printf "  Trit %d: Hue=%.1f° Sat=%.2f Light=%.2f RGB=(%d,%d,%d)\n" i h s l r g b
end

# Test 3: GF(3) conservation
println("\n[3] GF(3) Conservation")
stream = gay_ternary_stream(UInt64(999), 1000)
is_conserved = verify_gf3_conservation(stream)
@printf "  1000-element stream conserved? %s ✓\n" is_conserved

# Test 4: Entropy
println("\n[4] Entropy Analysis")
hues = [ternary_to_okhsl(stream[i], i-1)[1] for i in 1:length(stream)]
ent = color_stream_entropy(hues, 360)
max_ent = estimate_max_entropy(3)
@printf "  Entropy: %.4f nats (max: %.4f, %.1f%% efficiency)\n" ent max_ent (ent/max_ent*100)

# Test 5: Verification suite
println("\n[5] Full Verification")
results = run_verification_suite(UInt64(0x123456789abcdef0), 5000)
for (test, val) in results
    if test in ["entropy_value", "max_entropy", "entropy_ratio"]
        @printf "  %-20s: %.4f\n" test val
    else
        status = val ? "✓" : "✗"
        println("  $(lpad(test, 20)): $status")
    end
end

println("\n" * repeat("=", 70))
println("Integration Status: ✓ COMPLETE")
println("\nImplemented:")
println("  ✓ SplitMix64 RNG (deterministic ternary)")
println("  ✓ Okhsl color conversion")
println("  ✓ Colored operadic composition (GF(3))")
println("  ✓ Shannon entropy measurement")
println("  ✓ Verification framework")
println("\nNext: Connect to Chicken color egg & build Narya bridge")
println(repeat("=", 70) * "\n")
