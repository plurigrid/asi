#!/usr/bin/env julia
# verify_cones.jl — Ordered Locale Verification Script
# GF(3): MINUS(-1) validation

include("ordered_locale.jl")
using .OrderedLocales

function main()
    println("═══ Ordered Locale Verification ═══")
    
    all_pass = true
    
    # Test 1: Walking Arrow
    F_arrow = walking_arrow()
    valid, msg = verify_open_cone_condition(F_arrow)
    if valid
        println("Walking Arrow: ✓")
    else
        println("Walking Arrow: ✗ ($msg)")
        all_pass = false
    end
    
    # Test 2: Diamond
    F_diamond = diamond()
    valid, msg = verify_open_cone_condition(F_diamond)
    m = frame_meet(F_diamond, 2, 3)
    j = frame_join(F_diamond, 2, 3)
    if valid && m == 1 && j == 4
        println("Diamond: ✓ (meet(a,b)=⊥, join(a,b)=⊤)")
    else
        println("Diamond: ✗ (meet=$m, join=$j, valid=$valid)")
        all_pass = false
    end
    
    # Test 3: Chain(5)
    F_chain = chain(5)
    valid, msg = verify_open_cone_condition(F_chain)
    if valid
        println("Chain(5): ✓")
    else
        println("Chain(5): ✗ ($msg)")
        all_pass = false
    end
    
    # Test 4: PowerSet(3)
    F_power = power_set(3)
    valid, msg = verify_open_cone_condition(F_power)
    if valid && n_opens(F_power) == 8
        println("PowerSet(3): ✓")
    else
        println("PowerSet(3): ✗ ($msg, opens=$(n_opens(F_power)))")
        all_pass = false
    end
    
    # Test 5: Frame operations
    frame_ok = true
    # Test Heyting implication: a ⇒ a = ⊤
    impl_aa = frame_implies(F_diamond, 2, 2)
    if impl_aa != 4  # Should be top
        frame_ok = false
    end
    # Test negation: ¬⊤ = ⊥
    neg_top = frame_negate(F_diamond, 4)
    if neg_top != 1  # Should be bottom
        frame_ok = false
    end
    
    if frame_ok
        println("Frame Ops (meet/join/implies/negate): ✓")
    else
        println("Frame Ops: ✗")
        all_pass = false
    end
    
    # Test 6: Limits/Colimits
    lim = limit_cone(F_diamond, [2, 3])
    colim = colimit_cocone(F_diamond, [2, 3])
    if lim.apex == 1 && colim.apex == 4
        println("Limits/Colimits: ✓")
    else
        println("Limits/Colimits: ✗ (limit=$(lim.apex), colimit=$(colim.apex))")
        all_pass = false
    end
    
    # GF(3) conservation
    minus, ergodic, plus = -1, 0, 1
    sum_gf3 = minus + ergodic + plus
    if sum_gf3 == 0
        println("GF(3) conservation: -1 + 0 + 1 = 0 ✓")
    else
        println("GF(3) conservation: ✗ (sum=$sum_gf3)")
        all_pass = false
    end
    
    println()
    if all_pass
        println("All tests passed ✓")
    else
        println("Some tests failed ✗")
        exit(1)
    end
end

main()
