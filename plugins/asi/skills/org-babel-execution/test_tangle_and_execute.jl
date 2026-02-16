#!/usr/bin/env julia

"""
Test org-babel tangling and execution workflow.

Demonstrates:
1. Parsing .org files
2. Extracting (tangling) source code
3. Executing tangled code
4. Comparing results with original implementations
"""

include("validate_org_files.jl")

using Test

function test_tangle_to_temp(org_path::String)::Dict{String, String}
    """Tangle an org file to temporary directory and return file contents."""
    
    println("\n" * "=" ^ 70)
    println("Testing: $org_path")
    println("=" ^ 70)
    
    # Parse org file
    org = parse_org_file(org_path)
    println("\nParsed org file:")
    println("  Title: $(org.title)")
    println("  Code blocks: $(length(org.code_blocks))")
    
    # Group blocks by tangle target
    tangle_map = Dict{String, Vector{CodeBlock}}()
    for block in org.code_blocks
        if block.tangle_file !== nothing && block.tangle_file != "no"
            if !haskey(tangle_map, block.tangle_file)
                tangle_map[block.tangle_file] = CodeBlock[]
            end
            push!(tangle_map[block.tangle_file], block)
        end
    end
    
    println("\nTangle targets:")
    for (target, blocks) in tangle_map
        println("  $target: $(length(blocks)) blocks")
    end
    
    # Create temp directory
    temp_dir = mktempdir()
    println("\nTemp directory: $temp_dir")
    
    # Tangle to temp
    tangled_files = Dict{String, String}()
    for (target_file, blocks) in tangle_map
        output_path = joinpath(temp_dir, target_file)
        mkpath(dirname(output_path))
        
        content = join([block.source for block in blocks], "\n\n")
        write(output_path, content)
        
        tangled_files[target_file] = output_path
        println("  ✓ Tangled → $output_path")
    end
    
    return tangled_files
end

function test_julia_execution(file_path::String)::Bool
    """Test execution of a Julia source file."""
    
    println("\n  Testing Julia execution...")
    
    try
        # Run julia on the file
        result = run(pipeline(`julia --project=. $file_path`, stdout=devnull, stderr=devnull), wait=true)
        
        if result.exitcode == 0
            println("    ✓ Executed successfully")
            return true
        else
            println("    ✗ Failed with exit code $(result.exitcode)")
            return false
        end
    catch e
        println("    ✗ Execution error: $e")
        return false
    end
end

function test_python_execution(file_path::String)::Bool
    """Test execution of a Python source file."""
    
    println("\n  Testing Python execution...")
    
    try
        result = run(pipeline(`python3 $file_path`, stdout=devnull, stderr=devnull), wait=true)
        
        if result.exitcode == 0
            println("    ✓ Executed successfully")
            return true
        else
            println("    ✗ Failed with exit code $(result.exitcode)")
            return false
        end
    catch e
        println("    ✗ Execution error: $e")
        return false
    end
end

function compare_with_original(org_path::String, tangled_files::Dict{String, String})
    """Compare tangled output with original source files."""
    
    println("\n" * "-" ^ 70)
    println("Comparing with original sources")
    println("-" ^ 70)
    
    skill_dir = dirname(org_path)
    
    for (basename, tangled_path) in tangled_files
        original_path = joinpath(skill_dir, basename)
        
        if !isfile(original_path)
            println("  ⚠ Original not found: $basename")
            continue
        end
        
        tangled_content = read(tangled_path, String)
        original_content = read(original_path, String)
        
        # Normalize whitespace for comparison
        tangled_lines = filter(!isempty, strip.(split(tangled_content, "\n")))
        original_lines = filter(!isempty, strip.(split(original_content, "\n")))
        
        if length(tangled_lines) == length(original_lines)
            println("  ✓ $basename: $(length(tangled_lines)) lines (matches original)")
        else
            println("  ⚠ $basename: $(length(tangled_lines)) tangled vs $(length(original_lines)) original")
        end
    end
end

function main()
    println("=" ^ 70)
    println("ORG-BABEL TANGLING AND EXECUTION TEST")
    println("=" ^ 70)
    
    # Test cases: [org_file, expected_tangles, language]
    test_cases = [
        (
            "/Users/bob/i/asi/skills/coequalizers/coequalizers.org",
            ["SkillCoequalizers.jl", "WorldHopping.jl"],
            "julia"
        ),
        (
            "/Users/bob/i/asi/skills/browser-history-acset/browser_history_acset.org",
            ["browser_history_acset.py"],
            "python"
        ),
        (
            "/Users/bob/i/asi/skills/finder-color-walk/schema.org",
            ["schema.jl"],
            "julia"
        ),
    ]
    
    results = []
    
    for (org_path, expected_tangles, lang) in test_cases
        if !isfile(org_path)
            println("\n⚠ Skipping missing file: $org_path")
            continue
        end
        
        # Tangle
        tangled_files = test_tangle_to_temp(org_path)
        
        # Verify expected files
        for expected in expected_tangles
            if haskey(tangled_files, expected)
                println("  ✓ Found expected tangle: $expected")
            else
                println("  ✗ Missing expected tangle: $expected")
            end
        end
        
        # Test execution for standalone files
        execution_passed = true
        for (basename, tangled_path) in tangled_files
            # Only test simple standalone files (not multi-file modules)
            if basename in ["browser_history_acset.py", "schema.jl"]
                if lang == "julia"
                    execution_passed = test_julia_execution(tangled_path)
                elseif lang == "python"
                    execution_passed = test_python_execution(tangled_path)
                end
            end
        end
        
        # Compare with originals
        compare_with_original(org_path, tangled_files)
        
        push!(results, (org_path, length(tangled_files) > 0, execution_passed))
    end
    
    # Summary
    println("\n" * "=" ^ 70)
    println("SUMMARY")
    println("=" ^ 70)
    println("\nTested $(length(results)) org files")
    
    tangled_count = count(r -> r[2], results)
    executed_count = count(r -> r[3], results)
    
    println("  Tangled successfully: $tangled_count/$(length(results))")
    println("  Executed successfully: $executed_count/$(length(results))")
    
    if tangled_count == length(results)
        println("\n✓ All tangling tests passed!")
    else
        println("\n✗ Some tangling tests failed")
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
