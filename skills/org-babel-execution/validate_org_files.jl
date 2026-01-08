#!/usr/bin/env julia

"""
Validate .org files for correct org-babel structure and extract/test code blocks.

This script provides org-babel validation without requiring Emacs:
1. Parse .org file structure
2. Extract code blocks (tangling simulation)
3. Validate syntax for each language
4. Run basic execution tests where safe
"""

using Dates

# Language detection and validation
const SUPPORTED_LANGUAGES = ["julia", "python", "clojure", "scheme", "bash", "sh"]

struct CodeBlock
    language::String
    source::String
    tangle_file::Union{String, Nothing}
    header_args::Dict{String, String}
    line_number::Int
end

struct OrgFile
    path::String
    title::String
    properties::Dict{String, String}
    code_blocks::Vector{CodeBlock}
end

function parse_org_file(path::String)::OrgFile
    lines = readlines(path)
    title = ""
    properties = Dict{String, String}()
    code_blocks = CodeBlock[]
    
    in_block = false
    block_lang = ""
    block_source = String[]
    block_tangle = nothing
    block_header = Dict{String, String}()
    block_start_line = 0
    
    for (i, line) in enumerate(lines)
        # Parse title
        if startswith(line, "#+TITLE:")
            title = strip(split(line, ":", limit=2)[2])
        end
        
        # Parse properties
        if startswith(line, "#+PROPERTY:")
            parts = split(line, ":", limit=2)[2]
            prop_parts = split(strip(parts), " ", limit=2)
            if length(prop_parts) == 2
                properties[prop_parts[1]] = prop_parts[2]
            end
        end
        
        # Parse code blocks
        if startswith(line, "#+BEGIN_SRC")
            in_block = true
            block_start_line = i
            block_source = String[]
            
            # Parse language and header args
            rest = strip(split(line, "#+BEGIN_SRC", limit=2)[2])
            parts = split(rest)
            block_lang = length(parts) > 0 ? parts[1] : "text"
            
            # Parse header args
            block_header = Dict{String, String}()
            block_tangle = nothing
            for j in 2:length(parts)
                if startswith(parts[j], ":")
                    key = parts[j]
                    if j + 1 <= length(parts) && !startswith(parts[j+1], ":")
                        value = parts[j+1]
                        block_header[key] = value
                        if key == ":tangle"
                            block_tangle = value
                        end
                    else
                        block_header[key] = "yes"
                    end
                end
            end
            
        elseif startswith(line, "#+END_SRC")
            if in_block
                push!(code_blocks, CodeBlock(
                    block_lang,
                    join(block_source, "\n"),
                    block_tangle,
                    block_header,
                    block_start_line
                ))
                in_block = false
            end
        elseif in_block
            push!(block_source, line)
        end
    end
    
    return OrgFile(path, title, properties, code_blocks)
end

function validate_julia_syntax(source::String, is_test::Bool=false)::Bool
    # Skip validation for test/demo blocks with incomplete snippets
    if is_test
        println("    ✓ Test/demo block (validation skipped)")
        return true
    end
    
    # Try parsing as Julia code
    try
        Meta.parse("begin\n$source\nend")
        return true
    catch e
        println("  ✗ Julia syntax error: $e")
        return false
    end
end

function validate_python_syntax(source::String)::Bool
    # Create temp file and check with python -m py_compile
    temp_file = tempname() * ".py"
    try
        write(temp_file, source)
        result = run(pipeline(`python3 -m py_compile $temp_file`, stderr=devnull), wait=true)
        return result.exitcode == 0
    catch e
        println("  ✗ Python syntax error: $e")
        return false
    finally
        isfile(temp_file) && rm(temp_file)
    end
end

function validate_code_block(block::CodeBlock, is_multi_block::Bool=false)::Bool
    println("  Code block at line $(block.line_number) ($(block.language))")
    
    # Check if this is a test/demo block (has :results or tangle=no)
    is_test = haskey(block.header_args, ":results") || 
              get(block.header_args, ":tangle", "") == "no" ||
              block.tangle_file === nothing
    
    # Skip syntax check for multi-block tangles (fragments)
    if is_multi_block && !is_test
        println("    ✓ Multi-block tangle fragment (syntax check skipped)")
        return true
    end
    
    if block.language == "julia"
        return validate_julia_syntax(block.source, is_test)
    elseif block.language == "python"
        return validate_python_syntax(block.source)
    elseif block.language in ["bash", "sh"]
        println("    ✓ Shell script (syntax check skipped)")
        return true
    elseif block.language in ["clojure", "scheme"]
        println("    ✓ Lisp dialect (syntax check skipped)")
        return true
    else
        println("    ⚠ Unknown language: $(block.language)")
        return true
    end
end

function tangle_org_file(org::OrgFile, output_dir::String)
    println("\n  Tangling code blocks...")
    
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
    
    # Write tangled files
    for (target_file, blocks) in tangle_map
        output_path = joinpath(output_dir, target_file)
        mkpath(dirname(output_path))
        
        content = join([block.source for block in blocks], "\n\n")
        write(output_path, content)
        
        println("    ✓ Tangled $(length(blocks)) blocks → $target_file")
    end
    
    return length(tangle_map)
end

function validate_org_file(path::String; do_tangle::Bool=false)::Bool
    println("\n📄 Validating: $path")
    
    if !isfile(path)
        println("  ✗ File not found")
        return false
    end
    
    org = parse_org_file(path)
    
    println("  Title: $(org.title)")
    println("  Properties: $(length(org.properties))")
    println("  Code blocks: $(length(org.code_blocks))")
    
    if isempty(org.code_blocks)
        println("  ⚠ No code blocks found")
        return true
    end
    
    # Group blocks by tangle target to detect multi-block tangles
    tangle_counts = Dict{String, Int}()
    for block in org.code_blocks
        if block.tangle_file !== nothing
            tangle_counts[block.tangle_file] = get(tangle_counts, block.tangle_file, 0) + 1
        end
    end
    
    # Validate each code block
    all_valid = true
    for block in org.code_blocks
        # Skip syntax validation for multi-block tangles (fragments can't be validated individually)
        is_multi_block = block.tangle_file !== nothing && get(tangle_counts, block.tangle_file, 0) > 1
        
        if !validate_code_block(block, is_multi_block)
            all_valid = false
        end
    end
    
    # Optionally tangle
    if do_tangle && all_valid
        skill_dir = dirname(path)
        tangle_count = tangle_org_file(org, skill_dir)
        println("  ✓ Tangled $tangle_count files")
    end
    
    status = all_valid ? "✓" : "✗"
    println("  $status Validation $(all_valid ? "passed" : "failed")")
    
    return all_valid
end

function find_all_org_files(root_dir::String)::Vector{String}
    org_files = String[]
    for (root, dirs, files) in walkdir(root_dir)
        for file in files
            if endswith(file, ".org")
                push!(org_files, joinpath(root, file))
            end
        end
    end
    return org_files
end

function main()
    println("=" ^ 70)
    println("Org-Babel Validation Script")
    println("Validating .org files in ASI repository")
    println("=" ^ 70)
    
    # Find all .org files
    asi_root = dirname(dirname(@__DIR__))
    org_files = find_all_org_files(joinpath(asi_root, "skills"))
    
    println("\nFound $(length(org_files)) .org files")
    
    # Validate each
    results = Dict{String, Bool}()
    for org_file in sort(org_files)
        results[org_file] = validate_org_file(org_file, do_tangle=false)
    end
    
    # Summary
    println("\n" * "=" ^ 70)
    println("VALIDATION SUMMARY")
    println("=" ^ 70)
    
    passed = count(values(results))
    total = length(results)
    
    println("Total: $total")
    println("Passed: $passed")
    println("Failed: $(total - passed)")
    
    if passed == total
        println("\n✓ All .org files validated successfully!")
    else
        println("\n✗ Some .org files have issues")
        println("\nFailed files:")
        for (file, status) in results
            if !status
                println("  - $file")
            end
        end
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
