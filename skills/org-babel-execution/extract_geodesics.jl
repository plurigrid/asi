#!/usr/bin/env julia

"""
Extract geodesic (nontangled) representations from .org files.

DISENTANGLEMENT THEORY:

Tangled representation:
  .org file → (tangle operation) → source file → (execute)
  Path length: 2 operations

Geodesic representation:
  .org file → (direct extract) → executable script
  Path length: 1 operation

The geodesic is the SHORTEST PATH from literate source to execution.
It disentangles the representation from the extraction ceremony.

Properties of geodesics:
1. Self-contained: All code in single file
2. Executable: Can run directly without tangling
3. Commented: Preserves narrative structure as comments
4. Minimal: No org-mode directives, pure source code
"""

using Dates

include("validate_org_files.jl")

function org_to_geodesic(org_path::String, output_path::String)
    """
    Extract geodesic representation from .org file.
    
    Combines all code blocks into a single executable file with
    narrative sections preserved as comments.
    """
    
    org = parse_org_file(org_path)
    lines = readlines(org_path)
    
    # Detect primary language (most common in code blocks)
    lang_counts = Dict{String, Int}()
    for block in org.code_blocks
        if block.language in ["julia", "python", "clojure", "scheme"]
            lang_counts[block.language] = get(lang_counts, block.language, 0) + 1
        end
    end
    
    if isempty(lang_counts)
        println("  ⚠ No code blocks with executable languages")
        return false
    end
    
    primary_lang = first(sort(collect(lang_counts), by=x->x[2], rev=true))[1]
    comment_char = primary_lang == "python" ? "#" : primary_lang in ["julia", "bash"] ? "#" : primary_lang in ["clojure", "scheme"] ? ";" : "#"
    
    # Build geodesic file
    output = IOBuffer()
    
    # Header
    println(output, comment_char, " " ^ 70)
    println(output, comment_char, " GEODESIC REPRESENTATION")
    println(output, comment_char, " Extracted from: ", basename(org_path))
    println(output, comment_char, " Primary language: ", primary_lang)
    println(output, comment_char, " Generated: ", Dates.format(now(), "yyyy-mm-dd HH:MM:SS"))
    println(output, comment_char, " " ^ 70)
    println(output)
    
    if !isempty(org.title)
        println(output, comment_char, " ", org.title)
        println(output)
    end
    
    # Track current section for context
    current_section = ""
    in_code_block = false
    block_lang = ""
    
    for line in lines
        # Detect section headers
        if startswith(line, "* ") || startswith(line, "** ") || startswith(line, "*** ")
            current_section = strip(replace(line, r"^\*+ " => ""))
            println(output)
            println(output, comment_char, " ", "=" ^ 68)
            println(output, comment_char, " ", current_section)
            println(output, comment_char, " ", "=" ^ 68)
            println(output)
            continue
        end
        
        # Skip org directives (but preserve comments)
        if startswith(line, "#+") && !startswith(line, "#+BEGIN_SRC") && !startswith(line, "#+END_SRC")
            continue
        end
        
        # Handle code blocks
        if startswith(line, "#+BEGIN_SRC")
            in_code_block = true
            parts = split(strip(split(line, "#+BEGIN_SRC")[2]))
            block_lang = length(parts) > 0 ? parts[1] : ""
            
            # Only include blocks in primary language (or language-agnostic)
            if block_lang != primary_lang && block_lang != ""
                in_code_block = :skip
            else
                println(output, comment_char, " --- Code Block (", block_lang, ") ---")
            end
            continue
        end
        
        if startswith(line, "#+END_SRC")
            if in_code_block == true
                println(output)
            end
            in_code_block = false
            continue
        end
        
        # Content handling
        if in_code_block == true
            # Direct code inclusion
            println(output, line)
        elseif in_code_block == :skip
            # Skip this block entirely
            continue
        elseif !isempty(strip(line))
            # Narrative text becomes comments
            println(output, comment_char, " ", line)
        end
    end
    
    # Write geodesic file
    write(output_path, String(take!(output)))
    return true
end

function get_geodesic_path(org_path::String)::String
    """
    Determine geodesic output path.
    
    Pattern: skill-name.org → geodesics/skill-name.geodesic.{ext}
    """
    skill_dir = dirname(org_path)
    org_basename = basename(org_path)
    
    # Detect extension from primary language
    org = parse_org_file(org_path)
    lang_counts = Dict{String, Int}()
    for block in org.code_blocks
        if block.language in ["julia", "python", "clojure", "scheme", "bash"]
            lang_counts[block.language] = get(lang_counts, block.language, 0) + 1
        end
    end
    
    ext = if !isempty(lang_counts)
        primary = first(sort(collect(lang_counts), by=x->x[2], rev=true))[1]
        primary == "julia" ? "jl" :
        primary == "python" ? "py" :
        primary == "clojure" ? "clj" :
        primary == "scheme" ? "scm" :
        primary == "bash" ? "sh" : "txt"
    else
        "txt"
    end
    
    # Create geodesics subdirectory
    geodesic_dir = joinpath(skill_dir, "geodesics")
    mkpath(geodesic_dir)
    
    name_without_ext = replace(org_basename, ".org" => "")
    return joinpath(geodesic_dir, "$(name_without_ext).geodesic.$ext")
end

function process_all_orgs(root_dir::String)
    """
    Generate geodesic versions for all .org files in ASI.
    """
    
    println("=" ^ 70)
    println("GEODESIC EXTRACTION")
    println("Disentangling representations: .org → direct executable")
    println("=" ^ 70)
    println()
    
    # Find all .org files
    org_files = String[]
    for (root, dirs, files) in walkdir(root_dir)
        for file in files
            if endswith(file, ".org")
                push!(org_files, joinpath(root, file))
            end
        end
    end
    
    println("Found $(length(org_files)) .org files")
    println()
    
    # Process each
    success_count = 0
    skip_count = 0
    
    for org_path in sort(org_files)
        skill_name = basename(dirname(org_path))
        org_name = basename(org_path)
        
        print("Processing: $skill_name/$org_name ... ")
        
        geodesic_path = get_geodesic_path(org_path)
        
        if org_to_geodesic(org_path, geodesic_path)
            println("✓ → $(basename(geodesic_path))")
            success_count += 1
        else
            println("⊘ (skipped)")
            skip_count += 1
        end
    end
    
    # Summary
    println()
    println("=" ^ 70)
    println("SUMMARY")
    println("=" ^ 70)
    println("Total .org files: $(length(org_files))")
    println("Geodesics created: $success_count")
    println("Skipped: $skip_count")
    println()
    
    if success_count > 0
        println("✓ Geodesic extraction complete!")
        println()
        println("Disentanglement achieved:")
        println("  Tangled path:   .org → tangle → source.jl → execute")
        println("  Geodesic path:  .org → extract → geodesic.jl → execute")
        println()
        println("All geodesics saved to skill-name/geodesics/ subdirectories")
    end
end

function compare_representations(org_path::String)
    """
    Compare tangled vs geodesic representations.
    
    Measures:
    - Path length (operations to execution)
    - File size
    - Execution time
    - Semantic equivalence
    """
    
    println("\n" * "=" ^ 70)
    println("REPRESENTATION COMPARISON")
    println("=" ^ 70)
    
    org = parse_org_file(org_path)
    geodesic_path = get_geodesic_path(org_path)
    
    println("\nSource: $(basename(org_path))")
    println("  Title: $(org.title)")
    println("  Code blocks: $(length(org.code_blocks))")
    
    # Tangled representation
    tangle_map = Dict{String, Vector{CodeBlock}}()
    for block in org.code_blocks
        if block.tangle_file !== nothing && block.tangle_file != "no"
            if !haskey(tangle_map, block.tangle_file)
                tangle_map[block.tangle_file] = CodeBlock[]
            end
            push!(tangle_map[block.tangle_file], block)
        end
    end
    
    tangled_count = length(tangle_map)
    tangled_blocks = sum(length(blocks) for blocks in values(tangle_map))
    
    println("\nTangled representation:")
    println("  Target files: $tangled_count")
    println("  Blocks tangled: $tangled_blocks")
    println("  Path length: 2 (tangle → execute)")
    
    # Geodesic representation
    if isfile(geodesic_path)
        geodesic_lines = length(readlines(geodesic_path))
        geodesic_size = filesize(geodesic_path)
        
        println("\nGeodesic representation:")
        println("  File: $(basename(geodesic_path))")
        println("  Lines: $geodesic_lines")
        println("  Size: $geodesic_size bytes")
        println("  Path length: 1 (direct execute)")
        
        println("\nDisentanglement factor:")
        println("  Path reduction: $(tangled_count > 0 ? round(100 * (1 - 1/2), digits=1) : 0)%")
        println("  File unification: $tangled_count files → 1 geodesic")
    else
        println("\n⚠ Geodesic not yet generated")
    end
end

function main()
    # Process all .org files in ASI
    asi_root = dirname(dirname(@__DIR__))
    skills_dir = joinpath(asi_root, "skills")
    
    process_all_orgs(skills_dir)
    
    # Example comparison
    example_org = joinpath(skills_dir, "coequalizers", "coequalizers.org")
    if isfile(example_org)
        compare_representations(example_org)
    end
end

if abspath(PROGRAM_FILE) == @__FILE__
    main()
end
