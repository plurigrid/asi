#                                                                      
# GEODESIC REPRESENTATION
# Extracted from: convert_to_literate.org
# Primary language: julia
# Generated: 2026-01-07 19:02:45
#                                                                      

# Org Babel Execution - Literate Implementation


# ====================================================================
# Overview
# ====================================================================

# Literate implementation of the *org-babel-execution* skill.

# ====================================================================
# Original Source
# ====================================================================

# This was automatically converted from =convert_to_literate.jl=.

# ====================================================================
# Implementation
# ====================================================================

# --- Code Block (julia) ---
#!/usr/bin/env julia

# convert_to_literate.jl
# Convert existing code files to literate .org format

using Printf
using Dates

"""
Detect programming language from file extension.
"""
function detect_language(filename::String)::String
    if endswith(filename, ".jl")
        return "julia"
    elseif endswith(filename, ".py")
        return "python"
    elseif endswith(filename, ".clj")
        return "clojure"
    elseif endswith(filename, ".rb")
        return "ruby"
    else
        return "text"
    end
end

"""
Generate org-babel header for language.
"""
function org_header(lang::String, filename::String)::String
    return """#+BEGIN_SRC $lang :tangle $filename
"""
end

"""
Convert a source file to org-babel format.
"""
function convert_to_org(source_file::String, output_org::String)
    # Read source
    source_code = read(source_file, String)
    lang = detect_language(source_file)
    basename_file = basename(source_file)
    
    # Extract skill name from path
    parts = splitpath(source_file)
    skill_idx = findfirst(x -> x == "skills", parts)
    skill_name = isnothing(skill_idx) ? "unknown" : parts[skill_idx + 1]
    
    # Generate org content
    org_content = """#+TITLE: $(titlecase(replace(skill_name, "-" => " "))) - Literate Implementation


# ====================================================================
# Overview
# ====================================================================


Literate implementation of the *$skill_name* skill.


# ====================================================================
# Original Source
# ====================================================================


This was automatically converted from =$basename_file=.


# ====================================================================
# Implementation
# ====================================================================



# ====================================================================
# Usage
# ====================================================================

# Execute the code above with =C-c C-c= or tangle with =C-c C-v t=.

# ====================================================================
# Testing
# ====================================================================

# Add test blocks here:

# ====================================================================
# Export
# ====================================================================

# To tangle: =M-x org-babel-tangle= or =C-c C-v t=
# To execute: =M-x org-babel-execute-buffer= or =C-c C-v C-b=
# To export: =M-x org-html-export-to-html= or =C-c C-e h h=
# """
#     # Write org file
#     write(output_org, org_content)
#     println("✓ Converted $source_file → $output_org")
# end
# """
# Scan a skill directory and convert all code files to .org.
# """
# function convert_skill(skill_dir::String)
#     println("=" ^ 70)
#     println("Converting skill: $(basename(skill_dir))")
#     println("=" ^ 70)
#     code_files = String[]
#     # Find all code files
#     for file in readdir(skill_dir, join=true)
#         if isfile(file) && any(endswith(file, ext) for ext in [".jl", ".py", ".clj", ".rb"])
#             push!(code_files, file)
#         end
#     end
#     if isempty(code_files)
#         println("No code files found")
#         return
#     end
#     println("Found $(length(code_files)) code file(s)")
#     # Convert each file
#     for code_file in code_files
#         basename_code = basename(code_file)
#         org_file = joinpath(skill_dir, replace(basename_code, r"\.(jl|py|clj|rb)$" => ".org"))
#         try
#             convert_to_org(code_file, org_file)
#         catch e
#             println("✗ Error converting $code_file: $e")
#         end
#     end
#     println()
# end
# """
# Convert all executable skills in asi repository.
# """
# function convert_all_skills(skills_dir::String="/Users/bob/i/asi/skills")
#     println("=" ^ 70)
#     println("ASI LITERATE PROGRAMMING CONVERSION")
#     println("=" ^ 70)
#     println()
#     converted = 0
#     skipped = 0
#     for skill_name in readdir(skills_dir)
#         skill_path = joinpath(skills_dir, skill_name)
#         if !isdir(skill_path)
#             continue
#         end
#         # Check if has code files
#         has_code = any(readdir(skill_path)) do file
#             any(endswith(file, ext) for ext in [".jl", ".py", ".clj", ".rb"])
#         end
#         if has_code
#             convert_skill(skill_path)
#             converted += 1
#         else
#             skipped += 1
#         end
#     end
#     println("=" ^ 70)
#     println("CONVERSION COMPLETE")
#     println("=" ^ 70)
#     println("Skills converted: $converted")
#     println("Skills skipped (no code): $skipped")
#     println()
# end
# # Main execution
# if abspath(PROGRAM_FILE) == @__FILE__
#     if length(ARGS) > 0
#         # Convert specific skill
#         convert_skill(ARGS[1])
#     else
#         # Convert all
#         convert_all_skills()
#     end
# end

# ====================================================================
# Usage
# ====================================================================

# Execute the code above with =C-c C-c= or tangle with =C-c C-v t=.

# ====================================================================
# Testing
# ====================================================================

# Add test blocks here:
# --- Code Block (julia) ---
# Add tests


# ====================================================================
# Export
# ====================================================================

# To tangle: =M-x org-babel-tangle= or =C-c C-v t=
# To execute: =M-x org-babel-execute-buffer= or =C-c C-v C-b=
# To export: =M-x org-html-export-to-html= or =C-c C-e h h=
