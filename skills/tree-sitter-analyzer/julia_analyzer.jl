"""
    TreeSitterJuliaAnalyzer

Julia-specific code analysis using tree-sitter patterns.

Provides advanced Julia-specific analysis including:
- Docstring extraction
- Type annotation analysis
- Macro detection
- Module structure discovery
"""

module TreeSitterJuliaAnalyzer

using LinearAlgebra
using Statistics

export
    extract_docstrings,
    extract_type_annotations,
    find_macros,
    analyze_module_structure,
    JuliaModule,
    DocstringInfo,
    MacroUsage

# ============================================================================
# Part 1: Julia-Specific Data Structures
# ============================================================================

"""
    DocstringInfo

Information about a docstring and its associated definition.
"""
struct DocstringInfo
    text::String
    associated_symbol::String
    symbol_type::String  # "function", "struct", "module"
    line::Int
end

"""
    MacroUsage

Information about macro usage in code.
"""
struct MacroUsage
    name::String
    args::Vector{String}
    line::Int
end

"""
    JuliaModule

Complete Julia module analysis.
"""
struct JuliaModule
    name::String
    path::String
    docstring::Union{String, Nothing}
    functions::Vector{String}
    structs::Vector{String}
    macros::Vector{MacroUsage}
    type_annotations::Dict{String, String}
    complexity::Int
end

# ============================================================================
# Part 2: Docstring Extraction
# ============================================================================

"""
    extract_docstrings(content::String) -> Vector{DocstringInfo}

Extract all docstrings from Julia code with their associated symbols.
"""
function extract_docstrings(content::String)::Vector{DocstringInfo}
    docstrings = DocstringInfo[]

    lines = split(content, '\n')
    i = 1
    while i <= length(lines)
        line = lines[i]

        # Match triple-quoted docstring - fixed regex
        if match(r"^\s*\"\"\"", line) !== nothing
            docstring_lines = [line]
            i += 1

            # Collect docstring lines until closing """
            while i <= length(lines)
                current_line = lines[i]
                # Check if this line contains closing """
                if match(r"\"\"\"", current_line) !== nothing
                    push!(docstring_lines, current_line)
                    break
                else
                    push!(docstring_lines, current_line)
                end
                i += 1
            end

            # Extract docstring text (skip first and last line which contain """)
            if length(docstring_lines) >= 2
                docstring_text = if length(docstring_lines) > 2
                    join(docstring_lines[2:end-1], '\n')
                else
                    ""
                end
                docstring_text = strip(docstring_text)

                # Look ahead for associated symbol
                i += 1
                while i <= length(lines) && isempty(strip(lines[i]))
                    i += 1
                end

                if i <= length(lines)
                    next_line = lines[i]

                    # Determine symbol type and name
                    if match(r"^\s*function\s+(\w+)", next_line) !== nothing
                        m = match(r"^\s*function\s+(\w+)", next_line)
                        symbol_name = m.captures[1]
                        push!(docstrings, DocstringInfo(
                            docstring_text,
                            symbol_name,
                            "function",
                            i
                        ))
                    elseif match(r"^\s*struct\s+(\w+)", next_line) !== nothing
                        m = match(r"^\s*struct\s+(\w+)", next_line)
                        symbol_name = m.captures[1]
                        push!(docstrings, DocstringInfo(
                            docstring_text,
                            symbol_name,
                            "struct",
                            i
                        ))
                    elseif match(r"^\s*module\s+(\w+)", next_line) !== nothing
                        m = match(r"^\s*module\s+(\w+)", next_line)
                        symbol_name = m.captures[1]
                        push!(docstrings, DocstringInfo(
                            docstring_text,
                            symbol_name,
                            "module",
                            i
                        ))
                    end
                end
            else
                i += 1
            end
        else
            i += 1
        end
    end

    return docstrings
end

# ============================================================================
# Part 3: Type Annotation Analysis
# ============================================================================

"""
    extract_type_annotations(content::String) -> Dict{String, String}

Extract type annotations from function signatures and variable declarations.
"""
function extract_type_annotations(content::String)::Dict{String, String}
    annotations = Dict{String, String}()

    lines = split(content, '\n')
    for line in lines
        # Function return type: function name(args)::ReturnType
        func_match = match(r"function\s+(\w+).*::\s*(\w+)", line)
        if !isnothing(func_match)
            func_name = func_match.captures[1]
            return_type = func_match.captures[2]
            annotations[func_name] = return_type
        end

        # Variable type annotation: name::Type
        var_match = match(r"^\s*(\w+)\s*::\s*(\w+)", line)
        if !isnothing(var_match)
            var_name = var_match.captures[1]
            var_type = var_match.captures[2]
            annotations[var_name] = var_type
        end
    end

    return annotations
end

# ============================================================================
# Part 4: Macro Detection
# ============================================================================

"""
    find_macros(content::String) -> Vector{MacroUsage}

Find all macro usages in Julia code.
"""
function find_macros(content::String)::Vector{MacroUsage}
    macros = MacroUsage[]

    lines = split(content, '\n')
    for (line_num, line) in enumerate(lines)
        # Match @macroname or @macroname(args)
        macro_pattern = r"@(\w+)(?:\((.*?)\))?"
        macro_matches = collect(eachmatch(macro_pattern, line))

        for m in macro_matches
            macro_name = m.captures[1]
            args_str = if length(m.captures) >= 2 && !isnothing(m.captures[2])
                m.captures[2]
            else
                ""
            end

            # Parse arguments
            args = if !isempty(args_str)
                arg_list = split(args_str, ',')
                [strip(arg) for arg in arg_list]
            else
                String[]
            end

            push!(macros, MacroUsage(
                macro_name,
                args,
                line_num
            ))
        end
    end

    return macros
end

# ============================================================================
# Part 5: Module Structure Analysis
# ============================================================================

"""
    analyze_module_structure(path::String) -> JuliaModule

Comprehensive analysis of Julia module structure.
"""
function analyze_module_structure(path::String)::JuliaModule
    if !isfile(path)
        return JuliaModule(
            basename(path),
            path,
            nothing,
            String[],
            String[],
            MacroUsage[],
            Dict{String, String}(),
            0
        )
    end

    try
        content = read(path, String)

        # Extract module name
        module_match = match(r"module\s+(\w+)", content)
        module_name = if !isnothing(module_match)
            module_match.captures[1]
        else
            basename(path, ".jl")
        end

        # Extract module-level docstring
        docstrings = extract_docstrings(content)
        module_doc = if !isempty(docstrings) && docstrings[1].symbol_type == "module"
            docstrings[1].text
        else
            nothing
        end

        # Extract symbols
        functions = extract_function_names(content)
        structs = extract_struct_names(content)

        # Extract macros and type annotations
        macros = find_macros(content)
        type_annotations = extract_type_annotations(content)

        # Compute complexity (simplified: lines of code)
        complexity = length(split(content, '\n'))

        return JuliaModule(
            module_name,
            path,
            module_doc,
            functions,
            structs,
            macros,
            type_annotations,
            complexity
        )
    catch e
        @warn "Module structure analysis failed for $path: $e"
        return JuliaModule(
            basename(path, ".jl"),
            path,
            nothing,
            String[],
            String[],
            MacroUsage[],
            Dict{String, String}(),
            0
        )
    end
end

# ============================================================================
# Part 6: Helper Functions
# ============================================================================

"""
    extract_function_names(content::String) -> Vector{String}

Extract all function names from Julia code.
"""
function extract_function_names(content::String)::Vector{String}
    functions = String[]

    lines = split(content, '\n')
    for line in lines
        # Match: function name(...) or name(...) =
        func_match = match(r"^\s*(?:function\s+)?(\w+)\s*\(", line)
        if !isnothing(func_match)
            push!(functions, func_match.captures[1])
        end
    end

    return unique(functions)
end

"""
    extract_struct_names(content::String) -> Vector{String}

Extract all struct names from Julia code.
"""
function extract_struct_names(content::String)::Vector{String}
    structs = String[]

    lines = split(content, '\n')
    for line in lines
        # Match: struct Name or mutable struct Name
        struct_match = match(r"^\s*(?:mutable\s+)?struct\s+(\w+)", line)
        if !isnothing(struct_match)
            push!(structs, struct_match.captures[1])
        end
    end

    return unique(structs)
end

"""
    compute_cyclomatic_complexity(content::String) -> Int

Estimate cyclomatic complexity based on control flow statements.
"""
function compute_cyclomatic_complexity(content::String)::Int
    complexity = 1  # Base complexity

    lines = split(content, '\n')
    for line in lines
        # Count control flow statements
        complexity += count(
            pat -> match(pat, line) !== nothing,
            [
                r"\bif\b",
                r"\belseif\b",
                r"\bfor\b",
                r"\bwhile\b",
                r"\btry\b",
                r"\bcatch\b",
            ]
        )
    end

    return complexity
end

end  # module TreeSitterJuliaAnalyzer
