# Phase 2: Export Skills for MLX+OLMo Embedding
# File: production_phase2_export_skills.jl

using Dates

println("\n" * "="^80)
println("PHASE 2: EXPORT SKILLS FOR MLX+OLMO EMBEDDING")
println("="^80)

# Load GMRA from Phase 1 (assuming gmra structure exists in scope)
# If not in scope, you need to run the GMRA loading first
if !@isdefined(gmra)
    println("\n⚠ GMRA not loaded. Running GMRA loader...")
    include("GMRA_WORLDS_UNWORLDING.jl")
end

println("\n✓ GMRA structure available ($(length(gmra.skills)) skills)")

# Export skills with full context for embedding
function export_skills_for_mlx_embedding(gmra::Dict)::Vector{Dict}
    skills_export = []

    for skill in gmra.skills
        # Rich context for OLMo embedding
        skill_dict = Dict(
            "id" => skill.id,
            "skill_name" => skill.skill_name,
            "project_name" => skill.project_name,  # Get from parent group
            "world" => skill.parent_world,
            "trit" => skill.gf3_trit,
            "color" => skill.gay_color,

            # Embedding context: combine multiple fields for semantic richness
            "embedding_text" => string(
                "Skill: ", skill.skill_name, ". ",
                "Project: ", skill.project_name, ". ",
                "World: ", skill.parent_world, ". ",
                "Category: ", skill.gf3_trit == 1 ? "generative" : (skill.gf3_trit == 0 ? "neutral" : "validating"), "."
            )
        )

        push!(skills_export, skill_dict)
    end

    return skills_export
end

# Try to get project names from groups (enhanced context)
function get_project_name(skill_id::Int, gmra::Dict)::String
    # Find which group this skill belongs to
    for group in gmra.groups
        if group.id == skill.parent_group
            return group.project_name
        end
    end
    return "unknown_project"
end

# Enhanced export with better context
skills_export = []
for skill in gmra.skills
    project_name = "unknown"

    # Find project from group
    for group in gmra.groups
        if group.id == skill.parent_group
            project_name = group.project_name
            break
        end
    end

    push!(skills_export, Dict(
        "id" => skill.id,
        "skill_name" => skill.skill_name,
        "project_name" => project_name,
        "world" => skill.parent_world,
        "trit" => skill.gf3_trit,
        "color" => skill.gay_color,
        "embedding_text" => "Skill: $(skill.skill_name). Project: $project_name. World: $(skill.parent_world). Category: $(skill.gf3_trit == 1 ? "generative" : (skill.gf3_trit == 0 ? "neutral" : "validating"))."
    ))
end

# Save to TSV (simpler format, no external dependencies)
output_file_tsv = "gmra_skills_export_mlx.tsv"
output_file_txt = "gmra_skills_export_mlx.txt"

# TSV format for easier Python parsing
open(output_file_tsv, "w") do f
    write(f, "id\tskill_name\tproject_name\tworld\ttrit\tcolor\tembedding_text\n")
    for skill in skills_export
        write(f, "$(skill["id"])\t$(skill["skill_name"])\t$(skill["project_name"])\t$(skill["world"])\t$(skill["trit"])\t$(skill["color"])\t$(skill["embedding_text"])\n")
    end
end

# Also save as simple text for reference
open(output_file_txt, "w") do f
    write(f, "GMRA Skills Export for MLX+OLMo Embedding\n")
    write(f, "Timestamp: $(string(now()))\n")
    write(f, "Framework: MLX\n")
    write(f, "Model: OLMo-7B-instruct\n")
    write(f, "Number of skills: $(length(skills_export))\n\n")

    for skill in skills_export
        write(f, "ID: $(skill["id"])\n")
        write(f, "  Skill: $(skill["skill_name"])\n")
        write(f, "  Project: $(skill["project_name"])\n")
        write(f, "  World: $(skill["world"])\n")
        write(f, "  Trit: $(skill["trit"])\n")
        write(f, "  Color: $(skill["color"])\n")
        write(f, "  Text: $(skill["embedding_text"])\n\n")
    end
end

println("\n✓ Exported $(length(skills_export)) skills")
println("  Format 1: $output_file_tsv (tab-separated for Python)")
println("  Format 2: $output_file_txt (human-readable)")

println("\nExport Format:")
println("  - id: Unique skill identifier")
println("  - skill_name: Name of the skill")
println("  - project_name: Parent project")
println("  - world: World directory (A-z)")
println("  - trit: GF(3) value (-1, 0, +1)")
println("  - color: GayMCP deterministic color")
println("  - embedding_text: Rich text for MLX+OLMo encoding")

println("\n✓ PHASE 2 COMPLETE: Skills ready for MLX+OLMo embedding")
println("  Next: python3 production_phase3_mlx_olmo_embed.py")
