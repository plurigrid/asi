# Skill Network Diagram Visualization
#
# Generates SVG diagrams showing:
# 1. Skill dependency graphs with GF(3) coloring
# 2. Mixing time convergence curves
# 3. Hierarchical skill organization (Hackage-style)
# 4. Information propagation flow

require 'json'
require_relative 'skill_mixing_analysis'

module SkillDiagramVisualization
  # ============================================================================
  # SVG BUILDER: Generate SVG graphics programmatically
  # ============================================================================

  class SVGBuilder
    attr_reader :width
    attr_reader :height
    attr_reader :elements

    def initialize(width: 1200, height: 800)
      @width = width
      @height = height
      @elements = []
    end

    # Define colors for GF(3) roles
    def self.color_for_trit(trit)
      case trit
      when -1
        "#FF6B6B"  # Red - MINUS (validator)
      when 0
        "#4ECDC4"  # Teal - ERGODIC (coordinator)
      when 1
        "#95E1D3"  # Green - PLUS (generator)
      else
        "#CCCCCC"  # Gray - unknown
      end
    end

    def self.label_for_trit(trit)
      case trit
      when -1
        "MINUS"
      when 0
        "ERGODIC"
      when 1
        "PLUS"
      else
        "?"
      end
    end

    # Add SVG header
    def add_header
      @elements << %{<?xml version="1.0" encoding="UTF-8"?>}
      @elements << %{<svg width="#{@width}" height="#{@height}" xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink">}
      @elements << %{<defs>}
      @elements << %{<style>
        .skill-node { cursor: pointer; }
        .skill-node:hover circle { opacity: 0.8; }
        .skill-label { font-family: monospace; font-size: 11px; }
        .cluster-label { font-family: sans-serif; font-size: 14px; font-weight: bold; }
        .axis-label { font-family: monospace; font-size: 10px; }
        .legend-text { font-family: sans-serif; font-size: 12px; }
        .title { font-family: sans-serif; font-size: 18px; font-weight: bold; }
        line.edge { stroke: #666; stroke-width: 1; }
        line.edge-strong { stroke: #333; stroke-width: 2; }
        circle.node { stroke: #333; stroke-width: 1.5; }
      </style>}
      @elements << %{</defs>}
    end

    def add_rect(x, y, width, height, fill: "white", stroke: "black", stroke_width: 1, opacity: 1.0)
      @elements << %{<rect x="#{x}" y="#{y}" width="#{width}" height="#{height}" fill="#{fill}" stroke="#{stroke}" stroke-width="#{stroke_width}" opacity="#{opacity}" />}
    end

    def add_circle(x, y, radius, fill: "blue", stroke: "black", stroke_width: 1, id: nil, class_name: nil)
      id_attr = id ? %{ id="#{id}"} : ""
      class_attr = class_name ? %{ class="#{class_name}"} : ""
      @elements << %{<circle cx="#{x}" cy="#{y}" r="#{radius}" fill="#{fill}" stroke="#{stroke}" stroke-width="#{stroke_width}"#{id_attr}#{class_attr} />}
    end

    def add_line(x1, y1, x2, y2, stroke: "black", stroke_width: 1, dashed: false, class_name: nil)
      dash_attr = dashed ? %{ stroke-dasharray="5,5"} : ""
      class_attr = class_name ? %{ class="#{class_name}"} : ""
      @elements << %{<line x1="#{x1}" y1="#{y1}" x2="#{x2}" y2="#{y2}" stroke="#{stroke}" stroke-width="#{stroke_width}"#{dash_attr}#{class_attr} />}
    end

    def add_text(x, y, text, fill: "black", font_size: 12, class_name: nil, anchor: "start")
      class_attr = class_name ? %{ class="#{class_name}"} : ""
      @elements << %{<text x="#{x}" y="#{y}" fill="#{fill}" font-size="#{font_size}" text-anchor="#{anchor}"#{class_attr}>#{escape_xml(text)}</text>}
    end

    def add_arrow(x1, y1, x2, y2, stroke: "black", stroke_width: 1)
      # Draw line with arrowhead
      @elements << %{<defs><marker id="arrowhead" markerWidth="10" markerHeight="10" refX="9" refY="3" orient="auto"><polygon points="0 0, 10 3, 0 6" fill="#{stroke}" /></marker></defs>}
      @elements << %{<line x1="#{x1}" y1="#{y1}" x2="#{x2}" y2="#{y2}" stroke="#{stroke}" stroke-width="#{stroke_width}" marker-end="url(#arrowhead)" />}
    end

    def add_polygon(points, fill: "blue", stroke: "black", stroke_width: 1)
      points_str = points.map { |p| "#{p[0]},#{p[1]}" }.join(" ")
      @elements << %{<polygon points="#{points_str}" fill="#{fill}" stroke="#{stroke}" stroke-width="#{stroke_width}" />}
    end

    def add_path(d, fill: "none", stroke: "black", stroke_width: 1)
      @elements << %{<path d="#{d}" fill="#{fill}" stroke="#{stroke}" stroke-width="#{stroke_width}" />}
    end

    def add_group(id: nil, class_name: nil)
      id_attr = id ? %{ id="#{id}"} : ""
      class_attr = class_name ? %{ class="#{class_name}"} : ""
      @elements << %{<g#{id_attr}#{class_attr}>}
      yield
      @elements << %{</g>}
    end

    def add_footer
      @elements << %{</svg>}
    end

    def render
      add_header
      yield self
      add_footer
      @elements.join("\n")
    end

    private

    def escape_xml(str)
      str.gsub("&", "&amp;").gsub("<", "&lt;").gsub(">", "&gt;").gsub('"', "&quot;").gsub("'", "&apos;")
    end
  end

  # ============================================================================
  # GRAPH LAYOUT: Position nodes using force-directed algorithm
  # ============================================================================

  class ForceDirectedLayout
    def initialize(skills, width: 1000, height: 600, iterations: 50)
      @skills = skills
      @width = width
      @height = height
      @iterations = iterations
      @positions = {}
      @velocities = {}

      # Initialize random positions
      skills.each do |name, skill|
        @positions[name] = [rand(@width), rand(@height)]
        @velocities[name] = [0.0, 0.0]
      end
    end

    def layout
      @iterations.times do
        # Repulsive forces (all pairs)
        @positions.each_key do |name1|
          @positions.each_key do |name2|
            next if name1 == name2
            dx = @positions[name2][0] - @positions[name1][0]
            dy = @positions[name2][1] - @positions[name1][1]
            dist = Math.sqrt(dx*dx + dy*dy) + 1.0
            force = 50.0 / dist
            @velocities[name1][0] -= (dx / dist) * force
            @velocities[name1][1] -= (dy / dist) * force
          end
        end

        # Attractive forces (along edges)
        @skills.each do |name, skill|
          skill.dependencies.each do |dep|
            dx = @positions[dep][0] - @positions[name][0]
            dy = @positions[dep][1] - @positions[name][1]
            dist = Math.sqrt(dx*dx + dy*dy) + 1.0
            force = 0.1 * dist
            @velocities[name][0] += (dx / dist) * force
            @velocities[name][1] += (dy / dist) * force
          end
        end

        # Update positions with damping
        @positions.each_key do |name|
          @velocities[name][0] *= 0.9
          @velocities[name][1] *= 0.9
          @positions[name][0] += @velocities[name][0]
          @positions[name][1] += @velocities[name][1]

          # Keep within bounds
          @positions[name][0] = [10, [@width - 10, @positions[name][0]].min].max
          @positions[name][1] = [10, [@height - 10, @positions[name][1]].min].max
        end
      end

      @positions
    end

    def positions
      @positions
    end
  end

  # ============================================================================
  # DIAGRAM GENERATORS
  # ============================================================================

  class SkillNetworkDiagram
    def self.dependency_graph(network, output_file)
      # Compute layout
      layout = ForceDirectedLayout.new(network.skills, width: 1200, height: 800, iterations: 100)
      positions = layout.layout

      svg = SVGBuilder.new(width: 1200, height: 800)

      svg.render do |svg|
        # Title
        svg.add_text(600, 25, "Skill Dependency Network (GF(3) Colored)",
                     class_name: "title", anchor: "middle")

        # Legend
        svg.add_text(50, 50, "Legend:", class_name: "cluster-label")
        svg.add_circle(50, 70, 6, fill: SVGBuilder.color_for_trit(1))
        svg.add_text(65, 75, "PLUS (+1) - Generator", class_name: "legend-text")
        svg.add_circle(50, 95, 6, fill: SVGBuilder.color_for_trit(0))
        svg.add_text(65, 100, "ERGODIC (0) - Coordinator", class_name: "legend-text")
        svg.add_circle(50, 120, 6, fill: SVGBuilder.color_for_trit(-1))
        svg.add_text(65, 125, "MINUS (-1) - Validator", class_name: "legend-text")

        # Draw edges first (so they appear under nodes)
        network.skills.each do |name, skill|
          x1, y1 = positions[name]
          skill.dependencies.each do |dep|
            x2, y2 = positions[dep]
            svg.add_line(x1, y1, x2, y2, stroke: "#999", stroke_width: 1, class_name: "edge")
          end
        end

        # Draw nodes
        network.skills.each do |name, skill|
          x, y = positions[name]
          color = SVGBuilder.color_for_trit(skill.trit)
          svg.add_circle(x, y, 12, fill: color, stroke: "#333", stroke_width: 1.5, id: "skill-#{name}")

          # Label
          svg.add_text(x, y + 25, name[0..12], font_size: 9, class_name: "skill-label", anchor: "middle")
        end

        # Statistics box
        gf3 = network.analyze_gf3_conservation
        stats_text = [
          "Skills: #{network.skills.size}",
          "PLUS: #{gf3[:counts][:plus_1]} | ERGODIC: #{gf3[:counts][:zero]} | MINUS: #{gf3[:counts][:minus_1]}",
          "GF(3) Sum: #{gf3[:sum_mod_3]} (mod 3)",
          "Conserved: #{gf3[:conserved] ? 'YES' : 'NO'}"
        ]

        svg.add_rect(1000, 50, 140, 120, fill: "#f5f5f5", stroke: "#333", opacity: 0.9)
        stats_text.each_with_index do |text, idx|
          svg.add_text(1010, 70 + idx*20, text, font_size: 9, class_name: "axis-label")
        end
      end

      File.write(output_file, svg.elements.join("\n"))
      output_file
    end

    def self.mixing_time_curve(network, output_file)
      history = network.mixing_times[:entropy_history]
      return nil unless history

      svg = SVGBuilder.new(width: 1000, height: 600)

      # Calculate scaling
      max_round = history.size - 1
      max_entropy = 1.0
      margin = 60
      plot_width = 1000 - 2 * margin
      plot_height = 600 - 2 * margin

      svg.render do |svg|
        # Title
        svg.add_text(500, 30, "Skill Network Entropy Convergence (Mixing Time)",
                     class_name: "title", anchor: "middle")

        # Axes
        svg.add_line(margin, 600 - margin, 1000 - margin, 600 - margin, stroke: "#000", stroke_width: 2)
        svg.add_line(margin, 600 - margin, margin, margin, stroke: "#000", stroke_width: 2)

        # Axis labels
        svg.add_text(500, 580, "Round", class_name: "axis-label", anchor: "middle")
        svg.add_text(20, 300, "Entropy", class_name: "axis-label", anchor: "middle")

        # Grid lines and tick marks
        10.times do |i|
          x = margin + (i * plot_width) / 10
          y = 600 - margin
          svg.add_line(x, y, x, y + 5, stroke: "#000", stroke_width: 1)
          svg.add_text(x, y + 20, (i * max_round / 10).to_s, font_size: 9, class_name: "axis-label", anchor: "middle")
        end

        10.times do |i|
          y = 600 - margin - (i * plot_height) / 10
          x = margin
          svg.add_line(x - 5, y, x, y, stroke: "#000", stroke_width: 1)
          svg.add_text(x - 10, y + 3, (i * max_entropy / 10).round(1).to_s, font_size: 9, class_name: "axis-label", anchor: "end")
        end

        # Draw curve
        path_data = []
        history.each_with_index do |entropy, round|
          x = margin + (round.to_f / max_round) * plot_width
          y = 600 - margin - (entropy / max_entropy) * plot_height
          if round == 0
            path_data << "M #{x} #{y}"
          else
            path_data << "L #{x} #{y}"
          end
        end
        svg.add_path(path_data.join(" "), stroke: "#2E86AB", stroke_width: 2)

        # Mark mixing round if available
        if network.mixing_times[:mixing_round]
          mixing_round = network.mixing_times[:mixing_round]
          if mixing_round < history.size
            mixing_entropy = history[mixing_round]
            x = margin + (mixing_round.to_f / max_round) * plot_width
            y = 600 - margin - (mixing_entropy / max_entropy) * plot_height
            svg.add_circle(x, y, 5, fill: "#FF0000", stroke: "#000", stroke_width: 2)
            svg.add_text(x + 30, y - 10, "Mixing point (round #{mixing_round})", font_size: 10, fill: "#FF0000")
          end
        end

        # Stats box
        stats = [
          "Final entropy: #{history.last.round(4)}",
          "Mixing round: #{network.mixing_times[:mixing_round] || 'N/A'}",
          "Converged: #{network.mixing_times[:converged] ? 'YES' : 'NO'}"
        ]
        svg.add_rect(750, 50, 200, 100, fill: "#f5f5f5", stroke: "#333", opacity: 0.9)
        stats.each_with_index do |text, idx|
          svg.add_text(760, 70 + idx*20, text, font_size: 10, class_name: "axis-label")
        end
      end

      File.write(output_file, svg.elements.join("\n"))
      output_file
    end

    def self.hierarchical_skill_layout(network, output_file)
      # Group skills by bundle and trit
      bundles = network.skills.group_by { |_, s| s.bundle }

      svg = SVGBuilder.new(width: 1400, height: 900)

      svg.render do |svg|
        # Title
        svg.add_text(700, 30, "Hierarchical Skill Organization (Hackage-style)",
                     class_name: "title", anchor: "middle")

        y_pos = 100
        x_positions = {plus_1: 100, zero: 500, minus_1: 900}

        # Draw three columns for GF(3) roles
        [1, 0, -1].each do |trit|
          color = SVGBuilder.color_for_trit(trit)
          label = SVGBuilder.label_for_trit(trit)
          x = x_positions[trit == 1 ? :plus_1 : trit == 0 ? :zero : :minus_1]

          # Column header
          svg.add_rect(x - 80, y_pos - 30, 160, 30, fill: color, stroke: "#333", opacity: 0.7)
          svg.add_text(x, y_pos - 15, label, font_size: 12, class_name: "cluster-label", anchor: "middle", fill: "white")

          # List skills in this column
          col_y = y_pos + 10
          column_skills = network.skills.select { |_, s| s.trit == trit }
          column_skills.sort_by { |name, _| name }.each do |name, skill|
            svg.add_rect(x - 75, col_y, 150, 25, fill: "#fff", stroke: color, stroke_width: 1)
            svg.add_text(x - 70, col_y + 16, name[0..20], font_size: 9, class_name: "skill-label")
            col_y += 30
          end
        end

        # Statistics footer
        gf3 = network.analyze_gf3_conservation
        stats = [
          "Total skills: #{network.skills.size}",
          "GF(3) conservation: #{gf3[:conserved] ? 'VERIFIED ✓' : 'BROKEN ✗'}",
          "Distribution: #{gf3[:ratio]}"
        ]
        svg.add_rect(200, 820, 1000, 60, fill: "#f5f5f5", stroke: "#333", opacity: 0.9)
        stats.each_with_index do |text, idx|
          svg.add_text(220, 845 + idx*15, text, font_size: 11, class_name: "axis-label")
        end
      end

      File.write(output_file, svg.elements.join("\n"))
      output_file
    end
  end

  # ============================================================================
  # HACKAGE-STYLE DOCUMENTATION
  # ============================================================================

  class HackageStyleDocumentation
    def self.generate_index(network, output_dir)
      FileUtils.mkdir_p(output_dir)

      # Generate main index.html
      html = generate_index_html(network)
      File.write(File.join(output_dir, "index.html"), html)

      # Generate package pages for each skill
      network.skills.each do |name, skill|
        package_html = generate_package_html(name, skill, network)
        File.write(File.join(output_dir, "#{name}.html"), package_html)
      end

      puts "✅ Generated Hackage-style documentation in #{output_dir}"
    end

    private

    def self.generate_index_html(network)
      gf3 = network.analyze_gf3_conservation

      html = <<~HTML
        <!DOCTYPE html>
        <html>
        <head>
          <meta charset="utf-8">
          <title>Music-Topos Skill Registry</title>
          <style>
            body { font-family: Arial, sans-serif; max-width: 1200px; margin: 0 auto; padding: 20px; background: #f9f9f9; }
            h1 { color: #333; border-bottom: 3px solid #2E86AB; padding-bottom: 10px; }
            h2 { color: #555; margin-top: 30px; }
            .skill-group { margin: 20px 0; padding: 15px; background: white; border-radius: 5px; border-left: 4px solid #ccc; }
            .skill-group.plus { border-left-color: #95E1D3; }
            .skill-group.ergodic { border-left-color: #4ECDC4; }
            .skill-group.minus { border-left-color: #FF6B6B; }
            .skill-link { display: inline-block; margin: 5px 10px 5px 0; padding: 8px 12px; background: #f0f0f0; text-decoration: none; border-radius: 3px; color: #333; }
            .skill-link:hover { background: #e0e0e0; }
            .stats { background: #e8f4f8; padding: 15px; border-radius: 5px; margin: 20px 0; }
            .stats-table { width: 100%; border-collapse: collapse; }
            .stats-table td { padding: 8px; border-bottom: 1px solid #ccc; }
            .stats-table td:first-child { font-weight: bold; width: 200px; }
          </style>
        </head>
        <body>
          <h1>🎵 Music-Topos Skill Registry</h1>
          <p>Formal skill ecosystem with GF(3) conservation and mixing time analysis.</p>

          <div class="stats">
            <table class="stats-table">
              <tr><td>Total Skills:</td><td>#{network.skills.size}</td></tr>
              <tr><td>PLUS (+1) Skills:</td><td>#{gf3[:counts][:plus_1]}</td></tr>
              <tr><td>ERGODIC (0) Skills:</td><td>#{gf3[:counts][:zero]}</td></tr>
              <tr><td>MINUS (-1) Skills:</td><td>#{gf3[:counts][:minus_1]}</td></tr>
              <tr><td>GF(3) Sum (mod 3):</td><td>#{gf3[:sum_mod_3]}</td></tr>
              <tr><td>Conservation Status:</td><td>#{gf3[:conserved] ? '✓ VERIFIED' : '✗ BROKEN'}</td></tr>
              <tr><td>Average Mixing Distance:</td><td>#{network.average_mixing_distance.round(2)}</td></tr>
              <tr><td>Network Diameter:</td><td>#{network.diameter}</td></tr>
            </table>
          </div>

          <h2>📊 PLUS (+1) Skills (Generators)</h2>
          <div class="skill-group plus">
            #{network.skills.select { |_, s| s.trit == 1 }.map { |name, _| %{<a href="#{name}.html" class="skill-link">#{name}</a>} }.join("\n")}
          </div>

          <h2>⚙️  ERGODIC (0) Skills (Coordinators)</h2>
          <div class="skill-group ergodic">
            #{network.skills.select { |_, s| s.trit == 0 }.map { |name, _| %{<a href="#{name}.html" class="skill-link">#{name}</a>} }.join("\n")}
          </div>

          <h2>🔍 MINUS (-1) Skills (Validators)</h2>
          <div class="skill-group minus">
            #{network.skills.select { |_, s| s.trit == -1 }.map { |name, _| %{<a href="#{name}.html" class="skill-link">#{name}</a>} }.join("\n")}
          </div>
        </body>
        </html>
      HTML

      html
    end

    def self.generate_package_html(name, skill, network)
      deps_html = if skill.dependencies.any?
                    "<ul>" + skill.dependencies.map { |d| %{<li><a href="#{d}.html">#{d}</a></li>} }.join + "</ul>"
                  else
                    "<p><em>No dependencies</em></p>"
                  end

      reverse_deps = network.skills.select { |_, s| s.depends_on?(name) }.keys
      reverse_deps_html = if reverse_deps.any?
                            "<ul>" + reverse_deps.map { |d| %{<li><a href="#{d}.html">#{d}</a></li>} }.join + "</ul>"
                          else
                            "<p><em>None</em></p>"
                          end

      color = case skill.trit
              when 1
                "#95E1D3"
              when 0
                "#4ECDC4"
              when -1
                "#FF6B6B"
              else
                "#ccc"
              end

      html = <<~HTML
        <!DOCTYPE html>
        <html>
        <head>
          <meta charset="utf-8">
          <title>#{name} - Music-Topos Skill</title>
          <style>
            body { font-family: Arial, sans-serif; max-width: 900px; margin: 0 auto; padding: 20px; background: #f9f9f9; }
            .header { background: #{color}; color: white; padding: 20px; border-radius: 5px; margin-bottom: 20px; }
            .header h1 { margin: 0; }
            .meta { background: white; padding: 15px; border-radius: 5px; margin-bottom: 20px; border-left: 4px solid #{color}; }
            .meta-row { display: flex; margin: 10px 0; }
            .meta-row strong { width: 150px; }
            h2 { color: #333; border-bottom: 2px solid #{color}; padding-bottom: 10px; margin-top: 30px; }
            a { color: #{color}; text-decoration: none; }
            a:hover { text-decoration: underline; }
            ul { margin: 10px 0; padding-left: 20px; }
            li { margin: 5px 0; }
            .back-link { margin-bottom: 20px; }
          </style>
        </head>
        <body>
          <div class="back-link">
            <a href="index.html">← Back to Registry</a>
          </div>

          <div class="header">
            <h1>#{name}</h1>
            <p>GF(3) Role: <strong>#{SVGBuilder.label_for_trit(skill.trit)}</strong></p>
          </div>

          <div class="meta">
            <div class="meta-row"><strong>Version:</strong> #{skill.version}</div>
            <div class="meta-row"><strong>Bundle:</strong> #{skill.bundle}</div>
            <div class="meta-row"><strong>Trit (GF(3)):</strong> #{skill.trit}</div>
            <div class="meta-row"><strong>Last Modified:</strong> #{skill.date.strftime('%Y-%m-%d %H:%M:%S')}</div>
            <div class="meta-row"><strong>Logical Clock:</strong> #{skill.clock.now}</div>
          </div>

          <h2>Dependencies</h2>
          #{deps_html}

          <h2>Reverse Dependencies</h2>
          #{reverse_deps_html}

          <p style="margin-top: 40px; color: #999; font-size: 12px;">
            Generated by Music-Topos Skill Mixing Analysis | #{Time.now.strftime('%Y-%m-%d %H:%M:%S')}
          </p>
        </body>
        </html>
      HTML

      html
    end
  end
end

# ============================================================================
# DEMO: Generate visualizations
# ============================================================================

if __FILE__ == $0
  puts "🎨 Generating skill network diagrams..."

  # Load skills
  music_topos_dir = "/Users/bob/ies/music-topos"
  network = SkillMixingAnalysis::SkillLoader.load_from_directory(music_topos_dir)

  puts "✅ Loaded #{network.skills.size} skills"

  # Measure mixing time
  puts "📈 Measuring mixing times..."
  network.measure_mixing_time(max_rounds: 100)

  # Generate diagrams
  output_dir = "#{music_topos_dir}/diagrams"
  FileUtils.mkdir_p(output_dir)

  puts "🎨 Generating dependency graph..."
  SkillDiagramVisualization::SkillNetworkDiagram.dependency_graph(
    network,
    "#{output_dir}/skill_dependency_graph.svg"
  )

  puts "📊 Generating entropy convergence curve..."
  SkillDiagramVisualization::SkillNetworkDiagram.mixing_time_curve(
    network,
    "#{output_dir}/entropy_convergence.svg"
  )

  puts "🏛️  Generating hierarchical layout..."
  SkillDiagramVisualization::SkillNetworkDiagram.hierarchical_skill_layout(
    network,
    "#{output_dir}/hierarchical_skills.svg"
  )

  puts "📚 Generating Hackage-style documentation..."
  SkillDiagramVisualization::HackageStyleDocumentation.generate_index(
    network,
    "#{output_dir}/hackage-registry"
  )

  puts "\n✅ All diagrams generated in #{output_dir}/"
  puts "   - skill_dependency_graph.svg"
  puts "   - entropy_convergence.svg"
  puts "   - hierarchical_skills.svg"
  puts "   - hackage-registry/ (HTML)"
end
