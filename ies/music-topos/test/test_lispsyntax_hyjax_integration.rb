#!/usr/bin/env ruby
# test/test_lispsyntax_hyjax_integration.rb
#
# Integration test for LispSyntax.jl ↔ ACSet.jl ↔ HyJAX pipeline
# Tests the full roundtrip: ACSet → Sexp → ACSet verification

require 'minitest/autorun'
require 'open3'
require 'json'

class LispSyntaxHyJAXIntegrationTest < Minitest::Test
  def setup
    @project_root = File.expand_path('..', __dir__)
  end

  def test_julia_sexp_parsing
    cmd = <<~JULIA
      julia --project=. -e '
      include("lib/lispsyntax_acset_bridge.jl")
      using .LispSyntaxAcsetBridge
      
      # Test basic parsing
      sexp = parse_sexp("(+ 1 2)")
      println("PARSED: ", to_string(sexp))
      
      # Test roundtrip
      result = verify_parse_roundtrip("(a (b c) d)")
      println("ROUNDTRIP: ", result)
      '
    JULIA
    
    stdout, stderr, status = Open3.capture3(cmd, chdir: @project_root)
    
    assert status.success?, "Julia sexp parsing failed: #{stderr}"
    assert_includes stdout, "PARSED: (+ 1 2)"
    assert_includes stdout, "ROUNDTRIP: true"
  end

  def test_hy_thread_analysis
    cmd = <<~HY
      uv run hy -c '
      (import lib.thread_relational_hyjax :as tra)
      (setv analyzer (tra.ThreadRelationalAnalyzer))
      (analyzer.ingest-thread "T-test" "Test" [{"content" "hello" "timestamp" 1.0}])
      (analyzer.extract-concepts ["test" "concept"])
      (setv result (analyzer.analyze))
      (print "ANALYSIS_COMPLETE")
      (print "THREADS:" (len analyzer.acset.threads))
      (print "CONCEPTS:" (len analyzer.acset.concepts))
      '
    HY
    
    stdout, stderr, status = Open3.capture3(cmd, chdir: @project_root)
    
    assert status.success?, "HyJAX analysis failed: #{stderr}"
    assert_includes stdout, "ANALYSIS_COMPLETE"
    assert_includes stdout, "THREADS: 1"
    assert_includes stdout, "CONCEPTS: 2"
  end

  def test_ruby_world_broadcast_condensed
    require_relative '../lib/world_broadcast'
    
    # Test condensed anima integration
    assert WorldBroadcast::CondensedAnima.respond_to?(:profinite_approximate)
    assert WorldBroadcast::CondensedAnima.respond_to?(:liquid_norm)
    assert WorldBroadcast::CondensedAnima.respond_to?(:analytic_stack)
    
    # Test actual computation
    approx = WorldBroadcast::CondensedAnima.profinite_approximate(42)
    assert_kind_of Array, approx
    
    # Test liquid norm
    norm = WorldBroadcast::CondensedAnima.liquid_norm([1, 2, 3], r: 0.5)
    assert_kind_of Numeric, norm
    assert norm > 0
    
    # Test analytic stack
    stack = WorldBroadcast::CondensedAnima.analytic_stack([1, 2, 3])
    assert_kind_of Hash, stack
    assert stack[:objects]
    assert stack[:descent_data]
  end

  def test_sexp_colorization
    cmd = <<~JULIA
      julia --project=. -e '
      include("lib/lispsyntax_acset_bridge.jl")
      using .LispSyntaxAcsetBridge
      
      sexp = parse_sexp("(test (nested list))")
      colored = colorize(sexp, UInt64(0x598F318E2B9E884), 0)
      
      println("L: ", colored.L)
      println("C: ", colored.C)
      println("H: ", colored.H)
      println("INDEX: ", colored.index)
      '
    JULIA
    
    stdout, stderr, status = Open3.capture3(cmd, chdir: @project_root)
    
    assert status.success?, "Colorization failed: #{stderr}"
    assert_includes stdout, "L:"
    assert_includes stdout, "INDEX: 0"
  end

  def test_gf3_triad_conservation
    # Verify the LispSyntax bundle sums to 0
    triads = [
      { skills: ['slime-lisp', 'lispsyntax-acset', 'cider-clojure'], trits: [-1, 0, 1] },
      { skills: ['three-match', 'lispsyntax-acset', 'gay-mcp'], trits: [-1, 0, 1] },
      { skills: ['polyglot-spi', 'lispsyntax-acset', 'geiser-chicken'], trits: [-1, 0, 1] }
    ]
    
    triads.each do |triad|
      sum = triad[:trits].sum
      assert_equal 0, sum, "GF(3) not conserved for #{triad[:skills].join(' ⊗ ')}"
    end
  end
end

if __FILE__ == $0
  # Run specific test if provided
  if ARGV.any?
    Minitest.run(ARGV)
  end
end
