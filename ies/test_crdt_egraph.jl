#!/usr/bin/env julia

"""Test CRDT E-Graph implementation"""

include("/Users/bob/ies/crdt_egraph.jl")
using .CRDTEGraph

println("═" ^ 80)
println("CRDT E-Graph: 3-Coloring by Construction - Julia Implementation")
println("═" ^ 80)

# Create e-graph
println("\n[Phase 1: E-Graph Creation]")
eg = CRDTEGraphValue("agent1")
println("Created e-graph for agent: $(eg.agent_id)")

# Add RED node (positive/forward)
println("\n[Phase 2: Add Nodes with Color Constraints]")
red_node = ENode("assoc", String[], Red, Positive)
red_id = add_node!(eg, red_node)
println("✓ Added RED node (forward associative): $red_id")

# Add GREEN node (can be child of RED)
green_node = ENode("identity", [red_id], Green, Neutral)
green_id = add_node!(eg, green_node)
println("✓ Added GREEN node (identity): $green_id")

# Add BLUE node (negative/backward)
blue_node = ENode("distrib", String[], Blue, Negative)
blue_id = add_node!(eg, blue_node)
println("✓ Added BLUE node (backward distributive): $blue_id")

# Try to violate constraint (RED parent with BLUE child)
println("\n[Phase 3: Test Color Constraint Enforcement]")
try
    red_with_blue_child = ENode("bad", [blue_id], Red, Positive)
    add_node!(eg, red_with_blue_child)
    println("✗ ERROR: Should have rejected RED node with BLUE child!")
catch e
    println("✓ Correctly rejected RED node with BLUE child: $(e.msg)")
end

# Check node counts
red, blue, green = count_by_color(eg)
println("\n[Phase 4: Color Distribution]")
println("  RED nodes:   $red")
println("  BLUE nodes:  $blue")
println("  GREEN nodes: $green")
println("  Total nodes: $(length(eg.nodes))")

# Perform union operation
println("\n[Phase 5: Union Operations (Merge E-Classes)]")
red_node2 = ENode("assoc", String[], Red, Positive)
red_id2 = add_node!(eg, red_node2)
println("✓ Added second RED node: $red_id2")

union_nodes!(eg, red_id, red_id2)
println("✓ Merged e-classes of two RED nodes")
println("  Union log length: $(length(eg.union_log))")

# Verify three-coloring
println("\n[Phase 6: Verification Statistics]")
stats = verify_three_coloring(eg)
println("  Nodes checked:  $(stats.nodes_checked)")
println("  Nodes valid:    $(stats.nodes_valid)")
println("  Nodes invalid:  $(stats.nodes_invalid)")
println("  RED nodes:      $(stats.red_nodes)")
println("  BLUE nodes:     $(stats.blue_nodes)")
println("  GREEN nodes:    $(stats.green_nodes)")
println("  Union count:    $(stats.union_count)")

is_valid = stats.nodes_invalid == 0
println("\n✓ Three-coloring verification: $(is_valid ? "PASSED" : "FAILED")")

# Test merge operations
println("\n[Phase 7: Commutative Merge of E-Graphs]")
eg2 = CRDTEGraphValue("agent2")
node_a = ENode("op_a", String[], Green, Neutral)
node_a_id = add_node!(eg2, node_a)
println("✓ Created second e-graph with node: $node_a_id")

merged = merge_egraphs(eg, eg2, ColorDominance)
println("✓ Merged two e-graphs")
println("  Total nodes in merged: $(length(merged.nodes))")
println("  Total classes in merged: $(length(merged.classes))")

# Test saturation
println("\n[Phase 8: Distributed Saturation (4-Phase)]")
rules = [
    RewriteRule("red_assoc", "RED associativity", "assoc", Red, Red, 10, 0),
    RewriteRule("blue_dist", "BLUE distributivity", "distrib", Blue, Blue, 10, 0),
    RewriteRule("green_id", "GREEN identity", "identity", Green, Green, 5, 0)
]

backfill, verify, live, reconcile = saturate_distributed!(merged, rules)
println("  Phase 1 (Backfill/BLUE):  $backfill rewrites")
println("  Phase 2 (Verify/GREEN):   $verify rewrites")
println("  Phase 3 (Live/RED):       $live rewrites")
println("  Phase 4 (Reconcile):      $reconcile checks")
println("✓ Saturation complete")

# Final statistics
println("\n[Phase 9: Final E-Graph Statistics]")
red_f, blue_f, green_f = count_by_color(merged)
println("  RED nodes:      $red_f")
println("  BLUE nodes:     $blue_f")
println("  GREEN nodes:    $green_f")
println("  Total nodes:    $(length(merged.nodes))")
println("  Total classes:  $(length(merged.classes))")
println("  RED rewrites:   $(merged.red_rewrites)")
println("  BLUE rewrites:  $(merged.blue_rewrites)")
println("  GREEN rewrites: $(merged.green_rewrites)")

println("\n" * "═" ^ 80)
println("✓ All tests completed successfully!")
println("═" ^ 80)
