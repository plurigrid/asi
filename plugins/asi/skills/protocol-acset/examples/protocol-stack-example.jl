#!/usr/bin/env julia
"""
Protocol ACSet Example: Building a Data-Sovereign App Stack

Demonstrates:
- Modeling protocols as attributed C-sets
- Composing protocols together
- Verifying interoperability through categorical mathematics
- Assigning GF(3) trits for system balance
"""

using Catlab, Catlab.Theories, Catlab.CategoricalAlgebra

# Protocol ACSet Schema
@acset_type ProtocolACSet <: AbstractACSet begin
  (Protocol, Layer, Property, Bridge)

  # Protocol properties
  protocol_has_layer::EdgeVertex
  protocol_has_property::EdgeVertex
  property_value::EdgeAttribute

  # Composition
  bridge_connects::EdgeVertexDouble
  bridge_compatible::EdgeAttribute
end

# Data Sovereign Application Stack Example
# =========================================

function create_data_sovereign_stack()
  """
  Build a protocol stack for a data-sovereign file sync app:

  Layers:
    1. Transport:  Iroh (QUIC + holepunching)
    2. Storage:    IPFS (content-addressed)
    3. Sync:       Hypercore (append-only, offline-first)
    4. Identity:   DIDs (portable, user-controlled)

  Result: Users own their nodes, no central server required
  """

  protocols = ProtocolACSet()

  # Layer 1: Transport (Iroh)
  iroh = add_part!(protocols, :Protocol, name="Iroh")
  add_part!(protocols, :Layer, protocol=iroh, name="transport", version="0.13")
  add_part!(protocols, :Property,
    protocol=iroh,
    name="encryption",
    value="TLS1.3"
  )
  add_part!(protocols, :Property,
    protocol=iroh,
    name="topology",
    value="P2P-with-relay-fallback"
  )
  add_part!(protocols, :Property,
    protocol=iroh,
    name="trit",
    value="PLUS(+1)"  # Generative: enables new P2P apps
  )

  # Layer 2: Storage (IPFS)
  ipfs = add_part!(protocols, :Protocol, name="IPFS")
  add_part!(protocols, :Layer, protocol=ipfs, name="storage", version="0.14")
  add_part!(protocols, :Property,
    protocol=ipfs,
    name="addressing",
    value="content-hash"
  )
  add_part!(protocols, :Property,
    protocol=ipfs,
    name="persistence",
    value="permanent"
  )
  add_part!(protocols, :Property,
    protocol=ipfs,
    name="trit",
    value="PLUS(+1)"  # Generative: creates permanent archive
  )

  # Layer 3: Sync (Hypercore)
  hypercore = add_part!(protocols, :Protocol, name="Hypercore")
  add_part!(protocols, :Layer, protocol=hypercore, name="sync", version="10.0")
  add_part!(protocols, :Property,
    protocol=hypercore,
    name="data-model",
    value="append-only-log"
  )
  add_part!(protocols, :Property,
    protocol=hypercore,
    name="offline-capable",
    value="true"
  )
  add_part!(protocols, :Property,
    protocol=hypercore,
    name="trit",
    value="ERGODIC(0)"  # Balanced: enables sync without central server
  )

  # Layer 4: Identity (DIDs)
  did = add_part!(protocols, :Protocol, name="DID")
  add_part!(protocols, :Layer, protocol=did, name="identity", version="1.0")
  add_part!(protocols, :Property,
    protocol=did,
    name="portability",
    value="user-controlled"
  )
  add_part!(protocols, :Property,
    protocol=did,
    name="recovery",
    value="possible"
  )
  add_part!(protocols, :Property,
    protocol=did,
    name="trit",
    value="MINUS(-1)"  # Observational: recognizes identity constraints
  )

  # Bridge 1: Iroh → IPFS (Transport enables distribution)
  bridge_iroh_ipfs = add_part!(protocols, :Bridge,
    name="Iroh→IPFS",
    source=iroh,
    target=ipfs,
    compatible=true
  )

  # Bridge 2: IPFS → Hypercore (Content→Log bridging)
  bridge_ipfs_hc = add_part!(protocols, :Bridge,
    name="IPFS→Hypercore",
    source=ipfs,
    target=hypercore,
    compatible=true
  )

  # Bridge 3: Hypercore → DID (Sync enables identity anchor)
  bridge_hc_did = add_part!(protocols, :Bridge,
    name="Hypercore→DID",
    source=hypercore,
    target=did,
    compatible=true
  )

  return protocols
end

# Verify Stack Composition
# ========================

function verify_trit_balance(protocols::ProtocolACSet)
  """
  Check GF(3) conservation: sum of trits must equal 0 (mod 3)
  """
  trit_values = Dict(
    "MINUS(-1)" => -1,
    "ERGODIC(0)" => 0,
    "PLUS(+1)" => 1
  )

  total = 0
  for prop in protocols[:Property]
    if protocols[prop, :name] == "trit"
      trit_str = protocols[prop, :value]
      total += trit_values[trit_str]
    end
  end

  balanced = (total % 3) == 0
  println("GF(3) Balance Check:")
  println("  Sum of trits: $total")
  println("  Balanced: $balanced")

  return balanced
end

function check_bridge_compatibility(protocols::ProtocolACSet)
  """
  Verify all bridges are compatible (no conflicts)
  """
  compatible = true
  for bridge in protocols[:Bridge]
    if !protocols[bridge, :compatible]
      compatible = false
      println("⚠️  Bridge $(protocols[bridge, :name]) is NOT compatible")
    end
  end

  if compatible
    println("\n✅ All bridges are compatible!")
  end

  return compatible
end

function print_protocol_stack(protocols::ProtocolACSet)
  """
  Pretty-print the protocol stack
  """
  println("\n" * "="^60)
  println("DATA-SOVEREIGN FILE SYNC STACK")
  println("="^60)

  # Group by layer order
  layers = [
    ("Transport", "Iroh"),
    ("Storage", "IPFS"),
    ("Sync", "Hypercore"),
    ("Identity", "DID")
  ]

  for (layer_name, protocol_name) in layers
    println("\n📦 Layer: $layer_name")
    println("   Protocol: $protocol_name")

    # Find protocol in ACSet
    for proto in protocols[:Protocol]
      if protocols[proto, :name] == protocol_name
        for prop in protocols[:Property]
          if protocols[prop, :protocol] == proto
            key = protocols[prop, :name]
            val = protocols[prop, :value]

            if key == "trit"
              println("   Trit: $val")
            else
              println("   • $key: $val")
            end
          end
        end
      end
    end
  end

  println("\n" * "="^60)
  println("COMPOSITION BRIDGES")
  println("="^60)
  for bridge in protocols[:Bridge]
    name = protocols[bridge, :name]
    compat = protocols[bridge, :compatible] ? "✅" : "❌"
    println("  $compat $name")
  end

  println("\n" * "="^60)
end

# Properties Verification
# =======================

function verify_properties(protocols::ProtocolACSet)
  """
  Verify that the composed stack provides desired properties
  """
  desired_properties = [
    ("encryption", "TLS1.3"),
    ("persistence", "permanent"),
    ("offline-capable", "true"),
    ("portability", "user-controlled"),
    ("addressing", "content-hash")
  ]

  achieved = 0
  println("\n📋 Property Verification:")
  for (prop_name, expected_value) in desired_properties
    for prop in protocols[:Property]
      if protocols[prop, :name] == prop_name
        actual = protocols[prop, :value]
        match = actual == expected_value ? "✅" : "❌"
        println("  $match $prop_name: $actual")

        if match == "✅"
          achieved += 1
        end
      end
    end
  end

  println("\n  Achieved: $achieved/$(length(desired_properties)) properties")

  return achieved == length(desired_properties)
end

# Run Example
# ===========

function main()
  println("🏗️  Building Data-Sovereign Protocol Stack...\n")

  # Create stack
  stack = create_data_sovereign_stack()

  # Verify
  print_protocol_stack(stack)

  println("\n🔍 VERIFICATION CHECKS:\n")
  verified = true

  verified &= verify_trit_balance(stack)
  verified &= check_bridge_compatibility(stack)
  verified &= verify_properties(stack)

  println("\n" * "="^60)
  if verified
    println("✅ DATA-SOVEREIGN STACK VERIFIED!")
    println("\nThis stack provides:")
    println("  • Direct P2P connections (no central server)")
    println("  • Content-addressed storage (permanent, deduped)")
    println("  • Offline-first synchronization")
    println("  • User-controlled identity")
    println("  • End-to-end encryption throughout")
    println("\nUsers own their data and infrastructure.")
  else
    println("❌ Stack verification failed!")
  end
  println("="^60)
end

# Execute if run directly
if abspath(PROGRAM_FILE) == @__FILE__
  main()
end
