---
name: nix-acset-worlding
description: Model Nix store as Attributed C-Set for dependency verification, GC analysis,
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Nix ACSet Worlding Skill

> **Trit**: -1 (MINUS) - Constraint verification of Nix store semantics

Model Nix store as Attributed C-Set for dependency verification and world management.

## Schema

```julia
@present SchNixStore(FreeSchema) begin
    (Path, Hash, Name, Type, World)::Ob
    
    path_hash::Hom(Path, Hash)
    path_name::Hom(Path, Name)  
    path_type::Hom(Path, Type)
    depends_on::Hom(Path, Path)
    belongs_to::Hom(Path, World)
    
    hash_value::Attr(Hash, String)      # 32-char base32
    name_value::Attr(Name, String)
    type_value::Attr(Type, Symbol)      # :drv, :out, :source, :patch
    world_name::Attr(World, String)
    size_bytes::Attr(Path, Int)
    is_dead::Attr(Path, Bool)
end
```

## Core Operations

### 1. GC Root Analysis

```julia
function live_roots(store::NixStoreACSet)
    filter(p -> !store[:is_dead][p], parts(store, :Path))
end

function dead_paths(store::NixStoreACSet)
    filter(p -> store[:is_dead][p], parts(store, :Path))
end
```

### 2. World Management

Flox environments as categorical worlds:
```
World := {name, dev_env, run_env, manifest}
```

Live worlds (2024-12-24):
- `music-topos` - Audio/visual synthesis
- `stellogen` - Stellar generators
- `bevy_fullscreen_app` - Rust game engine
- `cubical-agda` - HoTT proof assistant

### 3. Dependency Sheaf

Dependencies form a sheaf over the store graph:
```julia
function dependency_sheaf(store::NixStoreACSet)
    # Check transitive closure consistency
    for p in parts(store, :Path)
        deps = store[:depends_on][p]
        for d in deps
            @assert haspart(store, :Path, d)
        end
    end
end
```

## Integration with Gay.jl

### Hash → Color Mapping

```julia
function hash_to_color(hash::String)
    seed = parse(UInt64, hash[1:16], base=32)
    gay_color(seed ⊻ GAY_SEED)
end
```

### GC Statistics (2024-12-24 Snapshot)

| Metric | Value |
|--------|-------|
| Dead paths | 299 |
| Reclaimable | 3.9 GB |
| Live roots | 17 |
| Worlds pruned | 5 |

## Triadi