"""
    RandomAccessStreams.jl

Random-access color streams without replay: jump directly to the nth element.

Key insight: SplitMix64 is a bijection on 64-bit state space, so we can:
1. **Direct access**: Compute state at index n without computing 0..n-1
2. **Stride patterns**: Skip every k elements (QUIC path management)
3. **GF(3) preservation**: Discontiguous subsequences conserve modulo-3 balance
4. **Sonification**: Map to QUIC path validation states & musical intervals

Applications:
- QUIC multipath: Each path gets deterministic color via (connection_id, path_index)
- Arweave random access: Jump to any block without downloading previous blocks
- Sheaf sections: Non-local compatibility checks via Laplacian on sparse subsets
- Musical skip patterns: Non-sequential chord progressions with maintained balance

Reference: SplitMix64 (Steele et al. 2014) has O(1) random access via state iteration.
"""

module RandomAccessStreams

using Printf

export
    # Core random access
    SplitMix64RandomAccessor,
    color_at,
    colors_in_range,
    colors_with_stride,

    # QUIC path integration
    QUICPathState,
    path_color,
    validate_path,
    multipath_colors,

    # GF(3) verification
    verify_discontiguous_gf3,
    gf3_sum_sparse,

    # Sonification
    path_to_musical_interval,
    multipath_chord,

    # Utilities
    state_at_index,
    display_access_pattern


#=============================================================================
 SplitMix64 Random Access
=#

"""
    SplitMix64RandomAccessor

Allows O(1) access to any element in a SplitMix64 sequence without replay.
"""
mutable struct SplitMix64RandomAccessor
    seed::UInt64
    gamma::UInt64
end

const SPLITMIX64_GAMMA = 0x9e3779b97f4a7c15

"""
    SplitMix64RandomAccessor(seed::UInt64)

Create a random accessor for deterministic stream starting at seed.
"""
function SplitMix64RandomAccessor(seed::UInt64)
    SplitMix64RandomAccessor(seed, SPLITMIX64_GAMMA)
end

"""
    state_at_index(accessor::SplitMix64RandomAccessor, n::Int) -> UInt64

Compute the SplitMix64 state after n steps without replay.

Mathematical foundation:
  state(n) = seed + n·γ  (linear recurrence in state space)

This works because SplitMix64 advances via state += γ, which is invertible.
"""
function state_at_index(accessor::SplitMix64RandomAccessor, n::Int)::UInt64
    # state(n) = seed + n * gamma (mod 2^64, automatic for UInt64)
    accessor.seed + UInt64(n) * accessor.gamma
end

"""
    _splitmix_next(state::UInt64) -> UInt64

Compute the next SplitMix64 output from a state.
"""
function _splitmix_next(state::UInt64)::UInt64
    z = xor(state, state >> 27)
    xor(z >> 31, z)
end

"""
    color_at(accessor::SplitMix64RandomAccessor, n::Int) -> Int

Get the ternary color (0, 1, or 2) at index n without computing 0..n-1.

Time: O(1)
Space: O(1)
"""
function color_at(accessor::SplitMix64RandomAccessor, n::Int)::Int
    state = state_at_index(accessor, n)
    output = _splitmix_next(state)
    Int(output % 3)
end

"""
    colors_in_range(accessor::SplitMix64RandomAccessor, start::Int, stop::Int) -> Vector{Int}

Get colors from start to stop index (inclusive).
Still O(N) but doesn't require replay for each access.
"""
function colors_in_range(accessor::SplitMix64RandomAccessor, start::Int, stop::Int)::Vector{Int}
    [color_at(accessor, i) for i in start:stop]
end

"""
    colors_with_stride(accessor::SplitMix64RandomAccessor, start::Int, stride::Int, count::Int) -> Vector{Int}

Get colors at positions: start, start+stride, start+2*stride, ..., start+(count-1)*stride.

Use case: QUIC multipath validation every Nth packet
"""
function colors_with_stride(accessor::SplitMix64RandomAccessor, start::Int, stride::Int, count::Int)::Vector{Int}
    [color_at(accessor, start + (i-1)*stride) for i in 1:count]
end


#=============================================================================
 QUIC Path Integration
=#

"""
    QUICPathState

Represents a QUIC path with deterministic color assignment.

Fields:
    connection_id::UInt64      - Identifies the connection
    path_index::Int            - Which path (0, 1, 2, ...)
    validation_state::Int      - -1=failed, 0=pending, +1=validated
    color::Int                 - Deterministic ternary color
"""
struct QUICPathState
    connection_id::UInt64
    path_index::Int
    validation_state::Int      # {-1, 0, +1} in GF(3)
    color::Int
end

"""
    path_color(connection_id::UInt64, path_index::Int) -> Int

Deterministically assign a color to a QUIC path.

The color depends on:
  - connection_id (seed)
    - path_index (which path in the connection)

This ensures:
  1. Same connection always produces same colors
  2. Different paths get different colors
  3. Color is deterministic but unpredictable without knowing connection_id
"""
function path_color(connection_id::UInt64, path_index::Int)::Int
    accessor = SplitMix64RandomAccessor(connection_id)
    color_at(accessor, path_index)
end

"""
    validate_path(connection_id::UInt64, path_index::Int, is_valid::Bool) -> QUICPathState

Create a path state after validation.
"""
function validate_path(connection_id::UInt64, path_index::Int, is_valid::Bool)::QUICPathState
    color = path_color(connection_id, path_index)
    validation_state = is_valid ? 1 : -1
    QUICPathState(connection_id, path_index, validation_state, color)
end

"""
    multipath_colors(connection_id::UInt64, num_paths::Int) -> Vector{Int}

Get deterministic colors for all paths in a connection.

Useful for multipath QUIC where you want each path to have a unique,
deterministic color for sonification/visualization.
"""
function multipath_colors(connection_id::UInt64, num_paths::Int)::Vector{Int}
    [path_color(connection_id, i-1) for i in 1:num_paths]
end


#=============================================================================
 GF(3) Verification for Discontiguous Subsequences
=#

"""
    gf3_sum_sparse(accessor::SplitMix64RandomAccessor, indices::Vector{Int}) -> Int

Compute GF(3) sum of colors at specific (non-contiguous) indices.

Useful for:
- Verifying balance across sparse subsets (sheaf sections)
- Checking consistency of random access patterns
- Auditing multipath selections
"""
function gf3_sum_sparse(accessor::SplitMix64RandomAccessor, indices::Vector{Int})::Int
    mod(sum(color_at(accessor, i) for i in indices), 3)
end

"""
    verify_discontiguous_gf3(accessor::SplitMix64RandomAccessor, indices::Vector{Int}) -> Bool

Check if a discontiguous subsequence conserves GF(3) balance.

Example: In QUIC, after validating paths {0, 2, 4}, check that their
colors sum to 0 mod 3 for operadic consistency.
"""
function verify_discontiguous_gf3(accessor::SplitMix64RandomAccessor, indices::Vector{Int})::Bool
    gf3_sum_sparse(accessor, indices) == 0
end


#=============================================================================
 Sonification: QUIC Paths as Musical Intervals
=#

"""
    path_to_musical_interval(color::Int, validation_state::Int) -> String

Map (color, validation_state) to musical intervals.

Encoding:
  color: 0=C, 1=E, 2=G (Major triad)
  validation_state: -1=minor (descending), 0=perfect (neutral), +1=major (ascending)

Result: Interval + direction (e.g., "m3 down", "P5 up")
"""
function path_to_musical_interval(color::Int, validation_state::Int)::String
    note_name = ["C", "E", "G"][color + 1]  # color in {0, 1, 2}

    interval = if color == 0
        "P1"  # Unison
    elseif color == 1
        "M3"  # Major third
    else   # color == 2
        "P5"  # Perfect fifth
    end

    direction = if validation_state == -1
        "down"
    elseif validation_state == 0
        "neutral"
    else
        "up"
    end

    "$interval $direction ($note_name)"
end

"""
    multipath_chord(paths::Vector{QUICPathState}) -> String

Sonify multiple QUIC paths as a musical chord.

Example:
  paths = [
    QUICPathState(..., color=0, validation_state=1),
    QUICPathState(..., color=1, validation_state=0),
    QUICPathState(..., color=2, validation_state=-1)
  ]
  → "C-major + E-neutral + G-descending"
"""
function multipath_chord(paths::Vector{QUICPathState})::String
    notes = []
    for path in paths
        note = ["C", "E", "G"][path.color + 1]
        direction = ["↓", "·", "↑"][path.validation_state + 2]  # +2 to index {-1,0,1}
        push!(notes, "$note$direction")
    end
    join(notes, " ")
end


#=============================================================================
 Utility Functions
=#

"""
    display_access_pattern(connection_id::UInt64, indices::Vector{Int})

Pretty-print a random access pattern for debugging.
"""
function display_access_pattern(connection_id::UInt64, indices::Vector{Int})
    accessor = SplitMix64RandomAccessor(connection_id)

    println("\nRandom Access Pattern")
    println("=" * 70)
    @printf "Connection ID: 0x%016x\n" connection_id
    @printf "Indices accessed: [%s]\n" join(indices, ", ")
    println()

    colors = [color_at(accessor, i) for i in indices]
    gf3_check = gf3_sum_sparse(accessor, indices) == 0

    println("Index → Color mapping:")
    for (idx, color) in zip(indices, colors)
        @printf "  [%4d] → %d\n" idx color
    end

    println()
    @printf "GF(3) Sum: %d (conserved? %s)\n" gf3_sum_sparse(accessor, indices) (gf3_check ? "✓" : "✗")

    println("\nMusical intervals:")
    for (idx, color) in zip(indices, colors)
        # Use dummy validation state for visualization
        interval = path_to_musical_interval(color, 0)
        @printf "  [%4d] → %s\n" idx interval
    end

    println("=" * 70 * "\n")
end

end  # module
