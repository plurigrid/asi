module gay_move::gay_colors {
    /// SplitMix64 constants - isomorphic to Gay.jl
    const GAMMA: u64 = 0x9e3779b97f4a7c15;
    const MIX1: u64 = 0xbf58476d1ce4e5b9;
    const MIX2: u64 = 0x94d049bb133111eb;

    struct GayColor has copy, drop, store {
        r: u8,
        g: u8,
        b: u8,
    }

    /// Helper for wrapping multiplication (u64 * u64 -> u64)
    fun wrapping_mul(a: u64, b: u64): u64 {
        let res = (a as u128) * (b as u128);
        let truncated = res & 0xFFFFFFFFFFFFFFFF;
        (truncated as u64)
    }

    /// Core SplitMix64 algorithm
    /// Matches Julia/C implementation with wrapping arithmetic
    public fun splitmix64(x: u64): u64 {
        let z = x ^ (x >> 30);
        z = wrapping_mul(z, MIX1);
        z = z ^ (z >> 27);
        z = wrapping_mul(z, MIX2);
        z = z ^ (z >> 31);
        z
    }

    /// Generate deterministic RGB color from seed and index
    /// Matches Gay.jl's hash_color implementation
    public fun hash_color(seed: u64, index: u64): GayColor {
        let mixed_index = wrapping_mul(index, GAMMA);
        let input = seed ^ mixed_index;
        let h = splitmix64(input);
        
        let r = (h & 0xFF) as u8;
        let g = ((h >> 8) & 0xFF) as u8;
        let b = ((h >> 16) & 0xFF) as u8;
        
        GayColor { r, g, b }
    }

    /// Get r, g, b values from GayColor
    public fun get_rgb(color: &GayColor): (u8, u8, u8) {
        (color.r, color.g, color.b)
    }

    /// Compute XOR fingerprint for SPI verification
    public fun xor_fingerprint(colors: &vector<GayColor>): u64 {
        let fp: u64 = 0;
        let i = 0;
        let len = std::vector::length(colors);
        while (i < len) {
            let c = std::vector::borrow(colors, i);
            let color_bits = ((c.r as u64) << 16) | ((c.g as u64) << 8) | (c.b as u64);
            fp = fp ^ color_bits;
            i = i + 1;
        };
        fp
    }

    #[test_only]
    public fun hash_color_test_helper(seed: u64, index: u64): (u8, u8, u8) {
        let c = hash_color(seed, index);
        get_rgb(&c)
    }
}
