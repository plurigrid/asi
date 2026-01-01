/// GF(3) Skill Triplet Generator with Aptos Mainnet Randomness
/// 
/// Generates valid skill triplets (MINUS ⊗ ERGODIC ⊗ PLUS = 0) using
/// Aptos on-chain randomness API.
///
/// Modes:
/// - With replacement: same skill can appear in multiple triplets
/// - Without replacement: each skill used at most once
/// - With coloring: use interaction entropy as seed for deterministic colors
/// - Without coloring: pure random selection
///
/// Reference: https://aptos.dev/build/smart-contracts/randomness
module plurigrid::triplet_generator {
    use std::vector;
    use std::option::{Self, Option};
    use aptos_framework::randomness;
    
    /// Error codes
    const E_INSUFFICIENT_SKILLS: u64 = 1;
    const E_INVALID_TRIT: u64 = 2;
    const E_NO_SKILLS_REMAINING: u64 = 3;
    
    /// GF(3) trit values
    const TRIT_MINUS: u8 = 0;    // -1 encoded as 0
    const TRIT_ERGODIC: u8 = 1;  // 0 encoded as 1  
    const TRIT_PLUS: u8 = 2;     // +1 encoded as 2
    
    /// Skill representation
    struct Skill has copy, drop, store {
        name: vector<u8>,
        trit: u8,  // 0=MINUS, 1=ERGODIC, 2=PLUS
    }
    
    /// A valid GF(3)-conserved triplet
    struct Triplet has copy, drop, store {
        minus: Skill,
        ergodic: Skill,
        plus: Skill,
        fingerprint: u64,
    }
    
    /// Pool of skills organized by trit category
    struct SkillPool has key, store {
        minus_skills: vector<Skill>,
        ergodic_skills: vector<Skill>,
        plus_skills: vector<Skill>,
        interaction_entropy: u64,  // Seed from interaction history
    }
    
    /// Result of triplet generation
    struct TripletBatch has drop, store {
        triplets: vector<Triplet>,
        used_indices: vector<u64>,  // For tracking without-replacement
    }
    
    // ═══════════════════════════════════════════════════════════════════════════
    // Core: Sample 3 at a time
    // ═══════════════════════════════════════════════════════════════════════════
    
    /// Sample a single triplet WITH replacement (skills can be reused)
    #[randomness]
    entry fun sample_triplet_with_replacement(
        pool: &SkillPool,
    ): Triplet acquires SkillPool {
        let n_minus = vector::length(&pool.minus_skills);
        let n_ergodic = vector::length(&pool.ergodic_skills);
        let n_plus = vector::length(&pool.plus_skills);
        
        assert!(n_minus > 0 && n_ergodic > 0 && n_plus > 0, E_INSUFFICIENT_SKILLS);
        
        // Use Aptos randomness API for each selection
        let m_idx = randomness::u64_range(0, n_minus);
        let e_idx = randomness::u64_range(0, n_ergodic);
        let p_idx = randomness::u64_range(0, n_plus);
        
        let minus = *vector::borrow(&pool.minus_skills, m_idx);
        let ergodic = *vector::borrow(&pool.ergodic_skills, e_idx);
        let plus = *vector::borrow(&pool.plus_skills, p_idx);
        
        // Compute fingerprint via XOR
        let fp = compute_fingerprint(&minus, &ergodic, &plus);
        
        Triplet { minus, ergodic, plus, fingerprint: fp }
    }
    
    /// Sample multiple triplets WITHOUT replacement
    /// Each skill can only be used once across all triplets
    #[randomness]
    entry fun sample_triplets_without_replacement(
        pool: &mut SkillPool,
        count: u64,
    ): vector<Triplet> acquires SkillPool {
        let triplets = vector::empty<Triplet>();
        
        let i = 0;
        while (i < count) {
            let n_minus = vector::length(&pool.minus_skills);
            let n_ergodic = vector::length(&pool.ergodic_skills);
            let n_plus = vector::length(&pool.plus_skills);
            
            // Check if we have skills remaining
            if (n_minus == 0 || n_ergodic == 0 || n_plus == 0) {
                break
            };
            
            // Random indices
            let m_idx = randomness::u64_range(0, n_minus);
            let e_idx = randomness::u64_range(0, n_ergodic);
            let p_idx = randomness::u64_range(0, n_plus);
            
            // Remove selected skills (swap-and-pop for O(1))
            let minus = vector::swap_remove(&mut pool.minus_skills, m_idx);
            let ergodic = vector::swap_remove(&mut pool.ergodic_skills, e_idx);
            let plus = vector::swap_remove(&mut pool.plus_skills, p_idx);
            
            let fp = compute_fingerprint(&minus, &ergodic, &plus);
            vector::push_back(&mut triplets, Triplet { minus, ergodic, plus, fingerprint: fp });
            
            i = i + 1;
        };
        
        triplets
    }
    
    // ═══════════════════════════════════════════════════════════════════════════
    // With Coloring: Use interaction entropy as seed
    // ═══════════════════════════════════════════════════════════════════════════
    
    /// Sample triplet using interaction entropy as index modifier
    /// This creates deterministic coloring from interaction history
    #[randomness]
    entry fun sample_triplet_with_coloring(
        pool: &SkillPool,
        interaction_index: u64,
    ): Triplet acquires SkillPool {
        let n_minus = vector::length(&pool.minus_skills);
        let n_ergodic = vector::length(&pool.ergodic_skills);
        let n_plus = vector::length(&pool.plus_skills);
        
        assert!(n_minus > 0 && n_ergodic > 0 && n_plus > 0, E_INSUFFICIENT_SKILLS);
        
        // Mix interaction entropy with on-chain randomness
        let entropy_seed = pool.interaction_entropy ^ interaction_index;
        
        // Get base random values
        let r_minus = randomness::u64_range(0, n_minus);
        let r_ergodic = randomness::u64_range(0, n_ergodic);
        let r_plus = randomness::u64_range(0, n_plus);
        
        // XOR with entropy-derived offsets for deterministic coloring
        let m_idx = (r_minus + (entropy_seed % n_minus)) % n_minus;
        let e_idx = (r_ergodic + ((entropy_seed >> 16) % n_ergodic)) % n_ergodic;
        let p_idx = (r_plus + ((entropy_seed >> 32) % n_plus)) % n_plus;
        
        let minus = *vector::borrow(&pool.minus_skills, m_idx);
        let ergodic = *vector::borrow(&pool.ergodic_skills, e_idx);
        let plus = *vector::borrow(&pool.plus_skills, p_idx);
        
        let fp = compute_fingerprint(&minus, &ergodic, &plus);
        
        Triplet { minus, ergodic, plus, fingerprint: fp }
    }
    
    /// Sample WITHOUT coloring (pure random, no entropy mixing)
    #[randomness]
    entry fun sample_triplet_without_coloring(
        pool: &SkillPool,
    ): Triplet acquires SkillPool {
        // Identical to with_replacement but semantically distinct
        sample_triplet_with_replacement(pool)
    }
    
    // ═══════════════════════════════════════════════════════════════════════════
    // Batch: Generate 3 triplets at a time using permutation
    // ═══════════════════════════════════════════════════════════════════════════
    
    /// Generate exactly 3 triplets using Aptos permutation API
    /// Most efficient for batch operations
    #[randomness]
    entry fun sample_three_triplets(
        pool: &SkillPool,
        with_replacement: bool,
    ): vector<Triplet> acquires SkillPool {
        let triplets = vector::empty<Triplet>();
        
        let n_minus = vector::length(&pool.minus_skills);
        let n_ergodic = vector::length(&pool.ergodic_skills);
        let n_plus = vector::length(&pool.plus_skills);
        
        if (with_replacement) {
            // Use permutation for efficient batch random selection
            let perm_m = randomness::permutation(n_minus);
            let perm_e = randomness::permutation(n_ergodic);
            let perm_p = randomness::permutation(n_plus);
            
            let i = 0;
            while (i < 3) {
                let m_idx = *vector::borrow(&perm_m, i % n_minus);
                let e_idx = *vector::borrow(&perm_e, i % n_ergodic);
                let p_idx = *vector::borrow(&perm_p, i % n_plus);
                
                let minus = *vector::borrow(&pool.minus_skills, m_idx);
                let ergodic = *vector::borrow(&pool.ergodic_skills, e_idx);
                let plus = *vector::borrow(&pool.plus_skills, p_idx);
                
                let fp = compute_fingerprint(&minus, &ergodic, &plus);
                vector::push_back(&mut triplets, Triplet { minus, ergodic, plus, fingerprint: fp });
                
                i = i + 1;
            };
        } else {
            // Without replacement - need at least 3 of each
            assert!(n_minus >= 3 && n_ergodic >= 3 && n_plus >= 3, E_INSUFFICIENT_SKILLS);
            
            let perm_m = randomness::permutation(n_minus);
            let perm_e = randomness::permutation(n_ergodic);
            let perm_p = randomness::permutation(n_plus);
            
            let i = 0;
            while (i < 3) {
                let m_idx = *vector::borrow(&perm_m, i);
                let e_idx = *vector::borrow(&perm_e, i);
                let p_idx = *vector::borrow(&perm_p, i);
                
                let minus = *vector::borrow(&pool.minus_skills, m_idx);
                let ergodic = *vector::borrow(&pool.ergodic_skills, e_idx);
                let plus = *vector::borrow(&pool.plus_skills, p_idx);
                
                let fp = compute_fingerprint(&minus, &ergodic, &plus);
                vector::push_back(&mut triplets, Triplet { minus, ergodic, plus, fingerprint: fp });
                
                i = i + 1;
            };
        };
        
        triplets
    }
    
    // ═══════════════════════════════════════════════════════════════════════════
    // Interaction Entropy Management
    // ═══════════════════════════════════════════════════════════════════════════
    
    /// Update interaction entropy (accumulates from off-chain interactions)
    public fun update_interaction_entropy(
        pool: &mut SkillPool,
        new_entropy: u64,
    ) {
        // XOR-accumulate to preserve entropy
        pool.interaction_entropy = pool.interaction_entropy ^ new_entropy;
    }
    
    /// Set interaction entropy from seed (e.g., thread ID hash)
    public fun set_entropy_from_seed(
        pool: &mut SkillPool,
        seed: vector<u8>,
    ) {
        // Simple hash: XOR all bytes shifted
        let entropy: u64 = 0;
        let i = 0;
        let len = vector::length(&seed);
        while (i < len && i < 8) {
            let byte = (*vector::borrow(&seed, i) as u64);
            entropy = entropy | (byte << ((i * 8) as u8));
            i = i + 1;
        };
        pool.interaction_entropy = entropy;
    }
    
    // ═══════════════════════════════════════════════════════════════════════════
    // Helpers
    // ═══════════════════════════════════════════════════════════════════════════
    
    /// Compute XOR fingerprint from triplet (order-independent)
    fun compute_fingerprint(minus: &Skill, ergodic: &Skill, plus: &Skill): u64 {
        // Simple hash of name bytes
        let h1 = hash_name(&minus.name);
        let h2 = hash_name(&ergodic.name);
        let h3 = hash_name(&plus.name);
        h1 ^ h2 ^ h3
    }
    
    fun hash_name(name: &vector<u8>): u64 {
        let hash: u64 = 0;
        let i = 0;
        let len = vector::length(name);
        while (i < len) {
            let byte = (*vector::borrow(name, i) as u64);
            hash = ((hash << 5) | (hash >> 59)) ^ byte;  // Rotate and XOR
            i = i + 1;
        };
        hash
    }
    
    /// Verify GF(3) conservation: trit values must sum to 0 mod 3
    /// MINUS(-1) + ERGODIC(0) + PLUS(+1) = 0 ✓
    public fun verify_triplet(triplet: &Triplet): bool {
        // With encoding: MINUS=0, ERGODIC=1, PLUS=2
        // Sum: 0 + 1 + 2 = 3 ≡ 0 (mod 3) ✓
        let sum = (triplet.minus.trit as u64) + 
                  (triplet.ergodic.trit as u64) + 
                  (triplet.plus.trit as u64);
        sum % 3 == 0
    }
    
    /// Get triplet count statistics
    public fun get_pool_stats(pool: &SkillPool): (u64, u64, u64, u64) {
        let n_minus = vector::length(&pool.minus_skills);
        let n_ergodic = vector::length(&pool.ergodic_skills);
        let n_plus = vector::length(&pool.plus_skills);
        let possible_triplets = n_minus * n_ergodic * n_plus;
        (n_minus, n_ergodic, n_plus, possible_triplets)
    }
    
    // ═══════════════════════════════════════════════════════════════════════════
    // Test helpers
    // ═══════════════════════════════════════════════════════════════════════════
    
    #[test_only]
    public fun create_test_pool(): SkillPool {
        let minus_skills = vector::empty<Skill>();
        let ergodic_skills = vector::empty<Skill>();
        let plus_skills = vector::empty<Skill>();
        
        // Add test skills (from TRIPARTITE_AGENTS.md)
        vector::push_back(&mut minus_skills, Skill { name: b"sheaf-cohomology", trit: TRIT_MINUS });
        vector::push_back(&mut minus_skills, Skill { name: b"code-review", trit: TRIT_MINUS });
        vector::push_back(&mut minus_skills, Skill { name: b"spi-parallel-verify", trit: TRIT_MINUS });
        
        vector::push_back(&mut ergodic_skills, Skill { name: b"acsets", trit: TRIT_ERGODIC });
        vector::push_back(&mut ergodic_skills, Skill { name: b"discopy", trit: TRIT_ERGODIC });
        vector::push_back(&mut ergodic_skills, Skill { name: b"gh-cli", trit: TRIT_ERGODIC });
        
        vector::push_back(&mut plus_skills, Skill { name: b"world-hopping", trit: TRIT_PLUS });
        vector::push_back(&mut plus_skills, Skill { name: b"julia-gay", trit: TRIT_PLUS });
        vector::push_back(&mut plus_skills, Skill { name: b"triad-interleave", trit: TRIT_PLUS });
        
        SkillPool {
            minus_skills,
            ergodic_skills,
            plus_skills,
            interaction_entropy: 0x6761795f636f6c6f,  // "gay_colo"
        }
    }
}
