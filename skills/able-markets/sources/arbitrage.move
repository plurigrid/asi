/// Cross-World Arbitrage Module
/// 
/// Detects and executes arbitrage opportunities between correlated standard worlds.
/// Uses trait similarity and historical ecosystem correlation patterns.

module able_markets::arbitrage {
    use std::string::String;
    use std::vector;
    use aptos_framework::event;

    /// Minimum spread for arbitrage opportunity (10% = 100,000 scaled)
    const MIN_ARBITRAGE_SPREAD: u64 = 100_000;
    
    /// Minimum trait similarity threshold (50% = 500,000 scaled)
    const MIN_TRAIT_SIMILARITY: u64 = 500_000;

    /// Correlation confidence threshold (40% = 400,000 scaled)
    const MIN_CORRELATION_CONFIDENCE: u64 = 400_000;

    /// Errors
    const E_NO_ARBITRAGE: u64 = 300;
    const E_INSUFFICIENT_CONFIDENCE: u64 = 301;

    /// Cross-ecosystem correlation pattern
    struct CorrelationPattern has store, copy, drop {
        leader_ecosystem: String,
        follower_ecosystem: String,
        pattern_name: String,
        lag_months: u64,
        confidence: u64,            // Scaled by 1M
    }

    /// Detected arbitrage opportunity
    struct ArbitrageOpportunity has store, copy, drop {
        leader_world: String,
        follower_world: String,
        leader_probability: u64,
        follower_probability: u64,
        spread: u64,
        trait_similarity: u64,
        expected_value: u64,
        signal: u8,                 // 0=HOLD, 1=BUY_FOLLOWER, 2=SELL_LEADER
    }

    /// Registry of known correlation patterns
    struct CorrelationRegistry has key {
        patterns: vector<CorrelationPattern>,
    }

    /// Events
    #[event]
    struct ArbitrageDetected has drop, store {
        leader_world: String,
        follower_world: String,
        spread: u64,
        signal: u8,
    }

    #[event]
    struct ArbitrageExecuted has drop, store {
        opportunity_hash: vector<u8>,
        profit: u64,
        executor: address,
    }

    /// Initialize correlation registry with known patterns
    public entry fun initialize(admin: &signer) {
        let patterns = vector::empty<CorrelationPattern>();
        
        // Swift → Aptos: Memory safety patterns
        vector::push_back(&mut patterns, CorrelationPattern {
            leader_ecosystem: std::string::utf8(b"swift"),
            follower_ecosystem: std::string::utf8(b"aptos"),
            pattern_name: std::string::utf8(b"memory_safety"),
            lag_months: 12,
            confidence: 700_000,  // 70%
        });
        
        // SRFI → Swift: Pattern matching
        vector::push_back(&mut patterns, CorrelationPattern {
            leader_ecosystem: std::string::utf8(b"srfi"),
            follower_ecosystem: std::string::utf8(b"swift"),
            pattern_name: std::string::utf8(b"pattern_matching"),
            lag_months: 24,
            confidence: 500_000,  // 50%
        });
        
        // Aptos → SRFI: Formal verification
        vector::push_back(&mut patterns, CorrelationPattern {
            leader_ecosystem: std::string::utf8(b"aptos"),
            follower_ecosystem: std::string::utf8(b"srfi"),
            pattern_name: std::string::utf8(b"formal_verification"),
            lag_months: 18,
            confidence: 400_000,  // 40%
        });
        
        // Swift → SRFI: Async patterns
        vector::push_back(&mut patterns, CorrelationPattern {
            leader_ecosystem: std::string::utf8(b"swift"),
            follower_ecosystem: std::string::utf8(b"srfi"),
            pattern_name: std::string::utf8(b"async_concurrency"),
            lag_months: 36,
            confidence: 600_000,  // 60%
        });
        
        move_to(admin, CorrelationRegistry { patterns });
    }

    /// Detect arbitrage opportunity between two worlds
    public fun detect_arbitrage(
        leader_world_id: String,
        leader_ecosystem: String,
        leader_probability: u64,
        leader_trait_hash: vector<u8>,
        follower_world_id: String,
        follower_ecosystem: String,
        follower_probability: u64,
        follower_trait_hash: vector<u8>,
    ): ArbitrageOpportunity acquires CorrelationRegistry {
        let registry = borrow_global<CorrelationRegistry>(@able_markets);
        
        // Check if there's a known correlation pattern
        let correlation_confidence = find_correlation(
            &registry.patterns,
            &leader_ecosystem,
            &follower_ecosystem
        );
        
        // Calculate trait similarity (Jaccard-like based on hash overlap)
        let trait_similarity = calculate_trait_similarity(
            &leader_trait_hash,
            &follower_trait_hash
        );
        
        // Calculate spread
        let spread = if (leader_probability > follower_probability) {
            leader_probability - follower_probability
        } else {
            0
        };
        
        // Determine signal
        let signal = if (
            spread >= MIN_ARBITRAGE_SPREAD &&
            trait_similarity >= MIN_TRAIT_SIMILARITY &&
            correlation_confidence >= MIN_CORRELATION_CONFIDENCE &&
            leader_probability >= 700_000  // Leader > 70%
        ) {
            1  // BUY_FOLLOWER
        } else if (
            spread >= MIN_ARBITRAGE_SPREAD &&
            follower_probability > leader_probability &&
            correlation_confidence >= MIN_CORRELATION_CONFIDENCE
        ) {
            2  // SELL_LEADER (follower leading)
        } else {
            0  // HOLD
        };
        
        // Calculate expected value
        let expected_value = if (signal > 0) {
            (spread * correlation_confidence * trait_similarity) / (1_000_000 * 1_000_000)
        } else {
            0
        };
        
        let opportunity = ArbitrageOpportunity {
            leader_world: leader_world_id,
            follower_world: follower_world_id,
            leader_probability,
            follower_probability,
            spread,
            trait_similarity,
            expected_value,
            signal,
        };
        
        if (signal > 0) {
            event::emit(ArbitrageDetected {
                leader_world: opportunity.leader_world,
                follower_world: opportunity.follower_world,
                spread,
                signal,
            });
        };
        
        opportunity
    }

    /// Find correlation confidence between two ecosystems
    fun find_correlation(
        patterns: &vector<CorrelationPattern>,
        leader: &String,
        follower: &String,
    ): u64 {
        let len = vector::length(patterns);
        let i = 0;
        while (i < len) {
            let pattern = vector::borrow(patterns, i);
            if (&pattern.leader_ecosystem == leader && 
                &pattern.follower_ecosystem == follower) {
                return pattern.confidence
            };
            i = i + 1;
        };
        0  // No known correlation
    }

    /// Calculate trait similarity from hashes
    /// Simplified: count matching bytes / total bytes
    fun calculate_trait_similarity(
        hash_a: &vector<u8>,
        hash_b: &vector<u8>,
    ): u64 {
        let len_a = vector::length(hash_a);
        let len_b = vector::length(hash_b);
        
        if (len_a == 0 || len_b == 0) {
            return 0
        };
        
        let min_len = if (len_a < len_b) { len_a } else { len_b };
        let matching = 0u64;
        
        let i = 0;
        while (i < min_len) {
            if (*vector::borrow(hash_a, i) == *vector::borrow(hash_b, i)) {
                matching = matching + 1;
            };
            i = i + 1;
        };
        
        // Scale to 1M
        (matching * 1_000_000) / min_len
    }

    /// View: Get number of registered correlation patterns
    #[view]
    public fun get_pattern_count(): u64 acquires CorrelationRegistry {
        let registry = borrow_global<CorrelationRegistry>(@able_markets);
        vector::length(&registry.patterns)
    }
}
