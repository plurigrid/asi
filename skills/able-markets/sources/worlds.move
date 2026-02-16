/// Multiversal Finance on Standards - World State Machine
/// 
/// Each proposal defines a possible world. Trading is navigating the multiverse.
/// GF(3) conservation ensures balanced exposure across world outcomes.

module able_markets::worlds {
    use std::string::String;
    use std::vector;
    use aptos_framework::event;

    /// World states corresponding to proposal lifecycle
    const WORLD_CURRENT: u8 = 0;    // W₀: Standard not adopted
    const WORLD_DRAFT: u8 = 1;      // W_draft: Proposal written
    const WORLD_REVIEW: u8 = 2;     // W_review: Under community review
    const WORLD_LAST_CALL: u8 = 3;  // W_lastcall: Final comment period
    const WORLD_ACCEPTED: u8 = 4;   // W₁: Standard adopted
    const WORLD_DEPLOYED: u8 = 5;   // W₂: Live on mainnet
    const WORLD_REJECTED: u8 = 6;   // W_reject: Proposal failed

    /// GF(3) trit values
    const TRIT_MINUS: u8 = 0;       // -1: Queryable (validators)
    const TRIT_ERGODIC: u8 = 1;     // 0: Derangeable (market makers)
    const TRIT_PLUS: u8 = 2;        // +1: Colorable (speculators)

    /// Errors
    const E_INVALID_TRANSITION: u64 = 200;
    const E_WORLD_NOT_FOUND: u64 = 201;
    const E_GF3_VIOLATION: u64 = 202;

    /// A possible world state for a standard proposal
    struct World has key, store, copy, drop {
        world_id: String,           // e.g., "W_AIP137_accepted"
        proposal_id: String,        // e.g., "AIP-137"
        ecosystem: String,          // "aptos", "swift", "srfi"
        state: u8,                  // WORLD_* constant
        trit: u8,                   // GF(3) classification
        probability: u64,           // Market-implied, scaled by 1M
        wev: u64,                   // World Extractable Value in μAPT
        trait_hash: vector<u8>,     // Hash of *Able trait for correlation
    }

    /// Registry of all possible worlds
    struct Multiverse has key {
        worlds: vector<World>,
        total_wev: u64,
        gf3_balance: i64,           // Should be 0 for balanced portfolio
    }

    /// Cross-world correlation for arbitrage
    struct WorldCorrelation has store, copy, drop {
        world_a: String,
        world_b: String,
        correlation: u64,           // Scaled 0-1M
        lag_months: u64,
        confidence: u64,            // Scaled 0-1M
    }

    /// Events
    #[event]
    struct WorldCreated has drop, store {
        world_id: String,
        proposal_id: String,
        initial_state: u8,
    }

    #[event]
    struct WorldTransition has drop, store {
        world_id: String,
        from_state: u8,
        to_state: u8,
        new_probability: u64,
    }

    #[event]
    struct WorldCollapsed has drop, store {
        world_id: String,
        final_state: u8,
        wev_extracted: u64,
    }

    /// Initialize the multiverse
    public entry fun initialize(admin: &signer) {
        move_to(admin, Multiverse {
            worlds: vector::empty(),
            total_wev: 0,
            gf3_balance: 0,
        });
    }

    /// Create a new possible world for a proposal
    public entry fun create_world(
        admin: &signer,
        world_id: String,
        proposal_id: String,
        ecosystem: String,
        trit: u8,
        initial_probability: u64,
        wev: u64,
        trait_hash: vector<u8>,
    ) acquires Multiverse {
        let multiverse = borrow_global_mut<Multiverse>(@able_markets);
        
        let world = World {
            world_id,
            proposal_id,
            ecosystem,
            state: WORLD_DRAFT,
            trit,
            probability: initial_probability,
            wev,
            trait_hash,
        };
        
        vector::push_back(&mut multiverse.worlds, world);
        multiverse.total_wev = multiverse.total_wev + wev;
        
        // Update GF(3) balance
        if (trit == TRIT_MINUS) {
            multiverse.gf3_balance = multiverse.gf3_balance - 1;
        } else if (trit == TRIT_PLUS) {
            multiverse.gf3_balance = multiverse.gf3_balance + 1;
        };
        // ERGODIC (0) doesn't change balance
        
        event::emit(WorldCreated {
            world_id,
            proposal_id,
            initial_state: WORLD_DRAFT,
        });
    }

    /// Transition world to new state based on oracle update
    public entry fun transition_world(
        oracle: &signer,
        world_id: String,
        new_state: u8,
        new_probability: u64,
    ) acquires Multiverse {
        let multiverse = borrow_global_mut<Multiverse>(@able_markets);
        
        let len = vector::length(&multiverse.worlds);
        let i = 0;
        while (i < len) {
            let world = vector::borrow_mut(&mut multiverse.worlds, i);
            if (world.world_id == world_id) {
                let old_state = world.state;
                
                // Validate transition is legal
                assert!(is_valid_transition(old_state, new_state), E_INVALID_TRANSITION);
                
                world.state = new_state;
                world.probability = new_probability;
                
                event::emit(WorldTransition {
                    world_id,
                    from_state: old_state,
                    to_state: new_state,
                    new_probability,
                });
                
                return
            };
            i = i + 1;
        };
        
        abort E_WORLD_NOT_FOUND
    }

    /// Collapse world to final state (accepted or rejected)
    public entry fun collapse_world(
        oracle: &signer,
        world_id: String,
        final_state: u8,
    ) acquires Multiverse {
        assert!(
            final_state == WORLD_ACCEPTED || 
            final_state == WORLD_REJECTED || 
            final_state == WORLD_DEPLOYED,
            E_INVALID_TRANSITION
        );
        
        let multiverse = borrow_global_mut<Multiverse>(@able_markets);
        
        let len = vector::length(&multiverse.worlds);
        let i = 0;
        while (i < len) {
            let world = vector::borrow_mut(&mut multiverse.worlds, i);
            if (world.world_id == world_id) {
                world.state = final_state;
                
                let wev_extracted = if (final_state == WORLD_ACCEPTED || final_state == WORLD_DEPLOYED) {
                    world.wev
                } else {
                    0
                };
                
                // Set probability to 1 or 0
                world.probability = if (final_state == WORLD_REJECTED) { 0 } else { 1_000_000 };
                
                event::emit(WorldCollapsed {
                    world_id,
                    final_state,
                    wev_extracted,
                });
                
                return
            };
            i = i + 1;
        };
        
        abort E_WORLD_NOT_FOUND
    }

    /// Check if transition between states is valid
    fun is_valid_transition(from: u8, to: u8): bool {
        // Valid transitions:
        // CURRENT → DRAFT
        // DRAFT → REVIEW
        // REVIEW → LAST_CALL
        // LAST_CALL → ACCEPTED | REJECTED
        // ACCEPTED → DEPLOYED
        // Any → REJECTED (withdrawal)
        
        if (to == WORLD_REJECTED) { return true };
        
        if (from == WORLD_CURRENT && to == WORLD_DRAFT) { return true };
        if (from == WORLD_DRAFT && to == WORLD_REVIEW) { return true };
        if (from == WORLD_REVIEW && to == WORLD_LAST_CALL) { return true };
        if (from == WORLD_LAST_CALL && to == WORLD_ACCEPTED) { return true };
        if (from == WORLD_ACCEPTED && to == WORLD_DEPLOYED) { return true };
        
        false
    }

    /// View: Get GF(3) balance (should be 0 for balanced multiverse)
    #[view]
    public fun get_gf3_balance(): i64 acquires Multiverse {
        let multiverse = borrow_global<Multiverse>(@able_markets);
        multiverse.gf3_balance
    }

    /// View: Get total WEV across all worlds
    #[view]
    public fun get_total_wev(): u64 acquires Multiverse {
        let multiverse = borrow_global<Multiverse>(@able_markets);
        multiverse.total_wev
    }

    /// View: Get world count
    #[view]
    public fun get_world_count(): u64 acquires Multiverse {
        let multiverse = borrow_global<Multiverse>(@able_markets);
        vector::length(&multiverse.worlds)
    }

    /// Check if multiverse is GF(3) balanced
    #[view]
    public fun is_balanced(): bool acquires Multiverse {
        let multiverse = borrow_global<Multiverse>(@able_markets);
        multiverse.gf3_balance == 0
    }
}
