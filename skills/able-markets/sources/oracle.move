/// Oracle Resolution Module for *Able Markets
/// 
/// Multi-sig attestation from GitHub status changes to resolve on-chain markets.
/// Oracles poll GitHub APIs and submit attestations; threshold agreement triggers resolution.

module able_markets::oracle {
    use std::signer;
    use std::vector;
    use std::string::String;
    use aptos_framework::timestamp;
    use aptos_framework::event;

    /// Error codes
    const E_NOT_ORACLE: u64 = 100;
    const E_ALREADY_ATTESTED: u64 = 101;
    const E_THRESHOLD_NOT_MET: u64 = 102;
    const E_INVALID_PROPOSAL: u64 = 103;
    const E_STALE_ATTESTATION: u64 = 104;

    /// Attestation validity window (24 hours in seconds)
    const ATTESTATION_WINDOW: u64 = 86400;

    /// Oracle configuration
    struct OracleConfig has key {
        oracles: vector<address>,
        threshold: u64,           // e.g., 3 of 5
        admin: address,
    }

    /// Single attestation from an oracle
    struct Attestation has store, drop, copy {
        oracle: address,
        proposal_id: String,
        ecosystem: String,        // "aptos", "swift", "srfi"
        outcome: bool,            // true = accepted
        source_hash: vector<u8>,  // GitHub commit SHA
        timestamp: u64,
    }

    /// Pending attestations for a proposal
    struct PendingResolution has key {
        proposal_id: String,
        attestations: vector<Attestation>,
        resolved: bool,
    }

    /// Events
    #[event]
    struct AttestationSubmitted has drop, store {
        oracle: address,
        proposal_id: String,
        outcome: bool,
        source_hash: vector<u8>,
    }

    #[event]
    struct ThresholdReached has drop, store {
        proposal_id: String,
        outcome: bool,
        attestation_count: u64,
    }

    /// Initialize oracle configuration
    public entry fun initialize(
        admin: &signer,
        oracles: vector<address>,
        threshold: u64,
    ) {
        let admin_addr = signer::address_of(admin);
        move_to(admin, OracleConfig {
            oracles,
            threshold,
            admin: admin_addr,
        });
    }

    /// Add a new oracle (admin only)
    public entry fun add_oracle(
        admin: &signer,
        new_oracle: address,
    ) acquires OracleConfig {
        let admin_addr = signer::address_of(admin);
        let config = borrow_global_mut<OracleConfig>(admin_addr);
        assert!(admin_addr == config.admin, E_NOT_ORACLE);
        vector::push_back(&mut config.oracles, new_oracle);
    }

    /// Remove an oracle (admin only)
    public entry fun remove_oracle(
        admin: &signer,
        oracle_to_remove: address,
    ) acquires OracleConfig {
        let admin_addr = signer::address_of(admin);
        let config = borrow_global_mut<OracleConfig>(admin_addr);
        assert!(admin_addr == config.admin, E_NOT_ORACLE);
        
        let (found, idx) = vector::index_of(&config.oracles, &oracle_to_remove);
        if (found) {
            vector::remove(&mut config.oracles, idx);
        };
    }

    /// Submit an attestation for a proposal outcome
    public entry fun submit_attestation(
        oracle: &signer,
        config_addr: address,
        proposal_id: String,
        ecosystem: String,
        outcome: bool,
        source_hash: vector<u8>,
    ) acquires OracleConfig, PendingResolution {
        let oracle_addr = signer::address_of(oracle);
        let config = borrow_global<OracleConfig>(config_addr);
        
        // Verify oracle is authorized
        let (is_oracle, _) = vector::index_of(&config.oracles, &oracle_addr);
        assert!(is_oracle, E_NOT_ORACLE);
        
        let now = timestamp::now_seconds();
        
        let attestation = Attestation {
            oracle: oracle_addr,
            proposal_id,
            ecosystem,
            outcome,
            source_hash,
            timestamp: now,
        };
        
        // Get or create pending resolution
        if (!exists<PendingResolution>(config_addr)) {
            move_to(oracle, PendingResolution {
                proposal_id,
                attestations: vector::singleton(attestation),
                resolved: false,
            });
        } else {
            let pending = borrow_global_mut<PendingResolution>(config_addr);
            
            // Check oracle hasn't already attested
            let len = vector::length(&pending.attestations);
            let i = 0;
            while (i < len) {
                let existing = vector::borrow(&pending.attestations, i);
                assert!(existing.oracle != oracle_addr, E_ALREADY_ATTESTED);
                i = i + 1;
            };
            
            vector::push_back(&mut pending.attestations, attestation);
        };
        
        event::emit(AttestationSubmitted {
            oracle: oracle_addr,
            proposal_id,
            outcome,
            source_hash,
        });
    }

    /// Check if threshold is met and return consensus outcome
    public fun check_threshold(
        config_addr: address,
    ): (bool, bool, u64) acquires OracleConfig, PendingResolution {
        let config = borrow_global<OracleConfig>(config_addr);
        let pending = borrow_global<PendingResolution>(config_addr);
        
        let now = timestamp::now_seconds();
        let valid_yes = 0u64;
        let valid_no = 0u64;
        
        let len = vector::length(&pending.attestations);
        let i = 0;
        
        while (i < len) {
            let att = vector::borrow(&pending.attestations, i);
            // Only count non-stale attestations
            if (now - att.timestamp <= ATTESTATION_WINDOW) {
                if (att.outcome) {
                    valid_yes = valid_yes + 1;
                } else {
                    valid_no = valid_no + 1;
                };
            };
            i = i + 1;
        };
        
        let total_valid = valid_yes + valid_no;
        let threshold_met = total_valid >= config.threshold;
        let outcome = valid_yes > valid_no;
        
        (threshold_met, outcome, total_valid)
    }

    /// Trigger resolution if threshold met
    public entry fun trigger_resolution(
        caller: &signer,
        config_addr: address,
        market_owner: address,
    ) acquires OracleConfig, PendingResolution {
        let (threshold_met, outcome, count) = check_threshold(config_addr);
        assert!(threshold_met, E_THRESHOLD_NOT_MET);
        
        let pending = borrow_global_mut<PendingResolution>(config_addr);
        pending.resolved = true;
        
        // Get resolution hash from majority attestation
        let resolution_hash = get_majority_hash(&pending.attestations, outcome);
        
        // Call market resolution (would need friend declaration in production)
        // able_markets::lmsr::resolve(caller, market_owner, outcome, resolution_hash);
        
        event::emit(ThresholdReached {
            proposal_id: pending.proposal_id,
            outcome,
            attestation_count: count,
        });
    }

    /// Get hash from majority outcome attestations
    fun get_majority_hash(attestations: &vector<Attestation>, outcome: bool): vector<u8> {
        let len = vector::length(attestations);
        let i = 0;
        while (i < len) {
            let att = vector::borrow(attestations, i);
            if (att.outcome == outcome) {
                return att.source_hash
            };
            i = i + 1;
        };
        vector::empty()
    }

    /// View: get attestation count
    #[view]
    public fun get_attestation_count(config_addr: address): u64 acquires PendingResolution {
        if (!exists<PendingResolution>(config_addr)) {
            return 0
        };
        let pending = borrow_global<PendingResolution>(config_addr);
        vector::length(&pending.attestations)
    }

    /// View: get oracle list
    #[view]
    public fun get_oracles(config_addr: address): vector<address> acquires OracleConfig {
        let config = borrow_global<OracleConfig>(config_addr);
        config.oracles
    }
}
