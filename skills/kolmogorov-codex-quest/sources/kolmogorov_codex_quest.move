/// Kolmogorov Codex Quest: L-Space Traversal with Plurigrid ASI Identity Proof
///
/// A cryptographic puzzle requiring solvers to prove they used the Plurigrid ASI
/// skill lattice via four-layer identity verification:
/// 1. Wikidata Distillation (26 letters × 69 concepts = 1794 Q-items)
/// 2. GayMCP Color Trace (GF(3) conservation)
/// 3. Skill Lattice Path (≥6 skills invoked)
/// 4. World Navigation (≥6 ~/worlds visited)
///
/// Bounty: 2 APT
///
/// References:
/// - Valeria Nikolaenko: Data Availability Sampling & Danksharding
/// - Lee Cronin: Assembly Theory (complexity metrics)
/// - Badiou: Triangle Inequality for world-hopping
/// - GF(3): Galois Field conservation law
module kolmogorov_codex::quest {
    use std::signer;
    use std::vector;
    use std::option::{Self, Option};
    use aptos_framework::coin;
    use aptos_framework::aptos_coin::AptosCoin;
    use aptos_framework::timestamp;
    use aptos_framework::event;
    use aptos_std::hash;

    // ═══════════════════════════════════════════════════════════════════════
    // ERRORS
    // ═══════════════════════════════════════════════════════════════════════

    const E_QUEST_ALREADY_EXISTS: u64 = 1;
    const E_QUEST_NOT_FOUND: u64 = 2;
    const E_QUEST_ALREADY_SOLVED: u64 = 3;
    const E_QUEST_EXPIRED: u64 = 4;
    const E_QUEST_NOT_EXPIRED: u64 = 5;
    const E_INVALID_SOLUTION: u64 = 6;
    const E_INSUFFICIENT_BOUNTY: u64 = 7;
    const E_INSUFFICIENT_SKILLS: u64 = 8;
    const E_INSUFFICIENT_WORLDS: u64 = 9;
    const E_GF3_VIOLATION: u64 = 10;
    const E_INVALID_COMMITMENT: u64 = 11;
    const E_NOT_QUEST_CREATOR: u64 = 12;
    const E_INVALID_WIKIDATA_ROOT: u64 = 13;
    const E_INVALID_GAYMCP_ROOT: u64 = 14;

    // ═══════════════════════════════════════════════════════════════════════
    // CONSTANTS
    // ═══════════════════════════════════════════════════════════════════════

    /// Minimum bounty: 1 APT (100_000_000 octas)
    const MIN_BOUNTY_OCTAS: u64 = 100_000_000;

    /// Quest timeout: 30 days in seconds
    const QUEST_TIMEOUT_SECS: u64 = 2592000;

    /// Minimum skills required for identity proof
    const MIN_SKILLS_REQUIRED: u64 = 6;

    /// Minimum worlds required for identity proof
    const MIN_WORLDS_REQUIRED: u64 = 6;

    // ═══════════════════════════════════════════════════════════════════════
    // STRUCTS
    // ═══════════════════════════════════════════════════════════════════════

    /// Identity proof submitted by solver
    struct IdentityProof has copy, drop, store {
        wikidata_root: vector<u8>,
        gaymcp_root: vector<u8>,
        skill_count: u64,
        world_count: u64,
        gf3_sum: u8,
        proof_uri: vector<u8>,
    }

    /// Quest state
    struct Quest has key {
        creator: address,
        commitment: vector<u8>,
        bounty: coin::Coin<AptosCoin>,
        created_at: u64,
        expires_at: u64,
        solved: bool,
        winner: Option<address>,
        winning_proof: Option<IdentityProof>,
    }

    // ═══════════════════════════════════════════════════════════════════════
    // EVENTS
    // ═══════════════════════════════════════════════════════════════════════

    #[event]
    struct QuestCreated has drop, store {
        quest_address: address,
        creator: address,
        bounty_octas: u64,
        commitment: vector<u8>,
        expires_at: u64,
    }

    #[event]
    struct QuestSolved has drop, store {
        quest_address: address,
        solver: address,
        bounty_octas: u64,
        skill_count: u64,
        world_count: u64,
        solved_at: u64,
    }

    #[event]
    struct QuestExpired has drop, store {
        quest_address: address,
        refunded_to: address,
        bounty_octas: u64,
        expired_at: u64,
    }

    // ═══════════════════════════════════════════════════════════════════════
    // ENTRY FUNCTIONS
    // ═══════════════════════════════════════════════════════════════════════

    /// Create a new quest with bounty and solution commitment
    public entry fun create_quest(
        creator: &signer,
        bounty_octas: u64,
        commitment: vector<u8>,
    ) {
        let creator_addr = signer::address_of(creator);
        assert!(bounty_octas >= MIN_BOUNTY_OCTAS, E_INSUFFICIENT_BOUNTY);
        assert!(vector::length(&commitment) == 32, E_INVALID_COMMITMENT);
        assert!(!exists<Quest>(creator_addr), E_QUEST_ALREADY_EXISTS);

        let bounty_coins = coin::withdraw<AptosCoin>(creator, bounty_octas);
        let now = timestamp::now_seconds();

        move_to(creator, Quest {
            creator: creator_addr,
            commitment,
            bounty: bounty_coins,
            created_at: now,
            expires_at: now + QUEST_TIMEOUT_SECS,
            solved: false,
            winner: option::none(),
            winning_proof: option::none(),
        });

        event::emit(QuestCreated {
            quest_address: creator_addr,
            creator: creator_addr,
            bounty_octas,
            commitment,
            expires_at: now + QUEST_TIMEOUT_SECS,
        });
    }

    /// Submit solution with identity proof
    public entry fun submit_solution(
        solver: &signer,
        quest_address: address,
        solution: vector<u8>,
        wikidata_root: vector<u8>,
        gaymcp_root: vector<u8>,
        skill_count: u64,
        world_count: u64,
        gf3_sum: u8,
        proof_uri: vector<u8>,
    ) acquires Quest {
        let solver_addr = signer::address_of(solver);
        assert!(exists<Quest>(quest_address), E_QUEST_NOT_FOUND);
        
        let quest = borrow_global_mut<Quest>(quest_address);
        assert!(!quest.solved, E_QUEST_ALREADY_SOLVED);
        assert!(timestamp::now_seconds() < quest.expires_at, E_QUEST_EXPIRED);

        // Verify solution
        let solution_hash = hash::sha3_256(solution);
        assert!(solution_hash == quest.commitment, E_INVALID_SOLUTION);

        // Verify identity proof
        assert!(skill_count >= MIN_SKILLS_REQUIRED, E_INSUFFICIENT_SKILLS);
        assert!(world_count >= MIN_WORLDS_REQUIRED, E_INSUFFICIENT_WORLDS);
        assert!(gf3_sum % 3 == 0, E_GF3_VIOLATION);
        assert!(vector::length(&wikidata_root) == 32, E_INVALID_WIKIDATA_ROOT);
        assert!(vector::length(&gaymcp_root) == 32, E_INVALID_GAYMCP_ROOT);

        // Record solution
        quest.solved = true;
        quest.winner = option::some(solver_addr);
        quest.winning_proof = option::some(IdentityProof {
            wikidata_root, gaymcp_root, skill_count, world_count, gf3_sum, proof_uri,
        });

        // Transfer bounty
        let bounty_value = coin::value(&quest.bounty);
        coin::deposit(solver_addr, coin::extract_all(&mut quest.bounty));

        event::emit(QuestSolved {
            quest_address,
            solver: solver_addr,
            bounty_octas: bounty_value,
            skill_count,
            world_count,
            solved_at: timestamp::now_seconds(),
        });
    }

    /// Refund if expired
    public entry fun refund_expired(creator: &signer) acquires Quest {
        let creator_addr = signer::address_of(creator);
        assert!(exists<Quest>(creator_addr), E_QUEST_NOT_FOUND);

        let Quest { creator: c, commitment: _, bounty, created_at: _, expires_at, solved, winner: _, winning_proof: _ } = move_from<Quest>(creator_addr);
        assert!(c == creator_addr, E_NOT_QUEST_CREATOR);
        assert!(!solved, E_QUEST_ALREADY_SOLVED);
        assert!(timestamp::now_seconds() >= expires_at, E_QUEST_NOT_EXPIRED);

        let bounty_value = coin::value(&bounty);
        coin::deposit(creator_addr, bounty);

        event::emit(QuestExpired {
            quest_address: creator_addr,
            refunded_to: creator_addr,
            bounty_octas: bounty_value,
            expired_at: timestamp::now_seconds(),
        });
    }

    // ═══════════════════════════════════════════════════════════════════════
    // VIEW FUNCTIONS
    // ═══════════════════════════════════════════════════════════════════════

    #[view]
    public fun get_quest_info(quest_address: address): (address, u64, u64, bool, Option<address>) acquires Quest {
        let quest = borrow_global<Quest>(quest_address);
        (quest.creator, coin::value(&quest.bounty), quest.expires_at, quest.solved, quest.winner)
    }

    #[view]
    public fun is_quest_active(quest_address: address): bool acquires Quest {
        if (!exists<Quest>(quest_address)) { return false };
        let quest = borrow_global<Quest>(quest_address);
        !quest.solved && timestamp::now_seconds() < quest.expires_at
    }

    #[view]
    public fun get_proof_requirements(): (u64, u64) {
        (MIN_SKILLS_REQUIRED, MIN_WORLDS_REQUIRED)
    }
}
