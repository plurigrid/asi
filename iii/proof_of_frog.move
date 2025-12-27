/// Proof-of-Frog: Society Merge Protocol 🐸
/// "Eat that frog first thing in the morning" - Brian Tracy
/// 
/// When two Aptos Societies merge, they must prove they can eat the same frog.
/// Knowledge networks unite via Reference IDs (RIDs) - Block Science KOI framework.
///
/// Frog Puns Throughout:
///   - Leap before you look (but verify after)
///   - Toadally conserved GF(3)
///   - Ribbit-ing proofs
///   - Hop-timistic execution
///   - Pond-ering knowledge graphs
///
/// Authors to tag:
///   @maboroz (Michael Zargham) - Block Science
///   @ilanbenmeir (Ilan Ben-Meir) - Block Science  
///   @lpscrypt - proof_chain ZK originator
///
/// Reference: https://blog.block.science/a-language-for-knowledge-networks/

module zubyul::proof_of_frog {
    use std::vector;
    use std::string::{Self, String};
    use aptos_framework::randomness;
    use aptos_framework::event;
    use aptos_framework::timestamp;
    use aptos_framework::hash;
    
    /// Error codes (frog-themed)
    const E_NOT_INITIALIZED: u64 = 1;          // Tadpole not hatched
    const E_FROG_NOT_EATEN: u64 = 2;           // Must eat frog first!
    const E_POND_EMPTY: u64 = 3;               // No frogs in pond
    const E_GF3_VIOLATION: u64 = 4;            // Toadally unbalanced
    const E_RID_MISMATCH: u64 = 5;             // Reference ID hop failed
    const E_SOCIETY_INCOMPATIBLE: u64 = 6;     // Can't merge lily pads
    const E_ALREADY_LEAPED: u64 = 7;           // Double hop detected
    
    /// Trit values (the three stages of frog life)
    const TADPOLE: i8 = -1;    // MINUS: Learning, absorbing
    const FROGLET: i8 = 0;     // ERGODIC: Transitioning, coordinating  
    const FROG: i8 = 1;        // PLUS: Mature, generating
    
    // ════════════════════════════════════════════════════════════════════════
    // Core Types: The Frog Lifecycle
    // ════════════════════════════════════════════════════════════════════════
    
    /// Reference ID (RID) - Block Science KOI concept
    /// Enables orgs to refer to same referent in different ways
    struct ReferenceID has store, copy, drop {
        local_name: String,      // How THIS society refers to it
        canonical_hash: vector<u8>,  // Universal content hash
        society_origin: address,     // Which pond it came from
    }
    
    /// Knowledge Nugget - a piece of org knowledge (the frog to eat)
    struct KnowledgeNugget has store, copy, drop {
        rid: ReferenceID,
        content_type: String,    // "skill" | "concept" | "procedure"
        trit: i8,                // GF(3) lifecycle stage
        eaten: bool,             // Has this frog been eaten?
        eaten_by: address,       // Who ate it?
        leap_count: u64,         // How many hops to get here
    }
    
    /// Society - a knowledge network (the pond)
    struct Society has store, copy, drop {
        name: String,
        lily_pad_count: u64,     // Number of knowledge clusters
        frog_count: u64,         // Total knowledge nuggets
        tadpole_count: u64,      // MINUS knowledge (-1)
        froglet_count: u64,      // ERGODIC knowledge (0)
        mature_frog_count: u64,  // PLUS knowledge (+1)
        gf3_sum: i64,            // Should be ≡ 0 (mod 3)
        frogs_eaten: u64,        // Productivity metric
    }
    
    /// Merge Proposal - when two ponds want to connect
    struct MergeProposal has store, copy, drop {
        society_a: String,
        society_b: String,
        shared_rids: u64,        // Common reference points
        gf3_compatible: bool,    // Can merge without breaking balance
        leap_distance: u64,      // Hops between societies
        proposal_time: u64,
        ribbit_count: u64,       // Approval votes (croaks of assent)
    }
    
    /// Proof of Frog - the consensus mechanism
    struct ProofOfFrog has store, copy, drop {
        frog_hash: vector<u8>,   // Hash of the eaten frog
        eater: address,          // Who did the eating
        timestamp: u64,          // When the frog was eaten
        leap_proof: vector<u8>,  // Proof of valid hop
        trit_before: i8,         // Frog stage before eating
        trit_after: i8,          // Frog stage after (always +1 or cycles)
    }
    
    /// Main Pond State
    struct PondState has key {
        societies: vector<Society>,
        knowledge_pool: vector<KnowledgeNugget>,
        merge_proposals: vector<MergeProposal>,
        proofs: vector<ProofOfFrog>,
        total_leaps: u64,
        total_frogs_eaten: u64,
        pond_gf3_sum: i64,
        seed: u64,               // 1069 - the magic frog number
    }
    
    // ════════════════════════════════════════════════════════════════════════
    // Events: Ribbit Announcements
    // ════════════════════════════════════════════════════════════════════════
    
    #[event]
    struct FrogEatenEvent has drop, store {
        eater: address,
        frog_rid: vector<u8>,
        trit_change: i8,
        timestamp: u64,
        message: String,  // Always a frog pun
    }
    
    #[event]
    struct LeapEvent has drop, store {
        from_society: String,
        to_society: String,
        leap_distance: u64,
        frogs_transferred: u64,
        gf3_conserved: bool,
    }
    
    #[event]
    struct MergeEvent has drop, store {
        society_a: String,
        society_b: String,
        new_society: String,
        total_frogs: u64,
        total_lily_pads: u64,
        ribbit_message: String,
    }
    
    #[event]
    struct RibbitEvent has drop, store {
        croaker: address,
        message: String,
        volume: u64,  // How loud the ribbit
    }
    
    // ════════════════════════════════════════════════════════════════════════
    // Initialization: Spawn the Pond
    // ════════════════════════════════════════════════════════════════════════
    
    /// Initialize the pond with starter frogs
    public entry fun spawn_pond(account: &signer) {
        let societies = vector::empty<Society>();
        
        // Create the two Aptos Societies that will merge
        // Society A: The OG pond
        vector::push_back(&mut societies, Society {
            name: string::utf8(b"Aptos-Society-Alpha"),
            lily_pad_count: 7,
            frog_count: 21,
            tadpole_count: 7,      // 7 × (-1) = -7
            froglet_count: 7,      // 7 × (0) = 0
            mature_frog_count: 7,  // 7 × (+1) = +7
            gf3_sum: 0,            // -7 + 0 + 7 = 0 ✓ Toadally balanced!
            frogs_eaten: 0,
        });
        
        // Society B: The new pond to merge
        vector::push_back(&mut societies, Society {
            name: string::utf8(b"Aptos-Society-Beta"),
            lily_pad_count: 5,
            frog_count: 15,
            tadpole_count: 5,
            froglet_count: 5,
            mature_frog_count: 5,
            gf3_sum: 0,            // Also balanced!
            frogs_eaten: 0,
        });
        
        // Spawn initial knowledge nuggets (the frogs to eat)
        let knowledge_pool = vector::empty<KnowledgeNugget>();
        
        // Block Science KOI concepts as frogs
        vector::push_back(&mut knowledge_pool, create_frog(
            b"reference-id", b"RID", TADPOLE, @zubyul
        ));
        vector::push_back(&mut knowledge_pool, create_frog(
            b"cyborganization", b"concept", FROGLET, @zubyul
        ));
        vector::push_back(&mut knowledge_pool, create_frog(
            b"knowledge-network", b"concept", FROG, @zubyul
        ));
        
        // LPSCRYPT proof_chain concepts
        vector::push_back(&mut knowledge_pool, create_frog(
            b"kzg-commitment", b"procedure", TADPOLE, @zubyul
        ));
        vector::push_back(&mut knowledge_pool, create_frog(
            b"proof-chain", b"procedure", FROGLET, @zubyul
        ));
        vector::push_back(&mut knowledge_pool, create_frog(
            b"zk-snark", b"procedure", FROG, @zubyul
        ));
        
        // GF(3) balanced: 2×(-1) + 2×(0) + 2×(+1) = 0
        
        move_to(account, PondState {
            societies,
            knowledge_pool,
            merge_proposals: vector::empty(),
            proofs: vector::empty(),
            total_leaps: 0,
            total_frogs_eaten: 0,
            pond_gf3_sum: 0,
            seed: 1069,
        });
    }
    
    // ════════════════════════════════════════════════════════════════════════
    // Eat That Frog: The Core Consensus Action
    // ════════════════════════════════════════════════════════════════════════
    
    /// Eat a frog - process a knowledge nugget first thing
    /// "If you have to eat a frog, do it first thing in the morning"
    #[randomness]
    entry fun eat_frog(
        account: &signer,
        frog_index: u64
    ) acquires PondState {
        let state = borrow_global_mut<PondState>(@zubyul);
        let pool_len = vector::length(&state.knowledge_pool);
        
        assert!(frog_index < pool_len, E_POND_EMPTY);
        
        let frog = vector::borrow_mut(&mut state.knowledge_pool, frog_index);
        assert!(!frog.eaten, E_ALREADY_LEAPED);
        
        let eater = std::signer::address_of(account);
        let trit_before = frog.trit;
        
        // Eating advances the frog lifecycle (with wraparound)
        let trit_after = if (frog.trit == FROG) { TADPOLE } else { frog.trit + 1 };
        let trit_change = trit_after - trit_before;
        
        frog.eaten = true;
        frog.eaten_by = eater;
        frog.trit = trit_after;
        frog.leap_count = frog.leap_count + 1;
        
        // Update pond GF(3)
        state.pond_gf3_sum = state.pond_gf3_sum + (trit_change as i64);
        state.total_frogs_eaten = state.total_frogs_eaten + 1;
        
        // Create proof
        let frog_hash = hash::sha3_256(frog.rid.canonical_hash);
        let leap_proof = create_leap_proof(eater, frog_index, trit_before);
        
        vector::push_back(&mut state.proofs, ProofOfFrog {
            frog_hash,
            eater,
            timestamp: timestamp::now_microseconds(),
            leap_proof,
            trit_before,
            trit_after,
        });
        
        // Emit ribbit-ing event
        let pun = get_frog_pun(state.total_frogs_eaten);
        event::emit(FrogEatenEvent {
            eater,
            frog_rid: frog.rid.canonical_hash,
            trit_change,
            timestamp: timestamp::now_microseconds(),
            message: pun,
        });
    }
    
    // ════════════════════════════════════════════════════════════════════════
    // Society Merge: Two Ponds Become One
    // ════════════════════════════════════════════════════════════════════════
    
    /// Propose merging two societies (Block Science KOI style)
    /// "Hop-timistic about this merger!"
    public entry fun propose_merge(
        account: &signer,
        society_a_idx: u64,
        society_b_idx: u64
    ) acquires PondState {
        let state = borrow_global_mut<PondState>(@zubyul);
        
        let soc_a = vector::borrow(&state.societies, society_a_idx);
        let soc_b = vector::borrow(&state.societies, society_b_idx);
        
        // Check GF(3) compatibility
        let combined_gf3 = soc_a.gf3_sum + soc_b.gf3_sum;
        let gf3_compatible = (combined_gf3 % 3) == 0;
        
        // Calculate leap distance (knowledge graph hops)
        let leap_distance = if (soc_a.lily_pad_count > soc_b.lily_pad_count) {
            soc_a.lily_pad_count - soc_b.lily_pad_count
        } else {
            soc_b.lily_pad_count - soc_a.lily_pad_count
        };
        
        // Count shared RIDs (simplified - count by frog type overlap)
        let shared_rids = min_u64(soc_a.frog_count, soc_b.frog_count);
        
        vector::push_back(&mut state.merge_proposals, MergeProposal {
            society_a: soc_a.name,
            society_b: soc_b.name,
            shared_rids,
            gf3_compatible,
            leap_distance,
            proposal_time: timestamp::now_microseconds(),
            ribbit_count: 1,  // Proposer's ribbit
        });
    }
    
    /// Execute the merge - "Toadally awesome!"
    #[randomness]
    entry fun execute_merge(
        account: &signer,
        proposal_idx: u64
    ) acquires PondState {
        let state = borrow_global_mut<PondState>(@zubyul);
        
        let proposal = vector::borrow(&state.merge_proposals, proposal_idx);
        assert!(proposal.gf3_compatible, E_GF3_VIOLATION);
        
        // Find the societies
        let len = vector::length(&state.societies);
        let (a_idx, b_idx) = find_societies_by_name(
            &state.societies, 
            &proposal.society_a, 
            &proposal.society_b
        );
        
        let soc_a = vector::borrow(&state.societies, a_idx);
        let soc_b = vector::borrow(&state.societies, b_idx);
        
        // Create merged society
        let merged = Society {
            name: string::utf8(b"Aptos-Society-Merged-Pond"),
            lily_pad_count: soc_a.lily_pad_count + soc_b.lily_pad_count,
            frog_count: soc_a.frog_count + soc_b.frog_count,
            tadpole_count: soc_a.tadpole_count + soc_b.tadpole_count,
            froglet_count: soc_a.froglet_count + soc_b.froglet_count,
            mature_frog_count: soc_a.mature_frog_count + soc_b.mature_frog_count,
            gf3_sum: soc_a.gf3_sum + soc_b.gf3_sum,
            frogs_eaten: soc_a.frogs_eaten + soc_b.frogs_eaten,
        };
        
        // Record the leap
        state.total_leaps = state.total_leaps + proposal.leap_distance;
        
        event::emit(MergeEvent {
            society_a: proposal.society_a,
            society_b: proposal.society_b,
            new_society: merged.name,
            total_frogs: merged.frog_count,
            total_lily_pads: merged.lily_pad_count,
            ribbit_message: string::utf8(b"Toadally merged! Two ponds, one dream. 🐸"),
        });
        
        event::emit(LeapEvent {
            from_society: proposal.society_a,
            to_society: proposal.society_b,
            leap_distance: proposal.leap_distance,
            frogs_transferred: proposal.shared_rids,
            gf3_conserved: (merged.gf3_sum % 3) == 0,
        });
        
        // Add merged society
        vector::push_back(&mut state.societies, merged);
    }
    
    /// Cast a ribbit vote on a merge proposal
    public entry fun ribbit_vote(
        account: &signer,
        proposal_idx: u64,
        volume: u64
    ) acquires PondState {
        let state = borrow_global_mut<PondState>(@zubyul);
        let proposal = vector::borrow_mut(&mut state.merge_proposals, proposal_idx);
        
        proposal.ribbit_count = proposal.ribbit_count + 1;
        
        event::emit(RibbitEvent {
            croaker: std::signer::address_of(account),
            message: string::utf8(b"RIBBIT! I approve this merge! 🐸"),
            volume,
        });
    }
    
    // ════════════════════════════════════════════════════════════════════════
    // Helper Functions: Pond Utilities
    // ════════════════════════════════════════════════════════════════════════
    
    fun create_frog(
        name: vector<u8>,
        content_type: vector<u8>,
        trit: i8,
        origin: address
    ): KnowledgeNugget {
        let canonical = hash::sha3_256(name);
        
        KnowledgeNugget {
            rid: ReferenceID {
                local_name: string::utf8(name),
                canonical_hash: canonical,
                society_origin: origin,
            },
            content_type: string::utf8(content_type),
            trit,
            eaten: false,
            eaten_by: @0x0,
            leap_count: 0,
        }
    }
    
    fun create_leap_proof(eater: address, frog_idx: u64, trit: i8): vector<u8> {
        let data = vector::empty<u8>();
        
        // Pack eater address (simplified)
        let i = 0;
        while (i < 8) {
            vector::push_back(&mut data, 0u8);
            i = i + 1;
        };
        
        // Pack frog index
        let idx = frog_idx;
        i = 0;
        while (i < 8) {
            vector::push_back(&mut data, ((idx & 0xFF) as u8));
            idx = idx >> 8;
            i = i + 1;
        };
        
        // Pack trit
        vector::push_back(&mut data, ((trit + 2) as u8));
        
        hash::sha3_256(data)
    }
    
    fun get_frog_pun(count: u64): String {
        let puns = vector[
            b"Hop to it!",
            b"Toadally awesome!",
            b"Ribbit-ing progress!",
            b"Leap of faith!",
            b"Un-frog-ettable!",
            b"Pond-ering success!",
            b"Frog-tastic work!",
            b"Croak-worthy achievement!",
            b"Lily-pad landing!",
            b"Amphi-brilliant!",
        ];
        
        let idx = count % 10;
        string::utf8(*vector::borrow(&puns, idx))
    }
    
    fun find_societies_by_name(
        societies: &vector<Society>,
        name_a: &String,
        name_b: &String
    ): (u64, u64) {
        let len = vector::length(societies);
        let a_idx = 0u64;
        let b_idx = 0u64;
        
        let i = 0;
        while (i < len) {
            let soc = vector::borrow(societies, i);
            if (&soc.name == name_a) {
                a_idx = i;
            };
            if (&soc.name == name_b) {
                b_idx = i;
            };
            i = i + 1;
        };
        
        (a_idx, b_idx)
    }
    
    fun min_u64(a: u64, b: u64): u64 {
        if (a < b) { a } else { b }
    }
    
    // ════════════════════════════════════════════════════════════════════════
    // View Functions: Pond Inspection
    // ════════════════════════════════════════════════════════════════════════
    
    #[view]
    public fun get_pond_stats(): (u64, u64, u64, i64, bool) acquires PondState {
        let state = borrow_global<PondState>(@zubyul);
        let society_count = vector::length(&state.societies);
        let frog_count = vector::length(&state.knowledge_pool);
        let gf3_balanced = (state.pond_gf3_sum % 3) == 0;
        
        (society_count, frog_count, state.total_frogs_eaten, state.pond_gf3_sum, gf3_balanced)
    }
    
    #[view]
    public fun get_society(idx: u64): (String, u64, u64, i64) acquires PondState {
        let state = borrow_global<PondState>(@zubyul);
        let soc = vector::borrow(&state.societies, idx);
        (soc.name, soc.frog_count, soc.frogs_eaten, soc.gf3_sum)
    }
    
    #[view]
    public fun is_frog_eaten(idx: u64): bool acquires PondState {
        let state = borrow_global<PondState>(@zubyul);
        let frog = vector::borrow(&state.knowledge_pool, idx);
        frog.eaten
    }
    
    #[view]
    public fun get_merge_proposal_count(): u64 acquires PondState {
        vector::length(&borrow_global<PondState>(@zubyul).merge_proposals)
    }
    
    #[view]
    public fun verify_toadal_balance(): (bool, String) acquires PondState {
        let state = borrow_global<PondState>(@zubyul);
        let balanced = (state.pond_gf3_sum % 3) == 0;
        let msg = if (balanced) {
            string::utf8(b"Toadally balanced! GF(3) conserved. 🐸")
        } else {
            string::utf8(b"Unbalanced! Needs more tadpoles or mature frogs!")
        };
        (balanced, msg)
    }
}
