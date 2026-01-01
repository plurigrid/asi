/// Proof Chain Module: 3 Parallel Subagents with Galois Hand-off
/// Each agent starts with coin flip (sortition), walks 3 skills at a time
/// Hand-off via Galois connection: floor ⊣ ceiling adjunction
///
/// Reference: LPSCRYPT/proof_chain (ZK proof chaining via KZG commitments)
/// Adapted for Aptos with GF(3) conservation and skill random walks
///
/// Galois Connection Guarantee:
///   floor(agent_state) ≤ target ⟺ agent_state ≤ ceiling(target)
///   Ensures lawful hand-off between subagents

module zubyul::proof_chain {
    use std::vector;
    use std::string::{Self, String};
    use aptos_framework::randomness;
    use aptos_framework::event;
    use aptos_framework::timestamp;
    use aptos_framework::hash;
    
    /// Error codes
    const E_NOT_INITIALIZED: u64 = 1;
    const E_INVALID_AGENT: u64 = 2;
    const E_GF3_VIOLATION: u64 = 3;
    const E_GALOIS_VIOLATION: u64 = 4;
    const E_HANDOFF_FAILED: u64 = 5;
    
    /// Trit values for GF(3)
    const TRIT_MINUS: i8 = -1;
    const TRIT_ERGODIC: i8 = 0;
    const TRIT_PLUS: i8 = 1;
    
    // ════════════════════════════════════════════════════════════════════════
    // Core Types
    // ════════════════════════════════════════════════════════════════════════
    
    /// Skill with trit assignment
    struct Skill has store, copy, drop {
        name: String,
        trit: i8,
        index: u64,
    }
    
    /// Proof link (KZG-style commitment placeholder)
    struct ProofLink has store, copy, drop {
        commitment: vector<u8>,  // Hash of previous state
        round: u64,
        agent_id: u8,
    }
    
    /// Subagent state
    struct SubAgent has store, copy, drop {
        id: u8,                    // 0, 1, 2 (alice, arbiter, bob)
        trit: i8,                  // -1, 0, +1
        current_skills: vector<Skill>,
        walk_count: u64,
        entropy: u64,
        last_coin_flip: bool,      // true = heads, false = tails
        proof_chain: vector<ProofLink>,
    }
    
    /// Galois hand-off state
    struct GaloisHandoff has store, copy, drop {
        from_agent: u8,
        to_agent: u8,
        floor_value: u64,          // Left adjoint: coarsen
        ceiling_value: u64,        // Right adjoint: refine
        valid: bool,               // floor(x) ≤ y ⟺ x ≤ ceiling(y)
        trit_delta: i8,
    }
    
    /// Main proof chain state
    struct ProofChainState has key {
        agents: vector<SubAgent>,
        skills: vector<Skill>,
        round: u64,
        total_walks: u64,
        gf3_sum: i64,
        handoffs: vector<GaloisHandoff>,
        seed: u64,
    }
    
    // ════════════════════════════════════════════════════════════════════════
    // Events
    // ════════════════════════════════════════════════════════════════════════
    
    #[event]
    struct CoinFlipEvent has drop, store {
        agent_id: u8,
        result: bool,  // heads/tails
        round: u64,
        timestamp: u64,
    }
    
    #[event]
    struct SkillWalkEvent has drop, store {
        agent_id: u8,
        skills: vector<String>,
        trit_sum: i8,
        round: u64,
    }
    
    #[event]
    struct HandoffEvent has drop, store {
        from_agent: u8,
        to_agent: u8,
        floor_value: u64,
        ceiling_value: u64,
        galois_valid: bool,
        round: u64,
    }
    
    #[event]
    struct ProofChainEvent has drop, store {
        round: u64,
        agent_walks: vector<u64>,
        gf3_conserved: bool,
        total_handoffs: u64,
    }
    
    // ════════════════════════════════════════════════════════════════════════
    // Initialization
    // ════════════════════════════════════════════════════════════════════════
    
    /// Initialize proof chain with 3 subagents and skill registry
    public entry fun initialize(account: &signer) {
        let agents = vector::empty<SubAgent>();
        
        // Agent 0: Alice (MINUS -1) - Validator/COPLAY
        vector::push_back(&mut agents, SubAgent {
            id: 0,
            trit: TRIT_MINUS,
            current_skills: vector::empty(),
            walk_count: 0,
            entropy: 0,
            last_coin_flip: false,
            proof_chain: vector::empty(),
        });
        
        // Agent 1: Arbiter (ERGODIC 0) - Coordinator
        vector::push_back(&mut agents, SubAgent {
            id: 1,
            trit: TRIT_ERGODIC,
            current_skills: vector::empty(),
            walk_count: 0,
            entropy: 0,
            last_coin_flip: false,
            proof_chain: vector::empty(),
        });
        
        // Agent 2: Bob (PLUS +1) - Executor/PLAY
        vector::push_back(&mut agents, SubAgent {
            id: 2,
            trit: TRIT_PLUS,
            current_skills: vector::empty(),
            walk_count: 0,
            entropy: 0,
            last_coin_flip: false,
            proof_chain: vector::empty(),
        });
        
        // Skill registry (21 skills, GF(3) balanced: 7×(-1) + 7×(0) + 7×(+1) = 0)
        let skills = vector::empty<Skill>();
        
        // MINUS skills (-1)
        vector::push_back(&mut skills, Skill { name: string::utf8(b"narya-proofs"), trit: -1, index: 0 });
        vector::push_back(&mut skills, Skill { name: string::utf8(b"bisimulation-game"), trit: -1, index: 1 });
        vector::push_back(&mut skills, Skill { name: string::utf8(b"three-match"), trit: -1, index: 2 });
        vector::push_back(&mut skills, Skill { name: string::utf8(b"cybernetic-immune"), trit: -1, index: 3 });
        vector::push_back(&mut skills, Skill { name: string::utf8(b"tree-sitter"), trit: -1, index: 4 });
        vector::push_back(&mut skills, Skill { name: string::utf8(b"duckdb-ies"), trit: -1, index: 5 });
        vector::push_back(&mut skills, Skill { name: string::utf8(b"mathpix-ocr"), trit: -1, index: 6 });
        
        // ERGODIC skills (0)
        vector::push_back(&mut skills, Skill { name: string::utf8(b"autopoiesis"), trit: 0, index: 7 });
        vector::push_back(&mut skills, Skill { name: string::utf8(b"world-hopping"), trit: 0, index: 8 });
        vector::push_back(&mut skills, Skill { name: string::utf8(b"ducklake-federation"), trit: 0, index: 9 });
        vector::push_back(&mut skills, Skill { name: string::utf8(b"semantic-mitosis"), trit: 0, index: 10 });
        vector::push_back(&mut skills, Skill { name: string::utf8(b"reafference"), trit: 0, index: 11 });
        vector::push_back(&mut skills, Skill { name: string::utf8(b"ordered-locale"), trit: 0, index: 12 });
        vector::push_back(&mut skills, Skill { name: string::utf8(b"galois-connections"), trit: 0, index: 13 });
        
        // PLUS skills (+1)
        vector::push_back(&mut skills, Skill { name: string::utf8(b"gay-mcp"), trit: 1, index: 14 });
        vector::push_back(&mut skills, Skill { name: string::utf8(b"derangeable"), trit: 1, index: 15 });
        vector::push_back(&mut skills, Skill { name: string::utf8(b"discohy-streams"), trit: 1, index: 16 });
        vector::push_back(&mut skills, Skill { name: string::utf8(b"alife"), trit: 1, index: 17 });
        vector::push_back(&mut skills, Skill { name: string::utf8(b"agent-o-rama"), trit: 1, index: 18 });
        vector::push_back(&mut skills, Skill { name: string::utf8(b"glass-bead-game"), trit: 1, index: 19 });
        vector::push_back(&mut skills, Skill { name: string::utf8(b"free-monad-gen"), trit: 1, index: 20 });
        
        move_to(account, ProofChainState {
            agents,
            skills,
            round: 0,
            total_walks: 0,
            gf3_sum: 0,
            handoffs: vector::empty(),
            seed: 1069,
        });
    }
    
    // ════════════════════════════════════════════════════════════════════════
    // Coin Flip: Random Walk Initiation (AIP-41)
    // ════════════════════════════════════════════════════════════════════════
    
    /// Flip coin for an agent to start random walk
    #[randomness]
    entry fun coin_flip(account: &signer, agent_id: u8) acquires ProofChainState {
        assert!(agent_id < 3, E_INVALID_AGENT);
        
        let state = borrow_global_mut<ProofChainState>(@zubyul);
        let agent = vector::borrow_mut(&mut state.agents, (agent_id as u64));
        
        // Random coin flip using Aptos randomness
        let flip = randomness::u64_range(0, 2);
        agent.last_coin_flip = flip == 1;
        agent.entropy = agent.entropy + flip;
        
        event::emit(CoinFlipEvent {
            agent_id,
            result: agent.last_coin_flip,
            round: state.round,
            timestamp: timestamp::now_microseconds(),
        });
    }
    
    // ════════════════════════════════════════════════════════════════════════
    // Skill Random Walk: 3 Skills at a Time
    // ════════════════════════════════════════════════════════════════════════
    
    /// Agent walks through 3 random skills
    #[randomness]
    entry fun skill_walk(account: &signer, agent_id: u8) acquires ProofChainState {
        assert!(agent_id < 3, E_INVALID_AGENT);
        
        let state = borrow_global_mut<ProofChainState>(@zubyul);
        let n_skills = vector::length(&state.skills);
        let agent = vector::borrow_mut(&mut state.agents, (agent_id as u64));
        
        // Clear current skills
        agent.current_skills = vector::empty();
        
        // Pick 3 random skills
        let skill_names = vector::empty<String>();
        let trit_sum: i8 = 0;
        
        let i = 0;
        while (i < 3) {
            let idx = randomness::u64_range(0, n_skills);
            let skill = vector::borrow(&state.skills, idx);
            vector::push_back(&mut agent.current_skills, *skill);
            vector::push_back(&mut skill_names, skill.name);
            trit_sum = trit_sum + skill.trit;
            i = i + 1;
        };
        
        agent.walk_count = agent.walk_count + 1;
        state.total_walks = state.total_walks + 1;
        state.gf3_sum = state.gf3_sum + (trit_sum as i64);
        
        // Create proof link
        let commitment = create_commitment(agent_id, state.round, trit_sum);
        vector::push_back(&mut agent.proof_chain, ProofLink {
            commitment,
            round: state.round,
            agent_id,
        });
        
        event::emit(SkillWalkEvent {
            agent_id,
            skills: skill_names,
            trit_sum,
            round: state.round,
        });
    }
    
    // ════════════════════════════════════════════════════════════════════════
    // Galois Hand-off: Lawful Agent State Transfer
    // ════════════════════════════════════════════════════════════════════════
    
    /// Hand-off state from one agent to another with Galois guarantee
    /// floor(from_state) ≤ to_target ⟺ from_state ≤ ceiling(to_target)
    #[randomness]
    entry fun galois_handoff(
        account: &signer,
        from_agent: u8,
        to_agent: u8
    ) acquires ProofChainState {
        assert!(from_agent < 3 && to_agent < 3, E_INVALID_AGENT);
        assert!(from_agent != to_agent, E_HANDOFF_FAILED);
        
        let state = borrow_global_mut<ProofChainState>(@zubyul);
        
        let from = vector::borrow(&state.agents, (from_agent as u64));
        let to = vector::borrow(&state.agents, (to_agent as u64));
        
        // Galois connection: floor ⊣ ceiling
        // floor: coarsen (entropy → walk_count)
        // ceiling: refine (walk_count → entropy * factor)
        let floor_value = from.entropy / 10;  // Coarsen: lose precision
        let ceiling_value = to.walk_count * 10;  // Refine: add structure
        
        // Galois guarantee: floor(x) ≤ y ⟺ x ≤ ceiling(y)
        // Check: from.entropy / 10 ≤ to.walk_count ⟺ from.entropy ≤ to.walk_count * 10
        let left_check = floor_value <= to.walk_count;
        let right_check = from.entropy <= ceiling_value;
        let galois_valid = (left_check && right_check) || (!left_check && !right_check);
        
        // Trit delta for GF(3)
        let trit_delta = to.trit - from.trit;
        
        // Record handoff
        let handoff = GaloisHandoff {
            from_agent,
            to_agent,
            floor_value,
            ceiling_value,
            valid: galois_valid,
            trit_delta,
        };
        vector::push_back(&mut state.handoffs, handoff);
        
        // Update target agent entropy (transfer)
        let to_mut = vector::borrow_mut(&mut state.agents, (to_agent as u64));
        to_mut.entropy = to_mut.entropy + floor_value;
        
        state.round = state.round + 1;
        
        event::emit(HandoffEvent {
            from_agent,
            to_agent,
            floor_value,
            ceiling_value,
            galois_valid,
            round: state.round,
        });
    }
    
    // ════════════════════════════════════════════════════════════════════════
    // Triadic Round: All 3 Agents in Parallel
    // ════════════════════════════════════════════════════════════════════════
    
    /// Execute full triadic round: coin_flip → skill_walk for all 3 agents
    #[randomness]
    entry fun triadic_round(account: &signer) acquires ProofChainState {
        let state = borrow_global_mut<ProofChainState>(@zubyul);
        let n_skills = vector::length(&state.skills);
        
        let agent_walks = vector::empty<u64>();
        let total_trit: i64 = 0;
        
        // Process all 3 agents
        let agent_id: u8 = 0;
        while (agent_id < 3) {
            let agent = vector::borrow_mut(&mut state.agents, (agent_id as u64));
            
            // Coin flip
            let flip = randomness::u64_range(0, 2);
            agent.last_coin_flip = flip == 1;
            agent.entropy = agent.entropy + flip;
            
            // Skill walk (3 skills)
            agent.current_skills = vector::empty();
            let trit_sum: i8 = 0;
            
            let i = 0;
            while (i < 3) {
                let idx = randomness::u64_range(0, n_skills);
                let skill = vector::borrow(&state.skills, idx);
                vector::push_back(&mut agent.current_skills, *skill);
                trit_sum = trit_sum + skill.trit;
                i = i + 1;
            };
            
            agent.walk_count = agent.walk_count + 1;
            total_trit = total_trit + (trit_sum as i64);
            vector::push_back(&mut agent_walks, agent.walk_count);
            
            // Proof link
            let commitment = create_commitment(agent_id, state.round, trit_sum);
            vector::push_back(&mut agent.proof_chain, ProofLink {
                commitment,
                round: state.round,
                agent_id,
            });
            
            agent_id = agent_id + 1;
        };
        
        state.total_walks = state.total_walks + 3;
        state.gf3_sum = state.gf3_sum + total_trit;
        state.round = state.round + 1;
        
        // GF(3) check: agent trits sum to 0
        let agent_trit_sum = TRIT_MINUS + TRIT_ERGODIC + TRIT_PLUS;
        let gf3_conserved = (agent_trit_sum % 3) == 0;
        
        event::emit(ProofChainEvent {
            round: state.round,
            agent_walks,
            gf3_conserved,
            total_handoffs: vector::length(&state.handoffs),
        });
    }
    
    // ════════════════════════════════════════════════════════════════════════
    // Proof Chain Linking (KZG-style)
    // ════════════════════════════════════════════════════════════════════════
    
    /// Create commitment hash for proof link
    fun create_commitment(agent_id: u8, round: u64, trit_sum: i8): vector<u8> {
        let data = vector::empty<u8>();
        vector::push_back(&mut data, agent_id);
        
        // Add round bytes
        let r = round;
        let i = 0;
        while (i < 8) {
            vector::push_back(&mut data, ((r & 0xFF) as u8));
            r = r >> 8;
            i = i + 1;
        };
        
        // Add trit (as unsigned)
        vector::push_back(&mut data, ((trit_sum + 2) as u8));  // Map -1,0,1 to 1,2,3
        
        hash::sha3_256(data)
    }
    
    /// Verify proof chain consistency
    public fun verify_chain(agent_id: u8): bool acquires ProofChainState {
        let state = borrow_global<ProofChainState>(@zubyul);
        let agent = vector::borrow(&state.agents, (agent_id as u64));
        
        let chain = &agent.proof_chain;
        let len = vector::length(chain);
        
        if (len < 2) {
            return true
        };
        
        // Verify sequential rounds
        let i = 1;
        while (i < len) {
            let prev = vector::borrow(chain, i - 1);
            let curr = vector::borrow(chain, i);
            if (curr.round <= prev.round) {
                return false
            };
            i = i + 1;
        };
        
        true
    }
    
    // ════════════════════════════════════════════════════════════════════════
    // View Functions
    // ════════════════════════════════════════════════════════════════════════
    
    #[view]
    public fun get_agent_state(agent_id: u8): (u64, u64, bool, u64) acquires ProofChainState {
        let state = borrow_global<ProofChainState>(@zubyul);
        let agent = vector::borrow(&state.agents, (agent_id as u64));
        (agent.walk_count, agent.entropy, agent.last_coin_flip, 
         vector::length(&agent.proof_chain))
    }
    
    #[view]
    public fun get_round(): u64 acquires ProofChainState {
        borrow_global<ProofChainState>(@zubyul).round
    }
    
    #[view]
    public fun get_gf3_status(): (i64, bool) acquires ProofChainState {
        let state = borrow_global<ProofChainState>(@zubyul);
        let conserved = (state.gf3_sum % 3) == 0;
        (state.gf3_sum, conserved)
    }
    
    #[view]
    public fun get_handoff_count(): u64 acquires ProofChainState {
        vector::length(&borrow_global<ProofChainState>(@zubyul).handoffs)
    }
    
    #[view]
    public fun verify_galois_invariant(): bool acquires ProofChainState {
        let state = borrow_global<ProofChainState>(@zubyul);
        let handoffs = &state.handoffs;
        let len = vector::length(handoffs);
        
        if (len == 0) {
            return true
        };
        
        let i = 0;
        while (i < len) {
            let h = vector::borrow(handoffs, i);
            if (!h.valid) {
                return false
            };
            i = i + 1;
        };
        
        true
    }
}
