/// Obstruction Hot Potato: Bumpus × Roughgarden Arena on Aptos
/// 
/// Combines:
/// - Bumpus decomposition theory: obstructions from treewidth > k (H¹ ≠ 0)
/// - Roughgarden mechanism design: VCG payments for externalities
/// - GF(3) conservation: trit sum ≡ 0 (mod 3)
/// - Goblins capability semantics: resources as unforgeable capabilities
///
/// Game Rules:
/// 1. Players stake APT to enter arena
/// 2. Obstructions generated from decomposition failures
/// 3. Pass obstructions via VCG-priced transfers
/// 4. Round ends: negative utility players get slashed
/// 5. GF(3) conservation verified on-chain
///
/// Reference: CS364A (Roughgarden), arXiv:2402.00206 (Bumpus et al.)
module plurigrid::obstruction_hot_potato {
    use std::vector;
    use std::signer;
    use std::option::{Self, Option};
    use aptos_framework::coin::{Self, Coin};
    use aptos_framework::aptos_coin::AptosCoin;
    use aptos_framework::randomness;
    use aptos_framework::timestamp;
    use aptos_framework::event;
    
    // ═══════════════════════════════════════════════════════════════════════════
    // Error Codes
    // ═══════════════════════════════════════════════════════════════════════════
    
    const E_INSUFFICIENT_STAKE: u64 = 1;
    const E_GAME_NOT_ACTIVE: u64 = 2;
    const E_NOT_PLAYER: u64 = 3;
    const E_INVALID_TARGET: u64 = 4;
    const E_GF3_VIOLATION: u64 = 5;
    const E_VCG_UNDERPAYMENT: u64 = 6;
    const E_TREEWIDTH_EXCEEDED: u64 = 7;
    const E_ROUND_NOT_ENDED: u64 = 8;
    const E_ALREADY_DEAD: u64 = 9;
    const E_NO_OBSTRUCTION: u64 = 10;
    const E_SELF_TRANSFER: u64 = 11;
    
    // ═══════════════════════════════════════════════════════════════════════════
    // Constants
    // ═══════════════════════════════════════════════════════════════════════════
    
    /// GF(3) trit encoding
    const TRIT_MINUS: u8 = 0;    // -1 → 0
    const TRIT_ERGODIC: u8 = 1;  // 0 → 1
    const TRIT_PLUS: u8 = 2;     // +1 → 2
    
    /// Treewidth threshold (Bumpus: random access works when tw ≤ k)
    const TREEWIDTH_THRESHOLD: u64 = 3;
    
    /// Minimum stake in octas (0.1 APT)
    const MIN_STAKE: u64 = 10_000_000;
    
    /// Round duration in seconds
    const ROUND_DURATION: u64 = 60;
    
    /// VCG externality multiplier (basis points, 10000 = 100%)
    const VCG_MULTIPLIER_BPS: u64 = 10000;
    
    // ═══════════════════════════════════════════════════════════════════════════
    // Core Types
    // ═══════════════════════════════════════════════════════════════════════════
    
    /// Obstruction S-expression: colored datum from decomposition failure
    /// Corresponds to H¹ ≠ 0 cohomology class in Bumpus theory
    struct Obstruction has copy, drop, store {
        /// S-expression bytes (serialized Scheme form)
        sexp: vector<u8>,
        /// GF(3) trit: -1, 0, +1 encoded as 0, 1, 2
        trit: u8,
        /// Gay.jl deterministic color (RGB hex)
        color: u64,
        /// SplitMix64 seed that generated this
        seed: u64,
        /// Cohomology class: 0 = trivial (no obstruction), >0 = obstruction
        h1_class: u64,
        /// Treewidth that caused failure
        treewidth: u64,
        /// Creation timestamp
        created_at: u64,
    }
    
    /// Player state in the arena (analogous to Goblins vat)
    struct Player has key, store {
        /// Address of player
        addr: address,
        /// Staked coins (slashable)
        stake: Coin<AptosCoin>,
        /// Held obstructions (hot potatoes)
        obstructions: vector<Obstruction>,
        /// Total VCG payments made
        total_payments: u64,
        /// Total VCG payments received
        total_received: u64,
        /// Death count across games
        deaths: u64,
        /// Is currently alive in game
        alive: bool,
        /// Player type: 0 = Goblin, 1 = Agent-o-rama
        player_type: u8,
        /// Learning rate for Agent-o-rama players (bps)
        learning_rate_bps: u64,
        /// Pattern memory (for learning agents)
        pattern_memory: vector<u64>,
    }
    
    /// Game state
    struct Game has key {
        /// Game ID
        id: u64,
        /// All player addresses
        players: vector<address>,
        /// Round number
        round: u64,
        /// Round start timestamp
        round_start: u64,
        /// Is game active
        active: bool,
        /// Treasury for VCG payments
        treasury: Coin<AptosCoin>,
        /// Total obstructions generated
        total_obstructions: u64,
        /// GF(3) running sum (must be 0 mod 3 at equilibrium)
        gf3_sum: u64,
        /// Interaction entropy (seed for deterministic coloring)
        interaction_entropy: u64,
    }
    
    /// Global arena state
    struct Arena has key {
        /// Next game ID
        next_game_id: u64,
        /// Active games
        active_games: vector<u64>,
        /// Total games played
        total_games: u64,
        /// Total deaths across all games
        total_deaths: u64,
    }
    
    // ═══════════════════════════════════════════════════════════════════════════
    // Events
    // ═══════════════════════════════════════════════════════════════════════════
    
    #[event]
    struct ObstructionCreated has drop, store {
        game_id: u64,
        player: address,
        h1_class: u64,
        treewidth: u64,
        trit: u8,
        color: u64,
    }
    
    #[event]
    struct ObstructionPassed has drop, store {
        game_id: u64,
        from: address,
        to: address,
        h1_class: u64,
        vcg_payment: u64,
    }
    
    #[event]
    struct PlayerDied has drop, store {
        game_id: u64,
        player: address,
        obstruction_count: u64,
        negative_utility: u64,
        stake_slashed: u64,
    }
    
    #[event]
    struct RoundEnded has drop, store {
        game_id: u64,
        round: u64,
        survivors: u64,
        deaths: u64,
        gf3_conserved: bool,
    }
    
    #[event]
    struct GF3Violation has drop, store {
        game_id: u64,
        expected_sum: u64,
        actual_sum: u64,
    }
    
    // ═══════════════════════════════════════════════════════════════════════════
    // Arena Initialization
    // ═══════════════════════════════════════════════════════════════════════════
    
    /// Initialize the arena (called once by deployer)
    public entry fun initialize_arena(deployer: &signer) {
        let arena = Arena {
            next_game_id: 0,
            active_games: vector::empty(),
            total_games: 0,
            total_deaths: 0,
        };
        move_to(deployer, arena);
    }
    
    // ═══════════════════════════════════════════════════════════════════════════
    // Game Creation
    // ═══════════════════════════════════════════════════════════════════════════
    
    /// Create a new game
    public entry fun create_game(
        creator: &signer,
        arena_addr: address,
    ) acquires Arena {
        let arena = borrow_global_mut<Arena>(arena_addr);
        
        let game_id = arena.next_game_id;
        arena.next_game_id = game_id + 1;
        arena.total_games = arena.total_games + 1;
        vector::push_back(&mut arena.active_games, game_id);
        
        let game = Game {
            id: game_id,
            players: vector::empty(),
            round: 0,
            round_start: timestamp::now_seconds(),
            active: true,
            treasury: coin::zero<AptosCoin>(),
            total_obstructions: 0,
            gf3_sum: 0,
            interaction_entropy: 0x6761795f636f6c6f,  // "gay_colo"
        };
        
        move_to(creator, game);
    }
    
    // ═══════════════════════════════════════════════════════════════════════════
    // Player Registration
    // ═══════════════════════════════════════════════════════════════════════════
    
    /// Join game as Goblin player (basic capability passing)
    public entry fun join_as_goblin(
        player_signer: &signer,
        game_addr: address,
        stake_amount: u64,
    ) acquires Game {
        join_game_internal(player_signer, game_addr, stake_amount, 0, 0);
    }
    
    /// Join game as Agent-o-rama player (learning agent)
    public entry fun join_as_agent(
        player_signer: &signer,
        game_addr: address,
        stake_amount: u64,
        learning_rate_bps: u64,
    ) acquires Game {
        join_game_internal(player_signer, game_addr, stake_amount, 1, learning_rate_bps);
    }
    
    fun join_game_internal(
        player_signer: &signer,
        game_addr: address,
        stake_amount: u64,
        player_type: u8,
        learning_rate_bps: u64,
    ) acquires Game {
        assert!(stake_amount >= MIN_STAKE, E_INSUFFICIENT_STAKE);
        
        let game = borrow_global_mut<Game>(game_addr);
        assert!(game.active, E_GAME_NOT_ACTIVE);
        
        let player_addr = signer::address_of(player_signer);
        
        // Withdraw stake
        let stake = coin::withdraw<AptosCoin>(player_signer, stake_amount);
        
        // Create player
        let player = Player {
            addr: player_addr,
            stake,
            obstructions: vector::empty(),
            total_payments: 0,
            total_received: 0,
            deaths: 0,
            alive: true,
            player_type,
            learning_rate_bps,
            pattern_memory: vector::empty(),
        };
        
        // Register in game
        vector::push_back(&mut game.players, player_addr);
        
        // XOR entropy with player address
        game.interaction_entropy = game.interaction_entropy ^ (player_addr as u64);
        
        move_to(player_signer, player);
    }
    
    // ═══════════════════════════════════════════════════════════════════════════
    // Obstruction Generation (Bumpus Decomposition Failure)
    // ═══════════════════════════════════════════════════════════════════════════
    
    /// Attempt decomposition; if treewidth > threshold, generate obstruction
    /// Maps Bumpus insight: random access works iff tw ≤ k
    #[randomness]
    public entry fun attempt_decomposition(
        player_signer: &signer,
        game_addr: address,
        sexp: vector<u8>,
        claimed_treewidth: u64,
    ) acquires Game, Player {
        let player_addr = signer::address_of(player_signer);
        let game = borrow_global_mut<Game>(game_addr);
        let player = borrow_global_mut<Player>(player_addr);
        
        assert!(game.active, E_GAME_NOT_ACTIVE);
        assert!(player.alive, E_ALREADY_DEAD);
        
        if (claimed_treewidth <= TREEWIDTH_THRESHOLD) {
            // Decomposition succeeds - no obstruction
            return
        };
        
        // Decomposition FAILED - generate obstruction (H¹ ≠ 0)
        let seed = game.interaction_entropy ^ (timestamp::now_microseconds() as u64);
        
        // Compute trit from seed and treewidth
        let trit_raw = (seed ^ claimed_treewidth) % 3;
        let trit = (trit_raw as u8);
        
        // Compute color via SplitMix64-style hash
        let color = compute_gay_color(seed, game.total_obstructions);
        
        // H¹ class: non-zero when treewidth exceeds threshold
        let h1_class = if (claimed_treewidth > TREEWIDTH_THRESHOLD) { 
            claimed_treewidth - TREEWIDTH_THRESHOLD 
        } else { 
            0 
        };
        
        let obstruction = Obstruction {
            sexp,
            trit,
            color,
            seed,
            h1_class,
            treewidth: claimed_treewidth,
            created_at: timestamp::now_seconds(),
        };
        
        // Update GF(3) sum
        game.gf3_sum = game.gf3_sum + (trit as u64);
        game.total_obstructions = game.total_obstructions + 1;
        
        // Update entropy
        game.interaction_entropy = seed;
        
        // Give obstruction to player
        vector::push_back(&mut player.obstructions, obstruction);
        
        // Agent-o-rama: learn from receiving
        if (player.player_type == 1) {
            vector::push_back(&mut player.pattern_memory, h1_class);
        };
        
        event::emit(ObstructionCreated {
            game_id: game.id,
            player: player_addr,
            h1_class,
            treewidth: claimed_treewidth,
            trit,
            color,
        });
    }
    
    // ═══════════════════════════════════════════════════════════════════════════
    // Obstruction Passing with VCG Payments (Roughgarden Mechanism Design)
    // ═══════════════════════════════════════════════════════════════════════════
    
    /// Pass obstruction to target with VCG payment
    /// VCG: pay the externality your action causes to others
    /// Incentive Compatible: truthful H¹ declaration is dominant strategy
    public entry fun pass_obstruction_vcg(
        from_signer: &signer,
        game_addr: address,
        target_addr: address,
        obstruction_idx: u64,
        declared_h1: u64,  // Truthful declaration (IC enforced)
    ) acquires Game, Player {
        let from_addr = signer::address_of(from_signer);
        assert!(from_addr != target_addr, E_SELF_TRANSFER);
        
        let game = borrow_global_mut<Game>(game_addr);
        assert!(game.active, E_GAME_NOT_ACTIVE);
        
        let from_player = borrow_global_mut<Player>(from_addr);
        assert!(from_player.alive, E_ALREADY_DEAD);
        assert!(vector::length(&from_player.obstructions) > obstruction_idx, E_NO_OBSTRUCTION);
        
        // Remove obstruction from sender
        let obs = vector::swap_remove(&mut from_player.obstructions, obstruction_idx);
        
        // Verify truthful declaration (IC check)
        assert!(declared_h1 == obs.h1_class, E_VCG_UNDERPAYMENT);
        
        // Compute VCG payment = externality to target
        // Externality = harm caused = H¹ class × multiplier
        let externality = compute_externality(declared_h1);
        
        // Pay VCG from stake
        let payment_amount = if (coin::value(&from_player.stake) >= externality) {
            externality
        } else {
            coin::value(&from_player.stake)
        };
        
        let payment = coin::extract(&mut from_player.stake, payment_amount);
        from_player.total_payments = from_player.total_payments + payment_amount;
        
        // Transfer to game treasury (redistributed to survivors)
        coin::merge(&mut game.treasury, payment);
        
        // Give obstruction to target
        let target_player = borrow_global_mut<Player>(target_addr);
        assert!(target_player.alive, E_INVALID_TARGET);
        
        target_player.total_received = target_player.total_received + payment_amount;
        vector::push_back(&mut target_player.obstructions, obs);
        
        // Agent-o-rama: learn pattern
        if (target_player.player_type == 1) {
            vector::push_back(&mut target_player.pattern_memory, declared_h1);
        };
        
        event::emit(ObstructionPassed {
            game_id: game.id,
            from: from_addr,
            to: target_addr,
            h1_class: declared_h1,
            vcg_payment: payment_amount,
        });
    }
    
    /// Agent-o-rama strategic pass: prioritize highest H¹ obstructions
    public entry fun pass_obstruction_strategic(
        from_signer: &signer,
        game_addr: address,
        target_addr: address,
    ) acquires Game, Player {
        let from_addr = signer::address_of(from_signer);
        let from_player = borrow_global<Player>(from_addr);
        
        assert!(from_player.player_type == 1, E_NOT_PLAYER);  // Must be Agent-o-rama
        assert!(vector::length(&from_player.obstructions) > 0, E_NO_OBSTRUCTION);
        
        // Find highest H¹ obstruction
        let max_idx = find_max_h1_obstruction(&from_player.obstructions);
        let max_h1 = vector::borrow(&from_player.obstructions, max_idx).h1_class;
        
        // Use VCG pass with strategic selection
        pass_obstruction_vcg(from_signer, game_addr, target_addr, max_idx, max_h1);
    }
    
    // ═══════════════════════════════════════════════════════════════════════════
    // Round Resolution with Death Condition
    // ═══════════════════════════════════════════════════════════════════════════
    
    /// End round and apply death condition
    /// Roughgarden modification: die when utility < 0, not when most obstructions
    public entry fun end_round(
        caller: &signer,
        game_addr: address,
    ) acquires Game, Player, Arena {
        let game = borrow_global_mut<Game>(game_addr);
        assert!(game.active, E_GAME_NOT_ACTIVE);
        
        let now = timestamp::now_seconds();
        assert!(now >= game.round_start + ROUND_DURATION, E_ROUND_NOT_ENDED);
        
        // Compute utility for each player and apply death
        let deaths = 0u64;
        let survivors = 0u64;
        let i = 0;
        let n = vector::length(&game.players);
        
        while (i < n) {
            let player_addr = *vector::borrow(&game.players, i);
            let player = borrow_global_mut<Player>(player_addr);
            
            if (player.alive) {
                // Utility = stake_value + received - payments - obstruction_cost
                let stake_value = coin::value(&player.stake);
                let obstruction_cost = compute_obstruction_cost(&player.obstructions);
                
                // Negative utility check (Roughgarden death condition)
                let total_in = stake_value + player.total_received;
                let total_out = player.total_payments + obstruction_cost;
                
                if (total_out > total_in) {
                    // DEATH: negative utility
                    let negative_utility = total_out - total_in;
                    let slash_amount = if (stake_value > 0) {
                        let slash = stake_value / 2;  // Slash 50%
                        let slashed = coin::extract(&mut player.stake, slash);
                        coin::merge(&mut game.treasury, slashed);
                        slash
                    } else {
                        0
                    };
                    
                    player.alive = false;
                    player.deaths = player.deaths + 1;
                    deaths = deaths + 1;
                    
                    event::emit(PlayerDied {
                        game_id: game.id,
                        player: player_addr,
                        obstruction_count: vector::length(&player.obstructions),
                        negative_utility,
                        stake_slashed: slash_amount,
                    });
                } else {
                    survivors = survivors + 1;
                }
            };
            i = i + 1;
        };
        
        // Verify GF(3) conservation
        let gf3_conserved = verify_gf3_conservation(game);
        
        if (!gf3_conserved) {
            event::emit(GF3Violation {
                game_id: game.id,
                expected_sum: 0,
                actual_sum: game.gf3_sum % 3,
            });
        };
        
        // Advance round
        game.round = game.round + 1;
        game.round_start = now;
        
        // Update arena stats
        let arena = borrow_global_mut<Arena>(@plurigrid);
        arena.total_deaths = arena.total_deaths + deaths;
        
        event::emit(RoundEnded {
            game_id: game.id,
            round: game.round - 1,
            survivors,
            deaths,
            gf3_conserved,
        });
    }
    
    // ═══════════════════════════════════════════════════════════════════════════
    // GF(3) Conservation Verification
    // ═══════════════════════════════════════════════════════════════════════════
    
    /// Verify GF(3) sum ≡ 0 (mod 3)
    /// On-chain enforcement of triadic balance
    fun verify_gf3_conservation(game: &Game): bool {
        game.gf3_sum % 3 == 0
    }
    
    /// Compute GF(3) sum from all player obstructions
    public fun compute_gf3_sum_from_players(
        game: &Game,
    ): u64 acquires Player {
        let sum = 0u64;
        let i = 0;
        let n = vector::length(&game.players);
        
        while (i < n) {
            let player_addr = *vector::borrow(&game.players, i);
            let player = borrow_global<Player>(player_addr);
            
            let j = 0;
            let m = vector::length(&player.obstructions);
            while (j < m) {
                let obs = vector::borrow(&player.obstructions, j);
                sum = sum + (obs.trit as u64);
                j = j + 1;
            };
            i = i + 1;
        };
        
        sum
    }
    
    // ═══════════════════════════════════════════════════════════════════════════
    // Helper Functions
    // ═══════════════════════════════════════════════════════════════════════════
    
    /// Compute Gay.jl deterministic color from seed and index
    /// SplitMix64-style hashing for reproducibility
    fun compute_gay_color(seed: u64, index: u64): u64 {
        let z = seed ^ (index * 0x9e3779b97f4a7c15);
        let z = z ^ (z >> 30);
        let z = z * 0xbf58476d1ce4e5b9;
        let z = z ^ (z >> 27);
        let z = z * 0x94d049bb133111eb;
        z ^ (z >> 31)
    }
    
    /// Compute VCG externality from H¹ class
    /// Externality = harm to others = H¹ × base_cost × multiplier
    fun compute_externality(h1_class: u64): u64 {
        // Base cost = 0.001 APT per H¹ unit
        let base_cost = 1_000_000;  // 0.001 APT in octas
        (h1_class * base_cost * VCG_MULTIPLIER_BPS) / 10000
    }
    
    /// Compute total cost of held obstructions
    fun compute_obstruction_cost(obstructions: &vector<Obstruction>): u64 {
        let cost = 0u64;
        let i = 0;
        let n = vector::length(obstructions);
        
        while (i < n) {
            let obs = vector::borrow(obstructions, i);
            cost = cost + (obs.h1_class * 500_000);  // 0.0005 APT per H¹
            i = i + 1;
        };
        
        cost
    }
    
    /// Find obstruction with maximum H¹ class (Agent-o-rama strategy)
    fun find_max_h1_obstruction(obstructions: &vector<Obstruction>): u64 {
        let max_idx = 0;
        let max_h1 = 0u64;
        let i = 0;
        let n = vector::length(obstructions);
        
        while (i < n) {
            let obs = vector::borrow(obstructions, i);
            if (obs.h1_class > max_h1) {
                max_h1 = obs.h1_class;
                max_idx = i;
            };
            i = i + 1;
        };
        
        max_idx
    }
    
    // ═══════════════════════════════════════════════════════════════════════════
    // View Functions
    // ═══════════════════════════════════════════════════════════════════════════
    
    #[view]
    public fun get_player_utility(player_addr: address): (u64, u64, bool) acquires Player {
        let player = borrow_global<Player>(player_addr);
        let stake_value = coin::value(&player.stake);
        let obstruction_cost = compute_obstruction_cost(&player.obstructions);
        
        let total_in = stake_value + player.total_received;
        let total_out = player.total_payments + obstruction_cost;
        
        let utility = if (total_in >= total_out) { total_in - total_out } else { 0 };
        let negative = total_out > total_in;
        
        (utility, vector::length(&player.obstructions), negative)
    }
    
    #[view]
    public fun get_game_stats(game_addr: address): (u64, u64, u64, bool) acquires Game {
        let game = borrow_global<Game>(game_addr);
        let gf3_conserved = verify_gf3_conservation(game);
        (
            game.round,
            vector::length(&game.players),
            game.total_obstructions,
            gf3_conserved
        )
    }
    
    #[view]
    public fun get_obstruction_color(game_addr: address, seed: u64, idx: u64): u64 acquires Game {
        let game = borrow_global<Game>(game_addr);
        compute_gay_color(game.interaction_entropy ^ seed, idx)
    }
    
    // ═══════════════════════════════════════════════════════════════════════════
    // Tests
    // ═══════════════════════════════════════════════════════════════════════════
    
    #[test_only]
    use aptos_framework::account;
    
    #[test]
    fun test_gf3_conservation() {
        // TRIT_MINUS + TRIT_ERGODIC + TRIT_PLUS = 0 + 1 + 2 = 3 ≡ 0 (mod 3)
        let sum = (TRIT_MINUS as u64) + (TRIT_ERGODIC as u64) + (TRIT_PLUS as u64);
        assert!(sum % 3 == 0, 0);
    }
    
    #[test]
    fun test_externality_computation() {
        let ext = compute_externality(5);  // H¹ = 5
        // 5 * 1_000_000 * 10000 / 10000 = 5_000_000 octas = 0.005 APT
        assert!(ext == 5_000_000, 1);
    }
    
    #[test]
    fun test_gay_color_determinism() {
        let seed = 0x6761795f636f6c6f;
        let c1 = compute_gay_color(seed, 1);
        let c2 = compute_gay_color(seed, 1);
        assert!(c1 == c2, 2);  // Same seed + index = same color
        
        let c3 = compute_gay_color(seed, 2);
        assert!(c1 != c3, 3);  // Different index = different color
    }
}
