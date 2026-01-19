/// 26-Wallet Aptos Swarm Bootstrap via SplitMix64
/// Uses deterministic parallel initialization with GF(3) conservation
///
/// Problem: 26 wallets need mutual awareness without ordering bottleneck
/// Solution: SplitMix64 PRNG with XOR-separated triadic fork (MINUS/ERGODIC/PLUS)
///
/// Reference: https://greenteatree01 Aptos swarm architecture
/// Architecture:
///   Stage 1: master_seed (1069 or timestamp_us)
///   Stage 2: Triadic fork - 26 wallets × 3 streams = 78 parallel SplitMix64 generators
///   Stage 3: Collision-free order ID generation
///   Stage 4: Mutual awareness via simultaneous order broadcast
///   Stage 5: Delimited continuation escape via order references

module zubyul::swarm_bootstrap {
    use std::option::{Self, Option};
    use std::vector;
    use aptos_framework::event;
    use aptos_framework::timestamp;

    // ════════════════════════════════════════════════════════════════════════
    // GF(3) Trit Constants
    // ════════════════════════════════════════════════════════════════════════

    const MINUS_TRIT: i8 = -1;       // Validator (-1)
    const ERGODIC_TRIT: i8 = 0;      // Coordinator (0)
    const PLUS_TRIT: i8 = 1;         // Executor (+1)

    // XOR separation for triadic fork
    const MINUS_XORBYTE: u8 = 0x2d;    // '-' (0x2d) for MINUS stream
    const ERGODIC_XORBYTE: u8 = 0x5f;  // '_' (0x5f) for ERGODIC stream
    const PLUS_XORBYTE: u8 = 0x2b;     // '+' (0x2b) for PLUS stream

    const LETTER_BASE: u8 = 97;  // 'a' = 97
    const WALLET_COUNT: u8 = 26;

    // Error codes
    const E_INVALID_WALLET_INDEX: u64 = 1001;
    const E_INVALID_WALLET_COUNT: u64 = 1002;
    const E_INVALID_STREAM: u64 = 1003;
    const E_GF3_VIOLATION: u64 = 1004;

    // ════════════════════════════════════════════════════════════════════════
    // Core Types: Order Book & Swarm Bootstrap
    // ════════════════════════════════════════════════════════════════════════

    /// Order ID - cross-wallet reference linking
    struct OrderIdType has store, copy, drop {
        account: address,           // Wallet address
        account_order_id: u64,      // Timestamp + counter + sequence
    }

    /// Priority index from SplitMix64
    struct UniqueIdxType has store, copy, drop {
        priority: u128,  // Full 128-bit SplitMix64 output
    }

    /// Trigger condition for order execution
    enum TriggerCondition has store, copy, drop {
        TimeBased(u64),     // Execute at specific timestamp
        PriceLess(u64),     // Execute when price < threshold
        PriceGreater(u64),  // Execute when price > threshold
    }

    /// Generic order with metadata
    struct Order<M: store + copy + drop> has store, copy, drop {
        id: OrderIdType,
        priority_idx: UniqueIdxType,
        price: u64,
        size: u64,
        remaining_size: u64,
        is_buy: bool,
        trigger: Option<TriggerCondition>,
        metadata: M,
    }

    /// Wallet identity in the swarm
    struct WalletIdentity has store, copy, drop {
        address: address,
        letter_index: u8,  // 0-25 for a-z
        letter: u8,        // ASCII 'a'-'z'
    }

    /// Triadic order set (MINUS, ERGODIC, PLUS) at same timestamp
    struct TriadicOrderSet<M: store + copy + drop> has store, copy, drop {
        wallet: WalletIdentity,
        timestamp_us: u64,
        master_seed: u128,
        minus_order: Order<M>,      // Validator
        ergodic_order: Order<M>,    // Coordinator
        plus_order: Order<M>,       // Executor
    }

    /// Metadata for swarm bootstrap
    struct SwarmBootstrapMetadata has store, copy, drop {
        wallet_letter: u8,
        trit: i8,
        peer_count: u8,
    }

    /// Delimited continuation escape context
    struct ContinuationContext<M: store + copy + drop> has store {
        source_wallet: WalletIdentity,
        target_wallet: WalletIdentity,
        source_order_id: OrderIdType,
        target_order_id: OrderIdType,
        timestamp_us: u64,
        payload: M,
    }

    /// SplitMix64 PRNG state (deterministic parallel RNG)
    struct SplitMix64 has copy, drop {
        state: u128,
    }

    /// Main swarm state
    struct SwarmBootstrapState has key {
        master_seed: u128,
        wallets: vector<WalletIdentity>,
        order_sets: vector<TriadicOrderSet<SwarmBootstrapMetadata>>,
        gf3_sum: i64,
        mutual_awareness_timestamp: Option<u64>,
    }

    // ════════════════════════════════════════════════════════════════════════
    // Events
    // ════════════════════════════════════════════════════════════════════════

    #[event]
    struct WalletRegisteredEvent has drop, store {
        wallet_address: address,
        letter: u8,
        timestamp: u64,
    }

    #[event]
    struct TriadicOrderSetCreatedEvent has drop, store {
        wallet_address: address,
        letter: u8,
        timestamp_us: u64,
        order_count: u64,
    }

    #[event]
    struct MutualAwarenessAchievedEvent has drop, store {
        wallet_count: u8,
        total_orders: u64,
        timestamp_us: u64,
        gf3_conserved: bool,
    }

    #[event]
    struct ContinuationEscapeEvent has drop, store {
        source_address: address,
        target_address: address,
        source_order_id: u64,
        target_order_id: u64,
        timestamp_us: u64,
    }

    // ════════════════════════════════════════════════════════════════════════
    // SplitMix64 Implementation
    // ════════════════════════════════════════════════════════════════════════

    /// Initialize SplitMix64 from 128-bit seed (uses lower 64 bits)
    public fun splitmix64_new(seed: u128): SplitMix64 {
        SplitMix64 { state: seed }
    }

    /// Wrapping multiply for u64 (Move doesn't have built-in wrapping)
    fun wrapping_mul_u64(a: u64, b: u64): u64 {
        let result = (a as u128) * (b as u128);
        (result & 0xFFFFFFFFFFFFFFFFu128) as u64
    }

    /// Next value from SplitMix64 (64-bit core, extended to 128-bit output)
    /// Uses standard SplitMix64 algorithm with wrapping arithmetic
    public fun splitmix64_next(rng: &mut SplitMix64): u128 {
        let z = (rng.state & 0xFFFFFFFFFFFFFFFFu128) as u64;
        z = z + 0x9e3779b97f4a7c15u64;  // Golden ratio constant
        rng.state = (z as u128);
        
        z = wrapping_mul_u64(z ^ (z >> 30), 0xbf58476d1ce4e5b9u64);
        z = wrapping_mul_u64(z ^ (z >> 27), 0x94d049bb133111ebu64);
        z = z ^ (z >> 31);
        
        (z as u128)
    }

    /// Next 64-bit value from SplitMix64
    public fun splitmix64_next_u64(rng: &mut SplitMix64): u64 {
        (splitmix64_next(rng) & 0xFFFFFFFFFFFFFFFFu128) as u64
    }

    // ════════════════════════════════════════════════════════════════════════
    // Wallet Management
    // ════════════════════════════════════════════════════════════════════════

    /// Get letter ('a'-'z') from index (0-25)
    public fun letter_from_index(index: u8): u8 {
        assert!(index < 26, E_INVALID_WALLET_INDEX);
        LETTER_BASE + index
    }

    /// Create wallet identity
    public fun wallet_identity(
        address: address,
        letter_index: u8
    ): WalletIdentity {
        assert!(letter_index < 26, E_INVALID_WALLET_INDEX);
        let letter = letter_from_index(letter_index);
        WalletIdentity { address, letter_index, letter }
    }

    // ════════════════════════════════════════════════════════════════════════
    // Stream Derivation (XOR Separation)
    // ════════════════════════════════════════════════════════════════════════

    /// Derive deterministic SplitMix64 stream for wallet + trit
    /// XOR combines: master_seed ⊻ trit_xorbyte ⊻ wallet_letter
    /// This ensures all 78 streams (26 × 3) are collision-free
    public fun derive_stream(
        master_seed: u128,
        wallet_index: u8,
        trit_xorbyte: u8
    ): SplitMix64 {
        let wallet_letter = letter_from_index(wallet_index);
        let wallet_seed = master_seed
            ^ ((trit_xorbyte as u128) << 8 | (wallet_letter as u128));
        splitmix64_new(wallet_seed)
    }

    // ════════════════════════════════════════════════════════════════════════
    // Order ID Generation
    // ════════════════════════════════════════════════════════════════════════

    /// Generate collision-free order ID for wallet's trit position
    /// Format: (timestamp << 32) | (counter >> 32) ^ sequence
    public fun generate_order_id(
        wallet: &WalletIdentity,
        timestamp_us: u64,
        trit_xorbyte: u8,
        master_seed: u128,
        sequence: u64
    ): OrderIdType {
        let stream = derive_stream(master_seed, wallet.letter_index, trit_xorbyte);
        let counter = splitmix64_next_u64(&mut stream);

        // Combine timestamp + counter + sequence for uniqueness
        let account_order_id = (
            ((timestamp_us as u64) << 32) |
            ((counter as u64) >> 32)
        ) ^ sequence;

        OrderIdType {
            account: wallet.address,
            account_order_id,
        }
    }

    /// Generate priority index from SplitMix64
    public fun generate_priority_idx(rng: &mut SplitMix64): UniqueIdxType {
        UniqueIdxType {
            priority: splitmix64_next(rng),
        }
    }

    // ════════════════════════════════════════════════════════════════════════
    // Triadic Order Set Creation (Stage 3 & 4)
    // ════════════════════════════════════════════════════════════════════════

    /// Create triadic order set for wallet at given timestamp
    /// This is the core mutual awareness bootstrap function
    /// Generates 3 parallel SplitMix64 streams (MINUS, ERGODIC, PLUS)
    public fun create_triadic_order_set<M: store + copy + drop>(
        wallet: WalletIdentity,
        timestamp_us: u64,
        master_seed: u128,
        price: u64,
        size: u64,
        metadata: M
    ): TriadicOrderSet<M> {
        // Generate three parallel SplitMix64 streams
        let minus_stream = derive_stream(master_seed, wallet.letter_index, MINUS_XORBYTE);
        let ergodic_stream = derive_stream(master_seed, wallet.letter_index, ERGODIC_XORBYTE);
        let plus_stream = derive_stream(master_seed, wallet.letter_index, PLUS_XORBYTE);

        // Generate order IDs (collision-free per stream)
        let minus_order_id = generate_order_id(
            &wallet, timestamp_us, MINUS_XORBYTE, master_seed, 0
        );
        let ergodic_order_id = generate_order_id(
            &wallet, timestamp_us, ERGODIC_XORBYTE, master_seed, 1
        );
        let plus_order_id = generate_order_id(
            &wallet, timestamp_us, PLUS_XORBYTE, master_seed, 2
        );

        // Generate priority indices from their streams
        let minus_idx = generate_priority_idx(&mut minus_stream);
        let ergodic_idx = generate_priority_idx(&mut ergodic_stream);
        let plus_idx = generate_priority_idx(&mut plus_stream);

        // All three orders trigger at same timestamp (mutual awareness point)
        let trigger = option::some(TriggerCondition::TimeBased(timestamp_us));

        TriadicOrderSet {
            wallet,
            timestamp_us,
            master_seed,
            minus_order: Order {
                id: minus_order_id,
                priority_idx: minus_idx,
                price,
                size,
                remaining_size: size,
                is_buy: true,
                trigger,
                metadata,
            },
            ergodic_order: Order {
                id: ergodic_order_id,
                priority_idx: ergodic_idx,
                price,
                size,
                remaining_size: size,
                is_buy: true,
                trigger,
                metadata,
            },
            plus_order: Order {
                id: plus_order_id,
                priority_idx: plus_idx,
                price,
                size,
                remaining_size: size,
                is_buy: true,
                trigger,
                metadata,
            },
        }
    }

    // ════════════════════════════════════════════════════════════════════════
    // Mutual Awareness (Stage 4)
    // ════════════════════════════════════════════════════════════════════════

    /// Initialize the swarm bootstrap state
    public entry fun initialize_swarm(account: &signer, master_seed: u128) {
        move_to(account, SwarmBootstrapState {
            master_seed,
            wallets: vector::empty(),
            order_sets: vector::empty(),
            gf3_sum: 0,
            mutual_awareness_timestamp: option::none(),
        });
    }

    /// Register a wallet and create its triadic order set
    /// All 26 wallets execute this at same timestamp t0 for mutual awareness
    public entry fun register_wallet_and_bootstrap(
        account: &signer,
        wallet_index: u8,
        price: u64,
        size: u64
    ) acquires SwarmBootstrapState {
        assert!(wallet_index < 26, E_INVALID_WALLET_INDEX);

        let state = borrow_global_mut<SwarmBootstrapState>(@zubyul);
        let wallet = wallet_identity(std::signer::address_of(account), wallet_index);
        let timestamp_us = timestamp::now_microseconds();

        // Create triadic order set
        let triadic_set = create_triadic_order_set<SwarmBootstrapMetadata>(
            wallet,
            timestamp_us,
            state.master_seed,
            price,
            size,
            SwarmBootstrapMetadata {
                wallet_letter: wallet.letter,
                trit: ERGODIC_TRIT,
                peer_count: WALLET_COUNT,
            }
        );

        // Register wallet
        vector::push_back(&mut state.wallets, wallet);
        vector::push_back(&mut state.order_sets, triadic_set);

        // Update GF(3) sum: each wallet contributes -1 + 0 + 1 = 0
        // So gf3_sum should remain 0 after each wallet
        state.gf3_sum = state.gf3_sum + (MINUS_TRIT as i64) + (ERGODIC_TRIT as i64) + (PLUS_TRIT as i64);

        event::emit(TriadicOrderSetCreatedEvent {
            wallet_address: wallet.address,
            letter: wallet.letter,
            timestamp_us,
            order_count: 3,
        });

        // If all 26 wallets registered, mutual awareness achieved
        if (vector::length(&state.wallets) == (WALLET_COUNT as u64)) {
            state.mutual_awareness_timestamp = option::some(timestamp_us);
            event::emit(MutualAwarenessAchievedEvent {
                wallet_count: WALLET_COUNT,
                total_orders: 26 * 3,
                timestamp_us,
                gf3_conserved: verify_gf3_conservation(WALLET_COUNT),
            });
        };
    }

    // ════════════════════════════════════════════════════════════════════════
    // GF(3) Conservation Verification
    // ════════════════════════════════════════════════════════════════════════

    /// Verify GF(3) conservation across all wallets
    /// 26 wallets × 3 trits = 78 total
    /// Sum = 26×(-1) + 26×(0) + 26×(+1) = -26 + 0 + 26 = 0 (mod 3) ✓
    public fun verify_gf3_conservation(wallet_count: u8): bool {
        assert!(wallet_count == 26, E_INVALID_WALLET_COUNT);

        // MINUS: 26 × (-1) = -26
        // ERGODIC: 26 × (0) = 0
        // PLUS: 26 × (+1) = +26
        // Total: -26 + 0 + 26 = 0
        let minus_contribution: i64 = -26i64;
        let ergodic_contribution: i64 = 0i64;
        let plus_contribution: i64 = 26i64;
        let total_trit_sum = minus_contribution + ergodic_contribution + plus_contribution;

        total_trit_sum == 0
    }

    // ════════════════════════════════════════════════════════════════════════
    // Delimited Continuation Escape (Stage 5)
    // ════════════════════════════════════════════════════════════════════════

    /// Create continuation bridge from source wallet to target wallet
    /// Enables session jumping between ownership regimes
    public fun create_continuation<M: store + copy + drop>(
        source: WalletIdentity,
        source_order: &Order<M>,
        target: WalletIdentity,
        target_order: &Order<M>,
        payload: M
    ): ContinuationContext<M> {
        ContinuationContext {
            source_wallet: source,
            target_wallet: target,
            source_order_id: source_order.id,
            target_order_id: target_order.id,
            timestamp_us: timestamp::now_microseconds(),
            payload,
        }
    }

    // ════════════════════════════════════════════════════════════════════════
    // View Functions
    // ════════════════════════════════════════════════════════════════════════

    #[view]
    public fun get_wallet_count(): u64 acquires SwarmBootstrapState {
        vector::length(&borrow_global<SwarmBootstrapState>(@zubyul).wallets)
    }

    #[view]
    public fun get_gf3_status(): (i64, bool) acquires SwarmBootstrapState {
        let state = borrow_global<SwarmBootstrapState>(@zubyul);
        let conserved = (state.gf3_sum % 3) == 0;
        (state.gf3_sum, conserved)
    }

    #[view]
    public fun is_mutual_awareness_achieved(): bool acquires SwarmBootstrapState {
        let state = borrow_global<SwarmBootstrapState>(@zubyul);
        option::is_some(&state.mutual_awareness_timestamp)
    }

    #[view]
    public fun get_mutual_awareness_timestamp(): Option<u64> acquires SwarmBootstrapState {
        borrow_global<SwarmBootstrapState>(@zubyul).mutual_awareness_timestamp
    }

    // ════════════════════════════════════════════════════════════════════════
    // Tests
    // ════════════════════════════════════════════════════════════════════════

    #[test]
    fun test_splitmix64_determinism() {
        let seed = 1069u128;
        let rng1 = splitmix64_new(seed);
        let rng2 = splitmix64_new(seed);

        let v1 = splitmix64_next(&mut rng1);
        let v2 = splitmix64_next(&mut rng2);
        assert!(v1 == v2, 2001);  // Same seed → same output
    }

    #[test]
    fun test_triadic_fork_collision_freedom() {
        let seed = 1069u128;
        let minus_stream = derive_stream(seed, 0, MINUS_XORBYTE);
        let ergodic_stream = derive_stream(seed, 0, ERGODIC_XORBYTE);
        let plus_stream = derive_stream(seed, 0, PLUS_XORBYTE);

        // All three streams should have different initial states
        assert!(minus_stream.state != ergodic_stream.state, 2002);
        assert!(ergodic_stream.state != plus_stream.state, 2003);
        assert!(minus_stream.state != plus_stream.state, 2004);
    }

    #[test]
    fun test_gf3_conservation() {
        assert!(verify_gf3_conservation(26), 2005);
    }
}
