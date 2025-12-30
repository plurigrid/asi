/// multiverse.move - Multiverse Finance on Aptos
///
/// INVARIANTS:
///   1. stake_a + stake_b + accumulated_decay = total_apt_locked
///   2. APT never destroyed, never injected — only moved by selection or decay
///   3. FA claim tokens are tradeable representations of verse stakes
///
/// Operations:
///   SPLIT    - Lock APT, create paired FA claim tokens (tradeable!)
///   MERGE    - Burn matched claims (equal A + B), withdraw proportional APT
///   MAINTAIN - Reset decay clock (costs attention, not money)
///   RESOLVE  - Oracle declares winner, loser stake → accumulated
///   CLAIM    - Winner burns tokens to receive APT
module gay_move::multiverse {
    use std::string::{Self, String};
    use std::signer;
    use std::option;
    use aptos_framework::coin;
    use aptos_framework::aptos_coin::AptosCoin;
    use aptos_framework::timestamp;
    use aptos_framework::event;
    use aptos_framework::account::{Self, SignerCapability};
    use aptos_framework::object::{Self, Object, ConstructorRef, ExtendRef};
    use aptos_framework::fungible_asset::{Self, MintRef, BurnRef, TransferRef, Metadata};
    use aptos_framework::primary_fungible_store;

    /// Error codes
    const E_NOT_AUTHORIZED: u64 = 1;
    const E_ALREADY_RESOLVED: u64 = 2;
    const E_NOT_RESOLVED: u64 = 3;
    const E_INVARIANT_VIOLATED: u64 = 4;
    const E_INSUFFICIENT_STAKE: u64 = 5;
    const E_NOT_EXPIRED: u64 = 6;
    const E_ALREADY_INITIALIZED: u64 = 7;
    const E_BIFURCATION_NOT_FOUND: u64 = 8;
    const E_MISMATCHED_AMOUNTS: u64 = 9;
    const E_NOT_VAULT: u64 = 10;

    /// PATH A: Vault-only mode. Only this address can move value.
    /// Worldnet handles intelligence; mainnet handles settlement.
    const VAULT_ADDRESS: address = @0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b;

    /// Default decay: 693 bps/hour ≈ 6.93%/hour ≈ 10 hour half-life
    const DEFAULT_DECAY_RATE: u64 = 693;
    const BPS_DENOMINATOR: u64 = 10000;
    const SECONDS_PER_HOUR: u64 = 3600;

    // ============================================================
    // TYPES
    // ============================================================

    /// Controller for verse FA tokens
    struct VerseTokenController has key {
        mint_ref: MintRef,
        burn_ref: BurnRef,
        transfer_ref: TransferRef,
    }

    /// A Bifurcation: the core escrow structure with two verse claim tokens
    struct Bifurcation has key {
        id: u64,
        creator: address,
        belief_a: String,
        belief_b: String,
        verse_a_metadata: Object<Metadata>,  // FA for verse A claims
        verse_b_metadata: Object<Metadata>,  // FA for verse B claims
        total_apt_locked: u64,               // APT in escrow
        stake_a: u64,                        // Current claim value A
        stake_b: u64,                        // Current claim value B
        accumulated_decay: u64,              // Decayed value (goes to winner)
        last_decay_time: u64,
        decay_rate: u64,                     // bps per hour
        expiry: u64,
        resolved: bool,
        winner_is_a: bool,
        extend_ref: ExtendRef,
    }

    /// Global state for the multiverse
    struct MultiverseState has key {
        next_id: u64,
        oracle: address,
        signer_cap: SignerCapability,
        escrow_addr: address,
    }

    // ============================================================
    // EVENTS
    // ============================================================

    #[event]
    struct SplitEvent has drop, store {
        bifurcation_id: u64,
        bifurcation_addr: address,
        belief_a: String,
        belief_b: String,
        apt_locked: u64,
        expiry: u64,
    }

    #[event]
    struct MergeEvent has drop, store {
        bifurcation_addr: address,
        claims_burned: u64,
        apt_returned: u64,
    }

    #[event]
    struct DecayEvent has drop, store {
        bifurcation_addr: address,
        decay_a: u64,
        decay_b: u64,
        new_accumulated: u64,
    }

    #[event]
    struct ResolveEvent has drop, store {
        bifurcation_addr: address,
        winner: String,
        winner_total: u64,  // stake + accumulated
    }

    #[event]
    struct ClaimEvent has drop, store {
        bifurcation_addr: address,
        claimer: address,
        apt_received: u64,
    }

    // ============================================================
    // INITIALIZATION
    // ============================================================

    /// Initialize the multiverse - called once by deployer
    public entry fun initialize(deployer: &signer) {
        let deployer_addr = signer::address_of(deployer);
        assert!(!exists<MultiverseState>(deployer_addr), E_ALREADY_INITIALIZED);

        // Create resource account for escrow
        let (resource_signer, signer_cap) = account::create_resource_account(deployer, b"gay_escrow");
        let escrow_addr = signer::address_of(&resource_signer);
        coin::register<AptosCoin>(&resource_signer);

        move_to(deployer, MultiverseState {
            next_id: 0,
            oracle: deployer_addr,
            signer_cap,
            escrow_addr,
        });
    }

    fun get_escrow_signer(state: &MultiverseState): signer {
        account::create_signer_with_capability(&state.signer_cap)
    }

    // ============================================================
    // SPLIT: Lock APT, create two FA claim token types
    // ============================================================

    /// Split APT into two tradeable verse claim tokens
    /// PATH A: Vault-only. Only VAULT_ADDRESS can call.
    public entry fun split(
        account: &signer,
        apt_amount: u64,
        belief_a: String,
        belief_b: String,
        duration_seconds: u64,
    ) acquires MultiverseState, VerseTokenController {
        let sender = signer::address_of(account);
        assert!(sender == VAULT_ADDRESS, E_NOT_VAULT);
        let state = borrow_global_mut<MultiverseState>(@gay_move);
        let id = state.next_id;
        state.next_id = id + 1;

        let now = timestamp::now_seconds();
        let expiry = now + duration_seconds;

        // Lock APT in escrow
        let apt = coin::withdraw<AptosCoin>(account, apt_amount);
        coin::deposit(state.escrow_addr, apt);

        // Create Bifurcation object
        let constructor_ref = object::create_object(sender);
        let object_signer = object::generate_signer(&constructor_ref);
        let extend_ref = object::generate_extend_ref(&constructor_ref);
        let bifurcation_addr = signer::address_of(&object_signer);

        // Create FA for Verse A claims
        let verse_a_constructor = object::create_named_object(&object_signer, b"verse_a");
        let verse_a_metadata = create_verse_fa(&verse_a_constructor, belief_a, string::utf8(b"VA"));

        // Create FA for Verse B claims
        let verse_b_constructor = object::create_named_object(&object_signer, b"verse_b");
        let verse_b_metadata = create_verse_fa(&verse_b_constructor, belief_b, string::utf8(b"VB"));

        // Each verse gets half as initial stake (remainder goes to A)
        let stake_a = (apt_amount + 1) / 2;
        let stake_b = apt_amount / 2;

        // Mint claim tokens to creator (they can trade these!)
        mint_verse_tokens(verse_a_metadata, sender, stake_a);
        mint_verse_tokens(verse_b_metadata, sender, stake_b);

        // Store bifurcation
        move_to(&object_signer, Bifurcation {
            id,
            creator: sender,
            belief_a,
            belief_b,
            verse_a_metadata,
            verse_b_metadata,
            total_apt_locked: apt_amount,
            stake_a,
            stake_b,
            accumulated_decay: 0,
            last_decay_time: now,
            decay_rate: DEFAULT_DECAY_RATE,
            expiry,
            resolved: false,
            winner_is_a: false,
            extend_ref,
        });

        event::emit(SplitEvent {
            bifurcation_id: id,
            bifurcation_addr,
            belief_a,
            belief_b,
            apt_locked: apt_amount,
            expiry,
        });
    }

    /// Create a verse FA (fungible asset) for claims
    fun create_verse_fa(
        constructor_ref: &ConstructorRef,
        name: String,
        symbol: String,
    ): Object<Metadata> {
        let object_signer = object::generate_signer(constructor_ref);

        primary_fungible_store::create_primary_store_enabled_fungible_asset(
            constructor_ref,
            option::none(), // unlimited supply
            name,
            symbol,
            8, // decimals
            string::utf8(b"https://gay.move/verse.png"),
            string::utf8(b"https://gay.move"),
        );

        let mint_ref = fungible_asset::generate_mint_ref(constructor_ref);
        let burn_ref = fungible_asset::generate_burn_ref(constructor_ref);
        let transfer_ref = fungible_asset::generate_transfer_ref(constructor_ref);

        move_to(&object_signer, VerseTokenController {
            mint_ref,
            burn_ref,
            transfer_ref,
        });

        object::object_from_constructor_ref(constructor_ref)
    }

    fun mint_verse_tokens(metadata: Object<Metadata>, to: address, amount: u64) acquires VerseTokenController {
        let metadata_addr = object::object_address(&metadata);
        let controller = borrow_global<VerseTokenController>(metadata_addr);
        let fa = fungible_asset::mint(&controller.mint_ref, amount);
        primary_fungible_store::deposit(to, fa);
    }

    fun burn_verse_tokens(metadata: Object<Metadata>, from: address, amount: u64) acquires VerseTokenController {
        let metadata_addr = object::object_address(&metadata);
        let controller = borrow_global<VerseTokenController>(metadata_addr);
        primary_fungible_store::burn(&controller.burn_ref, from, amount);
    }

    // ============================================================
    // APPLY DECAY: Shift stake to accumulated (conservation!)
    // ============================================================

    /// Apply decay - call this before any operation to update stakes
    fun apply_decay(bif: &mut Bifurcation) {
        let now = timestamp::now_seconds();
        if (now <= bif.last_decay_time || bif.resolved) {
            return
        };

        let elapsed_hours = (now - bif.last_decay_time) / SECONDS_PER_HOUR;
        if (elapsed_hours == 0) {
            return
        };

        // Decay rate in bps per hour
        // decay_amount = stake * rate * hours / BPS_DENOMINATOR
        let decay_a = (bif.stake_a * bif.decay_rate * elapsed_hours) / BPS_DENOMINATOR;
        let decay_b = (bif.stake_b * bif.decay_rate * elapsed_hours) / BPS_DENOMINATOR;

        // Clamp to available stake
        if (decay_a > bif.stake_a) { decay_a = bif.stake_a };
        if (decay_b > bif.stake_b) { decay_b = bif.stake_b };

        // CONSERVATION: stake decreases, accumulated increases
        bif.stake_a = bif.stake_a - decay_a;
        bif.stake_b = bif.stake_b - decay_b;
        bif.accumulated_decay = bif.accumulated_decay + decay_a + decay_b;
        bif.last_decay_time = now;

        // Verify invariant
        assert!(
            bif.stake_a + bif.stake_b + bif.accumulated_decay == bif.total_apt_locked,
            E_INVARIANT_VIOLATED
        );

        // Note: DecayEvent emitted by caller who has the address
    }

    // ============================================================
    // MAINTAIN: Reset decay clock (costs attention, not money)
    // ============================================================

    /// Holder can maintain their position to reset decay
    /// PATH A: Vault-only. Only VAULT_ADDRESS can call.
    public entry fun maintain(
        account: &signer,
        bifurcation_addr: address,
    ) acquires Bifurcation {
        assert!(signer::address_of(account) == VAULT_ADDRESS, E_NOT_VAULT);
        let bif = borrow_global_mut<Bifurcation>(bifurcation_addr);
        assert!(!bif.resolved, E_ALREADY_RESOLVED);

        // Apply any pending decay first
        apply_decay(bif);

        // Reset the clock (next decay starts from now)
        bif.last_decay_time = timestamp::now_seconds();
    }

    // ============================================================
    // MERGE: Burn matched claims, withdraw proportional APT
    // ============================================================

    /// Burn equal amounts of A and B tokens to withdraw APT
    /// PATH A: Vault-only. Only VAULT_ADDRESS can call.
    public entry fun merge(
        account: &signer,
        bifurcation_addr: address,
        amount: u64,  // Amount of each token to burn
    ) acquires Bifurcation, MultiverseState, VerseTokenController {
        let sender = signer::address_of(account);
        assert!(sender == VAULT_ADDRESS, E_NOT_VAULT);
        let bif = borrow_global_mut<Bifurcation>(bifurcation_addr);

        assert!(!bif.resolved, E_ALREADY_RESOLVED);

        // Apply decay first
        apply_decay(bif);

        // Validate amount doesn't exceed available stakes
        assert!(amount <= bif.stake_a && amount <= bif.stake_b, E_INSUFFICIENT_STAKE);

        // Burn equal amounts of both tokens
        burn_verse_tokens(bif.verse_a_metadata, sender, amount);
        burn_verse_tokens(bif.verse_b_metadata, sender, amount);

        // Calculate APT to return (proportional to total claims)
        // amount burned on each side, so 2*amount total claims
        let total_claims_remaining = bif.stake_a + bif.stake_b;
        let apt_to_return = if (total_claims_remaining == 0) {
            0
        } else {
            // Proportional: (2 * amount) / total_claims * total_apt_locked
            // But we need to exclude accumulated_decay from withdrawal
            let withdrawable_apt = bif.total_apt_locked - bif.accumulated_decay;
            ((2 * amount as u128) * (withdrawable_apt as u128) / (total_claims_remaining as u128)) as u64
        };

        // Transfer APT from escrow
        let state = borrow_global<MultiverseState>(@gay_move);
        let escrow_signer = get_escrow_signer(state);
        let apt = coin::withdraw<AptosCoin>(&escrow_signer, apt_to_return);
        coin::deposit(sender, apt);

        // Update stakes proportionally
        let stake_reduction = amount; // Each side reduced by amount
        bif.stake_a = bif.stake_a - stake_reduction;
        bif.stake_b = bif.stake_b - stake_reduction;
        bif.total_apt_locked = bif.total_apt_locked - apt_to_return;

        event::emit(MergeEvent {
            bifurcation_addr,
            claims_burned: amount * 2,
            apt_returned: apt_to_return,
        });
    }

    // ============================================================
    // RESOLVE: Oracle declares winner
    // ============================================================

    /// Oracle resolves the bifurcation after expiry
    /// PATH A: Vault-only. Only VAULT_ADDRESS can call.
    public entry fun resolve(
        oracle: &signer,
        bifurcation_addr: address,
        winner_is_a: bool,
    ) acquires MultiverseState, Bifurcation {
        let caller = signer::address_of(oracle);
        assert!(caller == VAULT_ADDRESS, E_NOT_VAULT);
        let state = borrow_global<MultiverseState>(@gay_move);
        assert!(caller == state.oracle, E_NOT_AUTHORIZED);

        let bif = borrow_global_mut<Bifurcation>(bifurcation_addr);
        assert!(!bif.resolved, E_ALREADY_RESOLVED);

        let now = timestamp::now_seconds();
        assert!(now >= bif.expiry, E_NOT_EXPIRED);

        // Apply final decay
        apply_decay(bif);

        bif.resolved = true;
        bif.winner_is_a = winner_is_a;

        let winner_belief = if (winner_is_a) { bif.belief_a } else { bif.belief_b };
        let winner_stake = if (winner_is_a) { bif.stake_a } else { bif.stake_b };

        event::emit(ResolveEvent {
            bifurcation_addr,
            winner: winner_belief,
            winner_total: winner_stake + bif.accumulated_decay,
        });
    }

    // ============================================================
    // CLAIM: Winner burns tokens to receive APT
    // ============================================================

    /// After resolution, winning token holders burn to claim APT
    /// PATH A: Vault-only. Only VAULT_ADDRESS can call.
    public entry fun claim(
        account: &signer,
        bifurcation_addr: address,
        amount: u64,
    ) acquires Bifurcation, MultiverseState, VerseTokenController {
        let sender = signer::address_of(account);
        assert!(sender == VAULT_ADDRESS, E_NOT_VAULT);
        let bif = borrow_global_mut<Bifurcation>(bifurcation_addr);

        assert!(bif.resolved, E_NOT_RESOLVED);

        // Determine winning token and stake
        let (winning_metadata, winning_stake) = if (bif.winner_is_a) {
            (bif.verse_a_metadata, bif.stake_a)
        } else {
            (bif.verse_b_metadata, bif.stake_b)
        };

        // Validate amount doesn't exceed stake
        assert!(amount <= winning_stake, E_INSUFFICIENT_STAKE);

        // Burn winner tokens
        burn_verse_tokens(winning_metadata, sender, amount);

        // Calculate payout: winner gets proportional share including accumulated decay
        let total_winner_value = winning_stake + bif.accumulated_decay;

        let apt_payout = if (total_winner_value == 0) {
            0
        } else {
            ((amount as u128) * (bif.total_apt_locked as u128) / (total_winner_value as u128)) as u64
        };

        // Clamp to available
        if (apt_payout > bif.total_apt_locked) {
            apt_payout = bif.total_apt_locked;
        };

        // Transfer APT
        let state = borrow_global<MultiverseState>(@gay_move);
        let escrow_signer = get_escrow_signer(state);
        let apt = coin::withdraw<AptosCoin>(&escrow_signer, apt_payout);
        coin::deposit(sender, apt);

        // Update tracking
        if (bif.winner_is_a) {
            bif.stake_a = bif.stake_a - amount;
        } else {
            bif.stake_b = bif.stake_b - amount;
        };
        bif.total_apt_locked = bif.total_apt_locked - apt_payout;

        event::emit(ClaimEvent {
            bifurcation_addr,
            claimer: sender,
            apt_received: apt_payout,
        });
    }

    // ============================================================
    // VIEW FUNCTIONS
    // ============================================================

    #[view]
    public fun get_bifurcation_info(bifurcation_addr: address): (u64, u64, u64, u64, bool) acquires Bifurcation {
        let bif = borrow_global<Bifurcation>(bifurcation_addr);
        (bif.total_apt_locked, bif.stake_a, bif.stake_b, bif.accumulated_decay, bif.resolved)
    }

    #[view]
    public fun check_invariant(bifurcation_addr: address): bool acquires Bifurcation {
        let bif = borrow_global<Bifurcation>(bifurcation_addr);
        bif.stake_a + bif.stake_b + bif.accumulated_decay == bif.total_apt_locked
    }

    #[view]
    public fun get_escrow_address(): address acquires MultiverseState {
        borrow_global<MultiverseState>(@gay_move).escrow_addr
    }
}
