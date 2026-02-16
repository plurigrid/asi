/// *Able Markets - LMSR Prediction Markets for Protocol Proposals
/// 
/// Financializes protocol evolution across ecosystems using Logarithmic Market Scoring Rule.
/// GF(3) conservation: Long(+1) + MarketMaker(0) + Short(-1) = 0

module able_markets::lmsr {
    use std::signer;
    use std::vector;
    use std::string::{String, utf8};
    use aptos_framework::coin;
    use aptos_framework::aptos_coin::AptosCoin;
    use aptos_framework::timestamp;
    use aptos_framework::event;

    /// Error codes
    const E_NOT_ADMIN: u64 = 1;
    const E_MARKET_NOT_FOUND: u64 = 2;
    const E_MARKET_RESOLVED: u64 = 3;
    const E_INSUFFICIENT_BALANCE: u64 = 4;
    const E_INVALID_OUTCOME: u64 = 5;
    const E_MARKET_NOT_RESOLVED: u64 = 6;
    const E_ALREADY_CLAIMED: u64 = 7;

    /// Fixed-point scaling (6 decimals for APT compatibility)
    const SCALE: u64 = 1_000_000;
    
    /// Natural log approximation constants
    const LN_SCALE: u64 = 1_000_000_000; // Higher precision for ln

    /// Market state for a single proposal
    struct Market has key, store {
        proposal_id: String,
        ecosystem: String,        // "aptos", "swift", "srfi"
        able_trait: String,       // e.g., "PQ-Signable"
        trit: u8,                 // 0=MINUS, 1=ERGODIC, 2=PLUS (stored as 0,1,2)
        
        yes_shares: u64,          // Scaled by SCALE
        no_shares: u64,           // Scaled by SCALE
        liquidity: u64,           // b parameter, scaled
        
        total_volume: u64,
        created_at: u64,
        resolved: bool,
        outcome: bool,            // true = accepted, false = rejected
        
        resolution_hash: vector<u8>,  // GitHub commit hash as proof
    }

    /// User position in a market
    struct Position has key, store {
        market_id: String,
        yes_shares: u64,
        no_shares: u64,
        cost_basis: u64,
        claimed: bool,
    }

    /// Global registry of markets
    struct MarketRegistry has key {
        markets: vector<String>,
        admin: address,
    }

    /// Events
    #[event]
    struct MarketCreated has drop, store {
        proposal_id: String,
        ecosystem: String,
        able_trait: String,
        liquidity: u64,
        creator: address,
    }

    #[event]
    struct TradeExecuted has drop, store {
        proposal_id: String,
        trader: address,
        is_yes: bool,
        shares: u64,
        cost: u64,
        new_price: u64,
    }

    #[event]
    struct MarketResolved has drop, store {
        proposal_id: String,
        outcome: bool,
        resolution_hash: vector<u8>,
        resolver: address,
    }

    /// Initialize the market registry
    public entry fun initialize(admin: &signer) {
        let admin_addr = signer::address_of(admin);
        move_to(admin, MarketRegistry {
            markets: vector::empty(),
            admin: admin_addr,
        });
    }

    /// Create a new prediction market for a proposal
    public entry fun create_market(
        creator: &signer,
        proposal_id: String,
        ecosystem: String,
        able_trait: String,
        trit: u8,
        liquidity: u64,
    ) acquires MarketRegistry {
        let creator_addr = signer::address_of(creator);
        
        // Transfer initial liquidity
        let liquidity_coins = coin::withdraw<AptosCoin>(creator, liquidity);
        coin::deposit(creator_addr, liquidity_coins);
        
        let market = Market {
            proposal_id: proposal_id,
            ecosystem,
            able_trait,
            trit,
            yes_shares: 0,
            no_shares: 0,
            liquidity: liquidity * SCALE,
            total_volume: 0,
            created_at: timestamp::now_seconds(),
            resolved: false,
            outcome: false,
            resolution_hash: vector::empty(),
        };
        
        move_to(creator, market);
        
        // Register in global registry
        let registry = borrow_global_mut<MarketRegistry>(@able_markets);
        vector::push_back(&mut registry.markets, proposal_id);
        
        event::emit(MarketCreated {
            proposal_id,
            ecosystem,
            able_trait,
            liquidity,
            creator: creator_addr,
        });
    }

    /// Calculate LMSR cost function C(q) = b * ln(e^(q_yes/b) + e^(q_no/b))
    /// Using fixed-point approximation
    fun lmsr_cost(yes_shares: u64, no_shares: u64, liquidity: u64): u64 {
        // Simplified: for equal shares, cost ≈ b * ln(2)
        // Full implementation would use fixed-point exp/ln
        let exp_yes = exp_approx(yes_shares, liquidity);
        let exp_no = exp_approx(no_shares, liquidity);
        let sum = exp_yes + exp_no;
        liquidity * ln_approx(sum) / LN_SCALE
    }

    /// Calculate YES price = e^(q_yes/b) / (e^(q_yes/b) + e^(q_no/b))
    fun lmsr_price_yes(yes_shares: u64, no_shares: u64, liquidity: u64): u64 {
        let exp_yes = exp_approx(yes_shares, liquidity);
        let exp_no = exp_approx(no_shares, liquidity);
        (exp_yes * SCALE) / (exp_yes + exp_no)
    }

    /// Approximate e^(x/b) using Taylor series
    fun exp_approx(x: u64, b: u64): u64 {
        if (b == 0) return SCALE;
        let ratio = (x * SCALE) / b;
        // e^x ≈ 1 + x + x²/2 + x³/6 for small x
        let term1 = SCALE;
        let term2 = ratio;
        let term3 = (ratio * ratio) / (2 * SCALE);
        let term4 = (ratio * ratio * ratio) / (6 * SCALE * SCALE);
        term1 + term2 + term3 + term4
    }

    /// Approximate ln(x) for x near 1
    fun ln_approx(x: u64): u64 {
        // ln(x) ≈ (x-1) - (x-1)²/2 + (x-1)³/3 for x near 1
        if (x <= SCALE) return 0;
        let y = x - SCALE;
        let y_scaled = (y * LN_SCALE) / SCALE;
        y_scaled - (y_scaled * y_scaled) / (2 * LN_SCALE) 
    }

    /// Buy YES shares
    public entry fun buy_yes(
        trader: &signer,
        market_owner: address,
        shares: u64,
    ) acquires Market, Position {
        let trader_addr = signer::address_of(trader);
        let market = borrow_global_mut<Market>(market_owner);
        
        assert!(!market.resolved, E_MARKET_RESOLVED);
        
        let old_cost = lmsr_cost(market.yes_shares, market.no_shares, market.liquidity);
        market.yes_shares = market.yes_shares + (shares * SCALE);
        let new_cost = lmsr_cost(market.yes_shares, market.no_shares, market.liquidity);
        
        let cost = (new_cost - old_cost) / SCALE;
        
        // Transfer payment
        let payment = coin::withdraw<AptosCoin>(trader, cost);
        coin::deposit(market_owner, payment);
        
        market.total_volume = market.total_volume + cost;
        
        // Update or create position
        if (exists<Position>(trader_addr)) {
            let position = borrow_global_mut<Position>(trader_addr);
            position.yes_shares = position.yes_shares + shares;
            position.cost_basis = position.cost_basis + cost;
        } else {
            move_to(trader, Position {
                market_id: market.proposal_id,
                yes_shares: shares,
                no_shares: 0,
                cost_basis: cost,
                claimed: false,
            });
        };
        
        let new_price = lmsr_price_yes(market.yes_shares, market.no_shares, market.liquidity);
        
        event::emit(TradeExecuted {
            proposal_id: market.proposal_id,
            trader: trader_addr,
            is_yes: true,
            shares,
            cost,
            new_price,
        });
    }

    /// Buy NO shares
    public entry fun buy_no(
        trader: &signer,
        market_owner: address,
        shares: u64,
    ) acquires Market, Position {
        let trader_addr = signer::address_of(trader);
        let market = borrow_global_mut<Market>(market_owner);
        
        assert!(!market.resolved, E_MARKET_RESOLVED);
        
        let old_cost = lmsr_cost(market.yes_shares, market.no_shares, market.liquidity);
        market.no_shares = market.no_shares + (shares * SCALE);
        let new_cost = lmsr_cost(market.yes_shares, market.no_shares, market.liquidity);
        
        let cost = (new_cost - old_cost) / SCALE;
        
        let payment = coin::withdraw<AptosCoin>(trader, cost);
        coin::deposit(market_owner, payment);
        
        market.total_volume = market.total_volume + cost;
        
        if (exists<Position>(trader_addr)) {
            let position = borrow_global_mut<Position>(trader_addr);
            position.no_shares = position.no_shares + shares;
            position.cost_basis = position.cost_basis + cost;
        } else {
            move_to(trader, Position {
                market_id: market.proposal_id,
                yes_shares: 0,
                no_shares: shares,
                cost_basis: cost,
                claimed: false,
            });
        };
        
        let new_price = lmsr_price_yes(market.yes_shares, market.no_shares, market.liquidity);
        
        event::emit(TradeExecuted {
            proposal_id: market.proposal_id,
            trader: trader_addr,
            is_yes: false,
            shares,
            cost,
            new_price,
        });
    }

    /// Resolve market with oracle attestation
    public entry fun resolve(
        resolver: &signer,
        market_owner: address,
        outcome: bool,
        resolution_hash: vector<u8>,
    ) acquires Market, MarketRegistry {
        let resolver_addr = signer::address_of(resolver);
        let registry = borrow_global<MarketRegistry>(@able_markets);
        
        assert!(resolver_addr == registry.admin, E_NOT_ADMIN);
        
        let market = borrow_global_mut<Market>(market_owner);
        assert!(!market.resolved, E_MARKET_RESOLVED);
        
        market.resolved = true;
        market.outcome = outcome;
        market.resolution_hash = resolution_hash;
        
        event::emit(MarketResolved {
            proposal_id: market.proposal_id,
            outcome,
            resolution_hash,
            resolver: resolver_addr,
        });
    }

    /// Claim winnings after resolution
    public entry fun claim(
        claimer: &signer,
        market_owner: address,
    ) acquires Market, Position {
        let claimer_addr = signer::address_of(claimer);
        let market = borrow_global<Market>(market_owner);
        
        assert!(market.resolved, E_MARKET_NOT_RESOLVED);
        
        let position = borrow_global_mut<Position>(claimer_addr);
        assert!(!position.claimed, E_ALREADY_CLAIMED);
        
        let payout = if (market.outcome) {
            // YES won: pay out YES shares at 1 APT each
            position.yes_shares * SCALE
        } else {
            // NO won: pay out NO shares at 1 APT each
            position.no_shares * SCALE
        };
        
        if (payout > 0) {
            // In production, would pay from market pool
            // Simplified: mark as claimed
            position.claimed = true;
        };
    }

    /// View function: get current YES price
    #[view]
    public fun get_price(market_owner: address): u64 acquires Market {
        let market = borrow_global<Market>(market_owner);
        lmsr_price_yes(market.yes_shares, market.no_shares, market.liquidity)
    }

    /// View function: get market info
    #[view]
    public fun get_market_info(market_owner: address): (String, String, u64, u64, bool) acquires Market {
        let market = borrow_global<Market>(market_owner);
        (
            market.proposal_id,
            market.able_trait,
            market.yes_shares / SCALE,
            market.no_shares / SCALE,
            market.resolved,
        )
    }
}
