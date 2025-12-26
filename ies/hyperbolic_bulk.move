/// Hyperbolic Bulk: On-Chain GF(3) Entropy Storage
/// 
/// The "bulk" in AdS/CFT correspondence: entropy lives in the interior,
/// observables project to the boundary. Triads are first-class objects
/// with GF(3) conservation as a geometric invariant.
///
/// Architecture:
///   BOUNDARY (agents, skills, colors) ←→ BULK (entropy triads, GF(3) invariants)
///
module hyperbolic_bulk::entropy_triads {
    use std::signer;
    use aptos_framework::randomness;
    use aptos_framework::timestamp;
    use aptos_std::table::{Self, Table};

    // GF(3) Elements: 0=ERGODIC, 1=PLUS, 2=MINUS (-1 ≡ 2 mod 3)
    const E_GF3_VIOLATION: u64 = 1;
    const E_RECORD_NOT_FOUND: u64 = 3;

    struct EntropyRecord has store, drop, copy {
        drand_round: u64,
        drand_seed: u256,
        eeg_seed: u256,
        combined_seed: u256,
        timestamp: u64,
        trit: u8,
        color_hex: vector<u8>,
    }

    struct EntropyTriad has store, drop, copy {
        record_id_1: u64,
        record_id_2: u64,
        record_id_3: u64,
        trit_1: u8,
        trit_2: u8,
        trit_3: u8,
        gf3_sum: u8,
        gf3_conserved: bool,
        skill_1: vector<u8>,
        skill_2: vector<u8>,
        skill_3: vector<u8>,
        formed_at: u64,
    }

    struct ReafferenceProof has store, drop, copy {
        seed: u256,
        index: u64,
        predicted_color: vector<u8>,
        observed_color: vector<u8>,
        matched: bool,
        loop_type: vector<u8>,
        verified_at: u64,
    }

    struct HyperbolicBulk has key {
        records: Table<u64, EntropyRecord>,
        triads: Table<u64, EntropyTriad>,
        reafference_proofs: Table<u64, ReafferenceProof>,
        next_record_id: u64,
        next_triad_id: u64,
        next_proof_id: u64,
        total_conserved_triads: u64,
        total_violated_triads: u64,
    }

    public entry fun initialize(account: &signer) {
        move_to(account, HyperbolicBulk {
            records: table::new(),
            triads: table::new(),
            reafference_proofs: table::new(),
            next_record_id: 0,
            next_triad_id: 0,
            next_proof_id: 0,
            total_conserved_triads: 0,
            total_violated_triads: 0,
        });
    }

    #[randomness]
    entry fun store_entropy(
        account: &signer,
        drand_round: u64,
        drand_seed: u256,
        eeg_seed: u256,
        color_hex: vector<u8>,
    ) acquires HyperbolicBulk {
        let addr = signer::address_of(account);
        let bulk = borrow_global_mut<HyperbolicBulk>(addr);
        let onchain_rand = randomness::u256_range(0, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF);
        let combined = drand_seed ^ eeg_seed ^ onchain_rand;
        let trit = ((combined % 3) as u8);
        let record_id = bulk.next_record_id;
        bulk.next_record_id = record_id + 1;
        table::add(&mut bulk.records, record_id, EntropyRecord {
            drand_round, drand_seed, eeg_seed, combined_seed: combined,
            timestamp: timestamp::now_microseconds(), trit, color_hex,
        });
    }

    public entry fun form_conserved_triad(
        account: &signer,
        id1: u64, id2: u64, id3: u64,
        skill_1: vector<u8>, skill_2: vector<u8>, skill_3: vector<u8>,
    ) acquires HyperbolicBulk {
        let addr = signer::address_of(account);
        let bulk = borrow_global_mut<HyperbolicBulk>(addr);
        let r1 = table::borrow(&bulk.records, id1);
        let r2 = table::borrow(&bulk.records, id2);
        let r3 = table::borrow(&bulk.records, id3);
        let sum = (r1.trit + r2.trit + r3.trit) % 3;
        assert!(sum == 0, E_GF3_VIOLATION);
        bulk.total_conserved_triads = bulk.total_conserved_triads + 1;
        let triad_id = bulk.next_triad_id;
        bulk.next_triad_id = triad_id + 1;
        table::add(&mut bulk.triads, triad_id, EntropyTriad {
            record_id_1: id1, record_id_2: id2, record_id_3: id3,
            trit_1: r1.trit, trit_2: r2.trit, trit_3: r3.trit,
            gf3_sum: 0, gf3_conserved: true,
            skill_1, skill_2, skill_3,
            formed_at: timestamp::now_microseconds(),
        });
    }

    public entry fun record_reafference(
        account: &signer,
        seed: u256,
        index: u64,
        predicted_color: vector<u8>,
        observed_color: vector<u8>,
    ) acquires HyperbolicBulk {
        let addr = signer::address_of(account);
        let bulk = borrow_global_mut<HyperbolicBulk>(addr);
        let matched = (predicted_color == observed_color);
        let loop_type = if (matched) { b"loopy_strange" } else { b"exafference" };
        let proof_id = bulk.next_proof_id;
        bulk.next_proof_id = proof_id + 1;
        table::add(&mut bulk.reafference_proofs, proof_id, ReafferenceProof {
            seed, index, predicted_color, observed_color, matched, loop_type,
            verified_at: timestamp::now_microseconds(),
        });
    }

    #[view]
    public fun get_triad(addr: address, id: u64): (bool, u8) acquires HyperbolicBulk {
        let bulk = borrow_global<HyperbolicBulk>(addr);
        let triad = table::borrow(&bulk.triads, id);
        (triad.gf3_conserved, triad.gf3_sum)
    }

    #[view]
    public fun get_stats(addr: address): (u64, u64) acquires HyperbolicBulk {
        let bulk = borrow_global<HyperbolicBulk>(addr);
        (bulk.total_conserved_triads, bulk.total_violated_triads)
    }
}
