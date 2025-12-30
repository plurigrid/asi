/// Unit tests for Kolmogorov Codex Quest
#[test_only]
module kolmogorov_codex::quest_tests {
    use std::signer;
    use std::vector;
    use aptos_framework::account;
    use aptos_framework::aptos_coin;
    use aptos_framework::coin;
    use aptos_framework::timestamp;
    use aptos_std::ed25519;
    use aptos_std::hash;
    use std::bcs;
    use kolmogorov_codex::quest;

    // Test constants
    const BOUNTY_AMOUNT: u64 = 200_000_000; // 2 APT

    // Test oracle keypair (deterministic for testing)
    // In production, use a secure key management system
    const TEST_ORACLE_PRIVKEY: vector<u8> = x"9b9a8b8e7d6c5b4a3d2e1f0a9b8c7d6e5f4a3b2c1d0e9f8a7b6c5d4e3f2a1b0c";

    #[test_only]
    fun setup_test(aptos: &signer, creator: &signer, solver: &signer) {
        // Initialize timestamp
        timestamp::set_time_has_started_for_testing(aptos);

        // Create accounts
        account::create_account_for_test(signer::address_of(creator));
        account::create_account_for_test(signer::address_of(solver));

        // Initialize AptosCoin
        let (burn_cap, mint_cap) = aptos_coin::initialize_for_test(aptos);

        // Mint coins for creator
        let coins = coin::mint<aptos_coin::AptosCoin>(BOUNTY_AMOUNT * 2, &mint_cap);
        coin::register<aptos_coin::AptosCoin>(creator);
        coin::deposit(signer::address_of(creator), coins);

        // Register solver for coins
        coin::register<aptos_coin::AptosCoin>(solver);

        // Clean up capabilities
        coin::destroy_burn_cap(burn_cap);
        coin::destroy_mint_cap(mint_cap);
    }

    #[test(aptos = @0x1, creator = @0x123, solver = @0x456)]
    fun test_create_quest(aptos: &signer, creator: &signer, solver: &signer) {
        setup_test(aptos, creator, solver);

        // Create commitment (SHA3-256 of solution)
        let solution = b"the_secret_solution";
        let commitment = hash::sha3_256(solution);

        // Oracle public key (32 bytes for ed25519)
        let oracle_pubkey = x"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

        // Create quest
        quest::create_quest(creator, BOUNTY_AMOUNT, commitment, oracle_pubkey);

        // Verify quest exists and is active
        assert!(quest::is_quest_active(signer::address_of(creator)), 1);

        // Verify requirements
        let (min_skills, min_worlds) = quest::get_proof_requirements();
        assert!(min_skills == 6, 2);
        assert!(min_worlds == 6, 3);
    }

    #[test(aptos = @0x1, creator = @0x123, solver = @0x456)]
    #[expected_failure(abort_code = 7)] // E_INSUFFICIENT_BOUNTY
    fun test_create_quest_insufficient_bounty(aptos: &signer, creator: &signer, solver: &signer) {
        setup_test(aptos, creator, solver);

        let commitment = hash::sha3_256(b"solution");
        let oracle_pubkey = x"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

        // Try to create quest with less than 1 APT
        quest::create_quest(creator, 50_000_000, commitment, oracle_pubkey);
    }

    #[test(aptos = @0x1, creator = @0x123, solver = @0x456)]
    #[expected_failure(abort_code = 15)] // E_INVALID_ORACLE_SIGNATURE
    fun test_submit_without_oracle_signature_fails(aptos: &signer, creator: &signer, solver: &signer) {
        setup_test(aptos, creator, solver);

        let solution = b"the_secret_solution";
        let commitment = hash::sha3_256(solution);
        let oracle_pubkey = x"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

        quest::create_quest(creator, BOUNTY_AMOUNT, commitment, oracle_pubkey);

        // Try to submit with invalid signature (should fail)
        let fake_signature = x"0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
        let wikidata_root = x"1111111111111111111111111111111111111111111111111111111111111111";
        let gaymcp_root = x"2222222222222222222222222222222222222222222222222222222222222222";

        quest::submit_solution(
            solver,
            signer::address_of(creator),
            solution,
            wikidata_root,
            gaymcp_root,
            6,  // skill_count
            6,  // world_count
            0,  // gf3_sum (0 % 3 == 0)
            b"ipfs://proof",
            fake_signature,
            timestamp::now_seconds(),
        );
    }

    #[test(aptos = @0x1, creator = @0x123, solver = @0x456)]
    #[expected_failure(abort_code = 8)] // E_INSUFFICIENT_SKILLS
    fun test_insufficient_skills_fails(aptos: &signer, creator: &signer, solver: &signer) {
        setup_test(aptos, creator, solver);

        let solution = b"solution";
        let commitment = hash::sha3_256(solution);
        let oracle_pubkey = x"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

        quest::create_quest(creator, BOUNTY_AMOUNT, commitment, oracle_pubkey);

        let fake_sig = x"0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
        let wikidata_root = x"1111111111111111111111111111111111111111111111111111111111111111";
        let gaymcp_root = x"2222222222222222222222222222222222222222222222222222222222222222";

        // Only 5 skills (should fail before signature check)
        quest::submit_solution(
            solver,
            signer::address_of(creator),
            solution,
            wikidata_root,
            gaymcp_root,
            5,  // skill_count < 6
            6,
            0,
            b"ipfs://proof",
            fake_sig,
            timestamp::now_seconds(),
        );
    }

    #[test(aptos = @0x1, creator = @0x123, solver = @0x456)]
    #[expected_failure(abort_code = 10)] // E_GF3_VIOLATION
    fun test_gf3_violation_fails(aptos: &signer, creator: &signer, solver: &signer) {
        setup_test(aptos, creator, solver);

        let solution = b"solution";
        let commitment = hash::sha3_256(solution);
        let oracle_pubkey = x"0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

        quest::create_quest(creator, BOUNTY_AMOUNT, commitment, oracle_pubkey);

        let fake_sig = x"0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000";
        let wikidata_root = x"1111111111111111111111111111111111111111111111111111111111111111";
        let gaymcp_root = x"2222222222222222222222222222222222222222222222222222222222222222";

        // gf3_sum = 1 (not divisible by 3)
        quest::submit_solution(
            solver,
            signer::address_of(creator),
            solution,
            wikidata_root,
            gaymcp_root,
            6,
            6,
            1,  // GF(3) violation: 1 % 3 != 0
            b"ipfs://proof",
            fake_sig,
            timestamp::now_seconds(),
        );
    }
}
