# E4 — Multi-ed25519 as TOFU Defense

The current `kolmogorov_codex_quest.move` uses a single ed25519 oracle pubkey committed at `create_quest` time. This is pure TOFU: compromise or loss of that one key owns or bricks the quest.

## Threat model

| Attack | Current | With 2-of-3 multi-ed25519 |
|---|---|---|
| Initial-deploy MITM swaps `oracle_pubkey` | Attacker owns quest | Attacker needs 2 of 3 slots |
| Oracle key leak post-deploy | Escrow drainable | Still need 1 more key |
| Key loss (hardware failure) | Quest bricks until `expires_at` | 2 surviving keys still solve |
| Key-reuse across quests | Single compromise drains all | Per-quest threshold config |

## Move-side sketch

```move
module plurigrid::kolmogorov_codex_quest_v2 {
    use std::vector;
    use aptos_std::multi_ed25519;

    struct Quest has key {
        commitment: vector<u8>,
        oracle_pubkeys: multi_ed25519::UnvalidatedPublicKey, // threshold + N keys
        threshold: u8,
        bounty: coin::Coin<AptosCoin>,
        expires_at: u64,
        solved: bool,
        winner: address,
    }

    public entry fun create_quest_v2(
        creator: &signer,
        commitment: vector<u8>,
        pubkeys_concat: vector<u8>,  // 32*N bytes
        threshold: u8,
        bounty_amount: u64,
        expires_at: u64,
    ) {
        let n = vector::length(&pubkeys_concat) / 32;
        assert!(threshold >= 1 && (threshold as u64) <= n, E_BAD_THRESHOLD);
        assert!(n >= 2, E_NEED_MULTISIG);
        // append threshold byte per aptos_std::multi_ed25519 convention
        vector::push_back(&mut pubkeys_concat, threshold);
        let pk = multi_ed25519::new_unvalidated_public_key_from_bytes(pubkeys_concat);
        // ... escrow, store Quest
    }

    public entry fun submit_solution_v2(
        solver: &signer,
        quest_addr: address,
        preimage: vector<u8>,
        wikidata_root: vector<u8>,
        gaymcp_root: vector<u8>,
        skill_count: u64,
        world_count: u64,
        gf3_sum: u8,
        proof_timestamp: u64,
        multi_sig_bytes: vector<u8>,  // concat sigs + bitmap
    ) acquires Quest {
        let q = borrow_global_mut<Quest>(quest_addr);
        // ... commitment/time/size checks same as v1 ...

        let msg = build_bcs_message(
            signer::address_of(solver), quest_addr,
            wikidata_root, gaymcp_root,
            skill_count, world_count, gf3_sum, proof_timestamp,
        );
        let sig = multi_ed25519::new_unvalidated_signature_from_bytes(multi_sig_bytes);
        assert!(
            multi_ed25519::signature_verify_strict(&sig, &q.oracle_pubkeys, msg),
            E_BAD_MULTISIG
        );
        q.solved = true;
        q.winner = signer::address_of(solver);
        // transfer bounty
    }
}
```

## Gas impact

Aptos `multi_ed25519::signature_verify_strict` is natively implemented. Per Aptos docs, verification cost scales linearly with threshold `t` (t ed25519 verifications + bitmap check). Empirically:

- 1-of-1 (current): 978 gas
- 2-of-3: ~1400 gas (estimated 1.5× based on Aptos gas schedule)
- 3-of-5: ~2100 gas

Bounty cost is paid in APT not gas — threshold choice is a security/ops tradeoff, not an economic one.

## Key custody split

Concrete 2-of-3 assignment for your stack:

1. **Laptop key** (`~/i/proofs/oracle_keypair.json`) — same as today, convenience, ed25519 in flat file
2. **nRF5340 secure element** — generated on-device, signs over USB/BLE; `bcf-0034` already budgets this as "secure element attestation"
3. **Cloud key** (1Password / iCloud Keychain / Turnkey custodial) — offline witness

Any 2 can sign. Losing any 1 is recoverable. Compromising any 1 is insufficient.

## Migration path

- v2 module deployed alongside v1 (no upgrade risk)
- existing quest bounties stay on v1 until `expires_at`
- new quests created on v2 immediately
- solver learns v1/v2 detection from `Quest.type_name` via resource view
- 10 additional Python tests in `solver/test_kolmogorov_solver.py` mirroring v2 asserts

## Bisimulation oracle connection

`passport.gay` as canonical form for cross-session identity (memory: `agentic-protocols-research/`). The 3 keys form a **3-node Paige-Tarjan equivalence class**: a solver is legit iff their multi-sig forms a valid witness against the committed equivalence class. Rotating any one key changes the class identity; rotating ≥2 is a class split, detectable on-chain.

GF(3) trit labels for the 3 key slots:
- laptop = −1 (soft, replaceable)
- secure element = 0 (neutral, hardware-bound)
- cloud = +1 (resilient, recoverable)

Σ = 0 mod 3. TOFU defense inherits GF(3) conservation.

## Status

Draft only. No Move code written to disk. Implementation cost:
- Move module ~120 LOC
- Python solver extension ~60 LOC (threshold sig assembly)
- Tests ~10 cases
- Mainnet redeploy: one `publish` tx (gas budget: ~30k)
