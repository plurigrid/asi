---
name: pump-sdk-dark
description: Adversarial map of pump.fun's SDK surface. What's extractable, how, and what the permissionless-evolution patch requires to not be a trap.
trit: +1
---

# Pump SDK — Dark Surface Map

Every primitive the pump ecosystem exposes has a light-path use and a dark-path use. The ossified mint (revoked auth triad) is a constraint on the light path; the dark path uses the **non-mint** levers — creator-fee stream, Jito bundling, pool LP ownership, MCP/telegram automation — which are *not* ossified and can be weaponized against holders even on a "clean" token.

## 1. Creator fee stream

**Light:** 10-slot shareholder split → community treasuries, veToken, public goods.

**Dark:**
- Creator never calls `init_fee_sharing`. Fees accrue 100% to single wallet forever. Soft rug — no headline, indefinite extraction.
- Creator sets 10 slots all pointing to wallets they control. Looks like a DAO split on a cursory scan; is a laundering tree.
- Slots point to contracts the creator can upgrade. If any PDA authority is retained, future drains possible.
- `buildDistributeCreatorFeesInstructions` is permissionless to call — but **only if** the config was written. No config = no permissionless distribution.

**Defense:** verify on-chain that (a) fee-sharing config exists, (b) shareholder addresses are PDAs of known programs whose upgrade authority is null / timelocked / multisig, (c) creator's own slot is ≤ a fair fraction (e.g. ≤ 30%).

## 2. Jito bundle creation

**Light:** atomic launch + pre-buy for liquidity bootstrapping.

**Dark:**
- `/api/create-bundle` accepts up to 4 pre-buyer wallets. Standard pattern: creator bundles themselves + 3 sybils, captures 20–40% of supply at curve minimum, dumps into retail FOMO.
- `holdings-visible-on-chain ≠ holders-distinct`. Concentrated supply masquerades as distributed by splitting across fresh wallets funded from a common source pre-launch.
- Bundle enables **MEV-proof sniping**: the launcher sees their tx and peer-buyers' txs atomically, retail can't front-run.

**Defense:** inspect creator wallet funding graph back ~5 hops, correlate top-10 holder funding timestamps within ±5 minutes of launch. Same funder → same entity.

## 3. PumpSwap pool LP position

**Light:** graduated token migrates to pumpswap pool, retail can LP alongside.

**Dark:**
- **LP position is an SPL NFT (or equivalent position account).** Whoever holds it can withdraw proportional reserves. Revoked *mint* authority says nothing about LP ownership.
- Single-entity LP concentration = exit ladder. Pull on dump, repopulate on FOMO.
- Meteora side pools (NASH has one) offer private-mempool execution paths the main pumpswap pool can be arbed against by the LP holder who sees both.

**Defense:** resolve LP position owner. If it's the creator or a fresh wallet, assume rugpullable. If it's a lock contract (Streamflow, Jupiter lock) with timelock visible on-chain, mitigated.

## 4. MCP server / Telegram bot automation

**Light:** user convenience, agentic trading.

**Dark:**
- `nirholas/pump-fun-sdk` ships an MCP server. Anyone plugging it into an LLM is authorizing the LLM to submit signed transactions. Prompt injection in a token's IPFS metadata, name, or pool comment field → LLM can be coerced into trading against the user.
- Telegram bot bots often run with hot-wallet keys. Social-engineered commands via group poison = wallet drain.
- Volume-reward farming loops via MCP create visible patterns that sophisticated searchers trivially sandwich.

**Defense:** LLM agent must never sign from a hot wallet without confirmation; all token metadata/URIs must be treated as untrusted user input; run the MCP server in read-only mode by default, require explicit human confirmation for signed operations.

## 5. Metadata / IPFS URI

**Light:** permanent soul of the token, immutable after authority revocation.

**Dark:**
- IPFS URI is immutable, but **IPFS content is only pinned as long as someone pins it.** Rely on the URI as canonical → future unpinning erases the token's soul. Creator can revive a pinner that serves *different bytes* at the same CID only if the CID is non-content-addressed (it isn't for CIDv1-bafy) — but gateways can still MITM lazy clients.
- Additional metadata fields (via `additionalMetadata` on tokenMetadata extension) were empty for NASH, but in general these can carry prompt-injection payloads to LLM routers.

**Defense:** fetch URI once, hash the bytes, pin to your own IPFS node. Reference by hash, not by URL. Treat `additionalMetadata` as untrusted.

## 6. Pool price oracle abuse

**Light:** AMM spot price as fair value.

**Dark:**
- Thin pool ($25k liquidity on NASH) → spot price trivially manipulable by a $2k swap. Anything that oracles pumpswap spot (lending, perps, options) is exploitable.
- Multi-pool spread (pumpswap + Meteora) creates sandwichable state across venues.

**Defense:** TWAP over >= 30 min, cross-venue median, reject oracle updates when pool depth < threshold.

## 7. State bridge / cross-chain wrap

**Light:** LayerZero OFT wrap to Aptos/ETH extends reach.

**Dark:**
- Wrapped version on destination chain can be minted by bridge operator. If bridge is compromised (Wormhole $320M precedent), wrapped supply exceeds locked supply → wrapped collapses, Solana mint unaffected but utility path severed.
- Bridge tokens attract different holder populations than base; creates arb opportunities the base holders don't see.

**Defense:** prefer lockbox-on-Solana + canonical bridge with published proofs (LayerZero V2 with Stargate). Monitor lock vs mint parity on every bridge.

## Synthesis — the NASH test

For NASH specifically, the dark-path audit checklist:

- [ ] Fee-sharing config written? (If no: the "permissionless evolution" story is unfunded.)
- [ ] Creator wallet funded from a fresh CEX withdrawal vs. a wallet with prior pump.fun launches?
- [ ] Top-10 holders' funding within ±5 min of mint creation?
- [ ] PumpSwap LP position owner — creator, locked, or community multisig?
- [ ] Meteora side pool depth and LP owner?
- [ ] IPFS URI content pinned by ≥ 2 independent pinners?

All six green = clean permissionless base worth building veNASH + Nashator-stake on top of.
Any red = the "clean on-chain" story is a surface reading; real authority lives in the **off-mint** levers.

## GF(3) reading

```
Fee stream      = +1   generativity (ongoing creation of value)
Bundle launch   =  0   ergodic (one-shot mixing at t=0)
LP / oracle     = −1   restraint (the only on-chain exit control)
```

Σ = 0 only if all three levers have decentralized/locked ownership. A revoked mint triad + centralized LP + centralized fee recipient = Σ = +1 mod 3 ≡ +1 = active extraction. The mint revocations are **necessary but not sufficient** for the triad to close.
