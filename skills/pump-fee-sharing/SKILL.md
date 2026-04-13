---
name: pump-fee-sharing
description: Creator fee configuration and distribution for Pump.fun — shareholder setup, BPS validation, fee collection
type: chain
trit: -1
---

# Pump Fee Sharing

Creator fee configuration and distribution.

## Trit: -1 (MINUS — Validator)

Validates fee share totals and distribution eligibility.

## Constraints

- Shares MUST total exactly **10,000 BPS**
- Maximum **10 shareholders**
- Setup is **one-time only**: `updateFeeShares` OR `collectWithoutSharing` (irreversible)

## Setup Fee Shares

```typescript
const ix = await sdk.updateFeeSharesInstruction({
  mint, creator: wallet.publicKey,
  shares: [
    { address: creator.publicKey, bps: 7000 },
    { address: partner.publicKey, bps: 3000 },
  ],
});
// Throws InvalidShareTotalError if sum != 10000
```

## Check Distributable Fees

```typescript
const result = await sdk.checkDistributableFees(mint);
// result.canDistribute, result.isGraduated
// Handles both graduated (AMM) and non-graduated (bonding curve) tokens
```

## Collect Fees

```typescript
const instructions = await sdk.collectCoinCreatorFeeInstructions(user);
```

## GF(3) Triad

```
pump-fee-sharing (-1) ⊗ pump-token-launch (0) ⊗ pump-graduation (+1) = 0 ✓
GF(3): (-1) + (0) + (+1) + (+1) + (-1) = 0 ✓ (all 5 skills balanced)
```
