---
name: pump-graduation
description: Bonding curve graduation detection and AMM migration — threshold monitoring, PumpAMM pool interaction
type: chain
trit: 1
---

# Pump Graduation

Monitors bonding curve completion and AMM migration.

## Trit: +1 (PLUS — Generator)

Generates graduation events and AMM pool state.

## Graduation Check

```typescript
const progress = await sdk.fetchGraduationProgress(mint);
// progress.progressBps — 0 to 10000 (0% to 100%)
// progress.isGraduated — boolean
```

## Summary

```typescript
const summary = await sdk.fetchBondingCurveSummary(mint);
// summary.marketCapSol, summary.progressBps, summary.isGraduated
```

## AMM Pool (Post-Graduation)

After graduation, tokens trade on PumpAMM (`pAMMBay6oceH9fJKBRHGP5D4bD4sWpmSwMn52FMfXEA`).

```typescript
// OnlinePumpSdk methods for graduated tokens:
await sdk.fetchAmmPool(mint);
await sdk.ammBuyInstructions({ pool, user, solAmount, minTokenAmount });
await sdk.ammSellInstructions({ pool, user, tokenAmount, minSolAmount });
```

## GF(3) Triad

```
pump-fee-sharing (-1) ⊗ pump-token-launch (0) ⊗ pump-graduation (+1) = 0 ✓
```
