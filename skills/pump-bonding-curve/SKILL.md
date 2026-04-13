---
name: pump-bonding-curve
description: Bonding curve math for Pump.fun SDK — quote, slippage, market cap, graduation progress
type: chain
trit: -1
---

# Pump Bonding Curve

Bonding curve math primitives from the Pump.fun protocol on Solana.

## Trit: -1 (MINUS — Validator)

Validates price quotes and slippage before execution.

## Core Functions

| Function | Returns | Description |
|----------|---------|-------------|
| `getBuyTokenAmountFromSolAmount(global, curve, solAmount)` | `BN` | Tokens received for SOL input |
| `getBuySolAmountFromTokenAmount(global, curve, tokenAmount)` | `BN` | SOL cost for token amount |
| `getSellSolAmountFromTokenAmount(global, curve, tokenAmount)` | `BN` | SOL received for selling |
| `bondingCurveMarketCap(global, curve)` | `BN` | Current market cap in lamports |
| `getGraduationProgress(global, curve)` | `GraduationProgress` | Progress toward AMM migration |

## On-Chain Programs

| Program | ID | Purpose |
|---------|----|---------| 
| Pump | `6EF8rrecthR5Dkzon8Nwu78hRvfCKubJ14M5uBEwF6P` | Bonding curve ops |
| PumpAMM | `pAMMBay6oceH9fJKBRHGP5D4bD4sWpmSwMn52FMfXEA` | Graduated AMM pools |

## SDK

```bash
npm install @pump-fun/pump-sdk
```

```typescript
import { PUMP_SDK, getBuyTokenAmountFromSolAmount } from "@pump-fun/pump-sdk";
const global = await sdk.fetchGlobal();
const tokens = getBuyTokenAmountFromSolAmount(global, bondingCurve, solAmount);
```

## GF(3) Triad

```
pump-bonding-curve (-1) ⊗ pump-token-launch (0) ⊗ pump-trading (+1) = 0 ✓
```
