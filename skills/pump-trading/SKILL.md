---
name: pump-trading
description: Buy and sell instruction building for Pump.fun — client-side and server-side trading patterns
type: chain
trit: 1
---

# Pump Trading

Buy/sell execution patterns for Pump.fun tokens.

## Trit: +1 (PLUS — Generator)

Generates trading transactions.

## Client-Side (Official SDK)

```typescript
const instructions = await sdk.buyInstructions({
  global, bondingCurveAccountInfo, bondingCurve,
  associatedUserAccountInfo, mint, user: wallet.publicKey,
  solAmount, tokenAmount, slippageBps: 500,
});
// Sign and send yourself
```

## Server-Side (PumpDev Lightning)

```javascript
const res = await fetch('https://pumpdev.io/api/trade-lightning?api-key=KEY', {
  method: 'POST',
  body: JSON.stringify({ action: 'buy', mint: 'TOKEN_MINT', amount: 0.1,
    denominatedInSol: 'true', slippage: 5, priorityFee: 0.005 })
});
```

## Sell Pattern

```typescript
const instructions = await sdk.sellInstructions({
  global, bondingCurveAccountInfo, bondingCurve,
  associatedUserAccountInfo, mint, user: wallet.publicKey,
  tokenAmount, minSolOutput, slippageBps: 500,
});
```

## GF(3) Triad

```
pump-bonding-curve (-1) ⊗ pump-token-launch (0) ⊗ pump-trading (+1) = 0 ✓
```
