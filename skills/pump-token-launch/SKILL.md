---
name: pump-token-launch
description: Token creation and createAndBuy pattern for Pump.fun — metadata, IPFS, mint keypair, dev buy
type: chain
trit: 0
---

# Pump Token Launch

Token creation patterns for the Pump.fun protocol.

## Trit: 0 (ERGODIC — Coordinator)

Coordinates token creation with optional initial buy.

## Create Token

```typescript
const createIx = await PUMP_SDK.createV2Instruction({
  mint: mintKeypair.publicKey,
  name: "Token Name",
  symbol: "TKN",
  uri: "https://arweave.net/metadata.json",
  creator: wallet.publicKey,
});
```

## Create + Buy (Atomic)

```typescript
const instructions = await sdk.createAndBuyInstructions({
  global, mint, name: "Token", symbol: "TKN", uri,
  creator: wallet.publicKey,
  amount: getBuyTokenAmountFromSolAmount(global, null, solAmount),
});
```

## REST API (PumpDev Lightning)

```javascript
const res = await fetch('https://pumpdev.io/api/create-lightning?api-key=KEY', {
  method: 'POST',
  headers: { 'Content-Type': 'application/json' },
  body: JSON.stringify({ name, symbol, image, description, buyAmountSol: 0.1 })
});
```

## Jito Bundle Launch

```
POST /api/create-bundle — atomic multi-buyer launch (up to 4 wallets)
```

## GF(3) Triad

```
pump-bonding-curve (-1) ⊗ pump-token-launch (0) ⊗ pump-trading (+1) = 0 ✓
```
