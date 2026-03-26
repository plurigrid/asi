---
name: elicit-prediction-market
description: Interface with the live Basin prediction market at elicit.attic.codes. Place bets, check positions, preview trades, monitor markets.
---

# Elicit Prediction Market

Live prediction market at **https://elicit.attic.codes** running basin-prediction (Rust CPMM).

## Auth

```bash
# Login (sets cookies in /tmp/elicit_cookies)
curl -s -c /tmp/elicit_cookies -X POST https://elicit.attic.codes/api/auth/login \
  -H 'Content-Type: application/json' \
  -d '{"username":"yulia","password":"normalizedvector"}'

# Check identity
curl -s -b /tmp/elicit_cookies https://elicit.attic.codes/api/auth/me
```

User: `yulia` (ID 10), role: `user`. CSRF header `X-Basin-Request: 1` required on all POST/DELETE.

## Read Markets

```bash
# List all markets
curl -s -b /tmp/elicit_cookies https://elicit.attic.codes/api/markets

# Single market + your position
curl -s -b /tmp/elicit_cookies https://elicit.attic.codes/api/markets/{id}

# Price history (array of {t: ms, p: [NO_prob, YES_prob]})
curl -s -b /tmp/elicit_cookies https://elicit.attic.codes/api/markets/{id}/history

# Trade log (limit/offset pagination)
curl -s -b /tmp/elicit_cookies "https://elicit.attic.codes/api/markets/{id}/trades?limit=20&offset=0"
```

## Preview Trades (dry run, no money moves)

```bash
# Preview buying $50 of YES shares
curl -s -b /tmp/elicit_cookies \
  "https://elicit.attic.codes/api/markets/{id}/preview?action=buy&outcome=1&amount=50"
# Returns: shares, avg_price, prob_before, prob_after, potential_payout

# Preview buying $50 of NO shares
curl -s -b /tmp/elicit_cookies \
  "https://elicit.attic.codes/api/markets/{id}/preview?action=buy&outcome=0&amount=50"

# Preview selling 10 YES shares
curl -s -b /tmp/elicit_cookies \
  "https://elicit.attic.codes/api/markets/{id}/preview?action=sell&outcome=1&amount=10"
# For sell, amount = number of shares. Returns: proceeds, realized_pnl
```

## Place Bets

```bash
# Buy YES shares (outcome=1) for $50
curl -s -b /tmp/elicit_cookies -X POST https://elicit.attic.codes/api/markets/{id}/buy \
  -H 'Content-Type: application/json' -H 'X-Basin-Request: 1' \
  -d '{"outcome": 1, "amount": 50.0}'
# Returns: {cost, shares, balance, probabilities}

# Buy NO shares (outcome=0) for $50
curl -s -b /tmp/elicit_cookies -X POST https://elicit.attic.codes/api/markets/{id}/buy \
  -H 'Content-Type: application/json' -H 'X-Basin-Request: 1' \
  -d '{"outcome": 0, "amount": 50.0}'

# Sell 10 YES shares
curl -s -b /tmp/elicit_cookies -X POST https://elicit.attic.codes/api/markets/{id}/sell \
  -H 'Content-Type: application/json' -H 'X-Basin-Request: 1' \
  -d '{"outcome": 1, "shares": 10.0}'
# Returns: {proceeds, shares (remaining), balance, probabilities, realized_pnl}

# Claim payout from resolved market
curl -s -b /tmp/elicit_cookies -X POST https://elicit.attic.codes/api/markets/{id}/claim \
  -H 'Content-Type: application/json' -H 'X-Basin-Request: 1' \
  -d '{}'
```

## Check Portfolio

```bash
# Your profile + all positions + total P&L
curl -s -b /tmp/elicit_cookies https://elicit.attic.codes/api/users/10

# Your trade history
curl -s -b /tmp/elicit_cookies "https://elicit.attic.codes/api/users/10/trades?limit=50"

# All users and balances
curl -s -b /tmp/elicit_cookies https://elicit.attic.codes/api/users/directory
```

## Outcomes

- `outcome: 0` = **NO**
- `outcome: 1` = **YES**
- Market status: `open`, `closed`, `resolved:outcome:0` (NO wins), `resolved:outcome:1` (YES wins), `resolved:percent:PPM`, `resolved:na`
- On resolution: winning shares pay $1 each, losing shares pay $0

## CPMM Math

Price = pool ratio. `yes_price = no_pool / (yes_pool + no_pool)`. Buying YES increases YES price. Pool invariant: `yes_pool * no_pool = k`.

## Current State (as of session)

| ID | Question | YES% | Trades | Volume | Status |
|----|----------|------|--------|--------|--------|
| 1 | Will this market work? | 92% | 16 | 274 | open |
| 3 | Will Dario show up at warehouse during stream? | 4% | 3 | 300 | open |
| 4 | Will the stream drop? | 97% | 12 | 594 | resolved:YES |
| 5 | Will we discover a new problematic bug in Basin? | 69% | 7 | 104 | open |
| 6 | Will Dario collaborate with Basin before end of Feb? | 6% | 7 | 305 | open |
| 7 | Will there be consensus a new egregore is born? | 34% | 11 | 2332 | open |

**Your position**: Market 7, 1049.13 YES shares @ $0.95 avg, unrealized P&L: -$720.15, balance: $0.00

## Kelly Criterion

For sizing bets given a belief:

```
kelly_fraction = (p * b - q) / b
where:
  p = your believed probability of YES
  q = 1 - p
  b = (1 / market_price) - 1  (net odds)
bet = kelly_fraction * bankroll * 0.25  (quarter-Kelly for safety)
```

## Script: Quick Trade

See `scripts/trade.sh` for a one-liner trade helper.
