# Vault Runbook: How to Collapse Safely, Once

## Prerequisites

- Vault key: `alice-aptos` profile in `~/.aptos/config.yaml`
- Contract: `0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b`
- Escrow: `0xda0d44ff75c4bcb6a0409f7dd69496674edb1904cdd14d0c542c5e65cd5d42f6`

## Collapse Workflow

### Phase 1: Pre-Collapse (Worldnet)

```bash
# 1. Verify ledger state
cd ~/.topos/GayMove/worldnet
bb decay.clj status

# 2. Apply final decay (if epoch boundary)
bb decay.clj decay

# 3. Freeze the ledger (NO MORE WRITES AFTER THIS)
bb decay.clj freeze > freeze_snapshot.json

# 4. Backup the database
cp ledger.duckdb ledger.duckdb.pre-collapse
```

**CRITICAL**: After `freeze`, no more events should be written to the ledger.

### Phase 2: On-Chain Resolution (Mainnet)

```bash
# 1. Check bifurcation state (view function, no gas)
aptos move view \
  --function-id 0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b::multiverse::get_bifurcation_info \
  --args address:<BIFURCATION_ADDR> \
  --profile alice-aptos

# 2. Resolve the bifurcation (oracle declares winner)
#    winner_is_a: true = belief_a wins, false = belief_b wins
aptos move run \
  --function-id 0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b::multiverse::resolve \
  --args address:<BIFURCATION_ADDR> bool:<winner_is_a> \
  --profile alice-aptos

# 3. Claim APT (vault receives all)
aptos move run \
  --function-id 0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b::multiverse::claim \
  --args address:<BIFURCATION_ADDR> u64:<amount> \
  --profile alice-aptos

# 4. Verify vault received APT
aptos account balance --profile alice-aptos
```

### Phase 3: Distribution (Vault → Agents)

```bash
# 1. Calculate payouts based on vault APT received
cd ~/.topos/GayMove/worldnet
bb decay.clj payout <VAULT_APT_AMOUNT> > payouts.json

# 2. Review payouts
cat payouts.json | jq '.payouts[] | "\(.agent): \(.apt_payout) APT (\(.pct)%)"'

# 3. Execute transfers (manual verification each)
for payout in $(cat payouts.json | jq -c '.payouts[]'); do
  agent=$(echo $payout | jq -r '.agent')
  amount=$(echo $payout | jq -r '.apt_payout')
  echo "Transfer $amount APT to $agent? (y/n)"
  read confirm
  if [ "$confirm" = "y" ]; then
    aptos move run \
      --function-id 0x1::aptos_account::transfer \
      --args address:$agent u64:$(echo "$amount * 100000000" | bc | cut -d. -f1) \
      --profile alice-aptos
  fi
done
```

## Rounding Rules

- **Floor** to 8 decimal places
- **Dust** (< 0.00000001 APT) remains in vault
- Document any rounding in `collapse_log.json`

## Safety Checklist

Before resolve:
- [ ] Ledger frozen (`freeze_snapshot.json` exists)
- [ ] Final epoch decay applied
- [ ] Database backed up
- [ ] Bifurcation expiry has passed
- [ ] Winner determination is correct

Before distribution:
- [ ] Vault received expected APT amount
- [ ] Payout sum ≤ vault balance
- [ ] Each agent address verified
- [ ] Rounding documented

## Error Recovery

### If resolve fails:
```bash
# Check if expiry has passed
aptos move view \
  --function-id 0xc793acdec12b4a63717b001e21bbb7a8564d5e9690f80d41f556c2d0d624cc7b::multiverse::get_bifurcation_info \
  --args address:<BIFURCATION_ADDR> \
  --profile alice-aptos
# Retry after expiry
```

### If claim fails:
```bash
# Check if already resolved
# Retry with correct amount (check remaining stake)
```

### If distribution fails mid-way:
```bash
# Log completed transfers
# Resume from last successful
# Never retry a successful transfer
```

## Post-Collapse

```bash
# 1. Archive everything
mkdir -p ~/.topos/GayMove/archives/$(date +%Y%m%d)
cp worldnet/ledger.duckdb worldnet/freeze_snapshot.json \
   payouts.json collapse_log.json \
   ~/.topos/GayMove/archives/$(date +%Y%m%d)/

# 2. Record on-chain transaction hashes
echo "resolve_tx: <HASH>" >> collapse_log.json
echo "claim_tx: <HASH>" >> collapse_log.json

# 3. Verify invariant held
# sum(distributed) + dust = vault_apt_received
```

## Command Reference

| Command | Purpose |
|---------|---------|
| `bb decay.clj status` | Show current state |
| `bb decay.clj decay` | Apply epoch decay |
| `bb decay.clj freeze` | Freeze before collapse |
| `bb decay.clj payout <apt>` | Calculate distribution |
| `aptos move view ...` | Read on-chain state |
| `aptos move run ...` | Execute on-chain tx |
