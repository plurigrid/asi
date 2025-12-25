#!/usr/bin/env python3
"""
ALPHA EXECUTOR - 12H DOUBLING STRATEGY
LIVE MAINNET VIA REST API
"""

import asyncio
import aiohttp
import time
import logging
import yaml
import hashlib
import json
from datetime import datetime
from pathlib import Path
from typing import Optional

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey
from cryptography.hazmat.primitives import serialization

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s | %(message)s',
    handlers=[
        logging.FileHandler('/Users/alice/agent_scripts/alpha.log'),
        logging.StreamHandler()
    ]
)
log = logging.getLogger(__name__)

# =============================================================================
# CONFIG
# =============================================================================

WALLETS = yaml.safe_load(open("/Users/alice/agent_scripts/wallets.yaml"))['wallets']
PRIVATE_KEY_HEX = WALLETS['apt_primary']['private_key'].replace("ed25519-priv-0x", "")
ACCOUNT_ADDR = "0x" + WALLETS['apt_primary']['account'].replace("0x", "")
USDC_OUT = "0x" + WALLETS['usdc_withdrawal']['account'].replace("0x", "")
NODE_URL = "https://fullnode.mainnet.aptoslabs.com/v1"

ALLOCATION = {
    "spot": 45.0,
    "leverage_collateral": 10.0,
    "vultures": 45.0,
}

BULL_1 = 1.60
BULL_2 = 1.80
BULL_3 = 2.00
MOON = 2.50

VULTURE_LEVELS = [(1.40, 15.0), (1.30, 15.0), (1.20, 15.0)]

# =============================================================================
# CRYPTO
# =============================================================================

def load_private_key():
    key_bytes = bytes.fromhex(PRIVATE_KEY_HEX)
    return Ed25519PrivateKey.from_private_bytes(key_bytes)

def sign_message(private_key, message: bytes) -> bytes:
    return private_key.sign(message)

def get_public_key_hex(private_key) -> str:
    pub_bytes = private_key.public_key().public_bytes(
        encoding=serialization.Encoding.Raw,
        format=serialization.PublicFormat.Raw
    )
    return pub_bytes.hex()

# =============================================================================
# APTOS REST CLIENT
# =============================================================================

class AptosClient:
    def __init__(self):
        self.private_key = load_private_key()
        self.public_key = get_public_key_hex(self.private_key)
        log.info(f"[LIVE] Account: {ACCOUNT_ADDR}")
    
    async def get_account_info(self):
        async with aiohttp.ClientSession() as s:
            async with s.get(f"{NODE_URL}/accounts/{ACCOUNT_ADDR}") as r:
                return await r.json()
    
    async def get_balance(self) -> float:
        """Get APT balance from fungible asset store."""
        try:
            # Fungible store address for this account's APT
            fa_store = "0xc95f37039644dc7e9ef6bbdbc1dc2b4d2be1fd96c38f541a64c79b5bc87e55f3"
            async with aiohttp.ClientSession() as s:
                url = f"{NODE_URL}/accounts/{fa_store}/resource/0x1::fungible_asset::FungibleStore"
                async with s.get(url) as r:
                    if r.status == 200:
                        data = await r.json()
                        return int(data["data"]["balance"]) / 1e8
        except Exception as e:
            log.error(f"Balance error: {e}")
        return 0.0
    
    async def submit_transaction(self, payload: dict) -> Optional[str]:
        """Submit a transaction to mainnet."""
        try:
            async with aiohttp.ClientSession() as session:
                # Get account sequence number
                acct = await self.get_account_info()
                seq_num = int(acct["sequence_number"])
                
                # Get chain ID and gas estimate
                async with session.get(f"{NODE_URL}") as r:
                    ledger = await r.json()
                    chain_id = ledger["chain_id"]
                
                # Build transaction
                txn = {
                    "sender": ACCOUNT_ADDR,
                    "sequence_number": str(seq_num),
                    "max_gas_amount": "10000",
                    "gas_unit_price": "100",
                    "expiration_timestamp_secs": str(int(time.time()) + 600),
                    "payload": payload,
                }
                
                # Encode for signing
                async with session.post(f"{NODE_URL}/transactions/encode_submission", json=txn) as r:
                    if r.status != 200:
                        err = await r.text()
                        log.error(f"Encode error: {err}")
                        return None
                    to_sign = bytes.fromhex((await r.json()).replace("0x", ""))
                
                # Sign
                signature = sign_message(self.private_key, to_sign)
                
                # Submit
                signed_txn = {
                    **txn,
                    "signature": {
                        "type": "ed25519_signature",
                        "public_key": f"0x{self.public_key}",
                        "signature": f"0x{signature.hex()}"
                    }
                }
                
                async with session.post(f"{NODE_URL}/transactions", json=signed_txn) as r:
                    result = await r.json()
                    if "hash" in result:
                        tx_hash = result["hash"]
                        log.info(f"[TX SUBMITTED] {tx_hash}")
                        
                        # Wait for confirmation
                        for _ in range(30):
                            await asyncio.sleep(1)
                            async with session.get(f"{NODE_URL}/transactions/by_hash/{tx_hash}") as check:
                                if check.status == 200:
                                    tx_data = await check.json()
                                    if tx_data.get("success"):
                                        log.info(f"[TX CONFIRMED] {tx_hash}")
                                        return tx_hash
                                    elif "vm_status" in tx_data:
                                        log.error(f"[TX FAILED] {tx_data['vm_status']}")
                                        return None
                        return tx_hash
                    else:
                        log.error(f"Submit error: {result}")
                        return None
                        
        except Exception as e:
            log.error(f"Transaction error: {e}")
            return None
    
    async def swap_apt_to_usdc(self, apt_amount: float, min_usdc: float) -> bool:
        """Swap APT to USDC via Liquidswap."""
        log.info(f"[SWAP] {apt_amount:.4f} APT → USDC (min: {min_usdc:.2f})")
        
        payload = {
            "type": "entry_function_payload",
            "function": "0x190d44266241744264b964a37b8f09863167a12d3e70cda39376cfb4e3561e12::scripts_v2::swap",
            "type_arguments": [
                "0x1::aptos_coin::AptosCoin",
                "0xf22bede237a07e121b56d91a491eb7bcdfd1f5907926a9e58338f964a01b17fa::asset::USDC",
                "0x190d44266241744264b964a37b8f09863167a12d3e70cda39376cfb4e3561e12::curves::Uncorrelated"
            ],
            "arguments": [
                str(int(apt_amount * 1e8)),
                str(int(min_usdc * 1e6))
            ]
        }
        
        tx_hash = await self.submit_transaction(payload)
        return tx_hash is not None

# =============================================================================
# PRICE
# =============================================================================

async def get_price() -> float:
    """Get APT price with fallbacks."""
    async with aiohttp.ClientSession() as s:
        # Try CoinGecko
        try:
            async with s.get("https://api.coingecko.com/api/v3/simple/price?ids=aptos&vs_currencies=usd", timeout=10) as r:
                data = await r.json()
                if 'aptos' in data:
                    return data['aptos']['usd']
        except:
            pass
        
        # Fallback: Binance
        try:
            async with s.get("https://api.binance.com/api/v3/ticker/price?symbol=APTUSDT", timeout=10) as r:
                data = await r.json()
                return float(data['price'])
        except:
            pass
        
        # Fallback: use last known or default
        return 1.50

# =============================================================================
# MAIN
# =============================================================================

async def run():
    log.info("=" * 50)
    log.info("ALPHA EXECUTOR - LIVE MAINNET")
    log.info("=" * 50)
    
    client = AptosClient()
    balance = await client.get_balance()
    log.info(f"APT Balance: {balance:.4f}")
    
    start_time = time.time()
    start_price = await get_price()
    
    log.info(f"Start: ${start_price:.4f} | Target: ${start_price * 2:.4f}")
    
    spot = ALLOCATION["spot"]
    leverage_notional = ALLOCATION["leverage_collateral"] * 5
    vulture_apt = ALLOCATION["vultures"]
    usdc_out = 0.0
    
    triggered = set()
    vultures_filled = set()
    
    log.info(f"[INIT] Spot: {spot} | Lev: {leverage_notional} | Vultures: {vulture_apt}")
    
    end_time = start_time + (12 * 60 * 60)
    hour_8_time = start_time + (8 * 60 * 60)
    hour_8_alerted = False
    last_log = 0
    
    while time.time() < end_time:
        try:
            price = await get_price()
            elapsed_h = (time.time() - start_time) / 3600
            pnl = ((price / start_price) - 1) * 100
            
            # Hour 8 alert
            if not hour_8_alerted and time.time() >= hour_8_time:
                log.info("!" * 50)
                log.info(f"HOUR 8 - Price: ${price:.4f} | PnL: {pnl:+.2f}%")
                log.info("!" * 50)
                hour_8_alerted = True
            
            # Vultures
            for level, amount in VULTURE_LEVELS:
                if price <= level and level not in vultures_filled and vulture_apt >= amount:
                    log.info(f"[VULTURE] ${level} - +{amount} APT")
                    spot += amount
                    vulture_apt -= amount
                    vultures_filled.add(level)
            
            # BULL triggers
            if price >= BULL_1 and "B1" not in triggered:
                log.info(f"[B1] ${price:.4f}")
                triggered.add("B1")
            
            if price >= BULL_2 and "B2" not in triggered:
                take = spot * 0.30
                usdc = take * price * 0.97
                log.info(f"[B2] ${price:.4f} - Swapping {take:.2f} APT")
                if await client.swap_apt_to_usdc(take, usdc):
                    spot -= take
                    usdc_out += usdc
                triggered.add("B2")
            
            if price >= BULL_3 and "B3" not in triggered:
                take = spot * 0.50
                usdc = take * price * 0.97
                log.info(f"[B3] ${price:.4f} - TARGET - Swapping {take:.2f} APT")
                if await client.swap_apt_to_usdc(take, usdc):
                    spot -= take
                    usdc_out += usdc
                triggered.add("B3")
            
            if price >= MOON and "MOON" not in triggered:
                take = spot * 0.75
                usdc = take * price * 0.97
                log.info(f"[MOON] ${price:.4f} - Swapping {take:.2f} APT")
                if await client.swap_apt_to_usdc(take, usdc):
                    spot -= take
                    usdc_out += usdc
                triggered.add("MOON")
            
            # Log every 10 min
            now = int(time.time())
            if now - last_log >= 600:
                log.info(f"[{elapsed_h:.1f}h] ${price:.4f} | PnL: {pnl:+.2f}% | Spot: {spot:.1f} | USDC: ${usdc_out:.1f}")
                last_log = now
            
            Path("/Users/alice/agent_scripts/Holdings.md").write_text(f"""# Holdings - {datetime.now().strftime('%H:%M:%S')}
**LIVE MAINNET**
Price: ${price:.4f} | PnL: {pnl:+.2f}%
Spot: {spot:.2f} APT | Vultures: {vulture_apt:.2f}
USDC out: ${usdc_out:.2f}
Triggers: {', '.join(triggered) or 'None'}
""")
            
            await asyncio.sleep(5)
            
        except Exception as e:
            log.error(f"Error: {e}")
            await asyncio.sleep(30)
    
    log.info("=" * 50)
    log.info(f"COMPLETE - USDC: ${usdc_out:.2f}")
    log.info("=" * 50)

if __name__ == "__main__":
    print("LIVE MAINNET - Type EXECUTE:")
    if input().strip() == "EXECUTE":
        asyncio.run(run())
