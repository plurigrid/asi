#!/usr/bin/env python3
"""
WEV Executor - Execute World Extractable Value trades based on *Able Markets signals.

Integrates with aptos-trading skill for actual APT execution.
Uses prediction market probabilities to size positions.

GF(3) Conservation: Long(+1) + MarketMaker(0) + Short(-1) = 0
"""

import os
import sys
import json
import math
import requests
from dataclasses import dataclass
from typing import Optional
from datetime import datetime

# Add aptos-trading to path
APTOS_TRADING_PATH = os.path.expanduser("~/.claude/skills/aptos-trading/scripts")
if os.path.exists(APTOS_TRADING_PATH):
    sys.path.insert(0, APTOS_TRADING_PATH)

@dataclass
class MarketSignal:
    proposal_id: str
    ecosystem: str
    able_trait: str
    implied_probability: float
    wev_apt: float
    signal: str  # "BUY", "SELL", "HOLD"
    confidence: float

@dataclass
class WEVParameters:
    """Parameters for WEV calculation"""
    accounts_at_risk: int = 10_000_000
    avg_value_apt: float = 100.0
    value_at_risk_ratio: float = 0.001
    
def calculate_wev(
    probability: float,
    params: WEVParameters = WEVParameters()
) -> float:
    """
    WEV(W₀ → W₁) = Σᵢ [V(entityᵢ, W₁) - V(entityᵢ, W₀)] × P(transition)
    """
    return (
        params.accounts_at_risk * 
        params.avg_value_apt * 
        probability * 
        params.value_at_risk_ratio
    )

def fetch_market_data() -> list[dict]:
    """Fetch current market state from dashboard API"""
    try:
        response = requests.get("http://localhost:3137/api/markets", timeout=5)
        return response.json()
    except:
        # Fallback to hardcoded data if dashboard not running
        return [
            {
                "proposalId": "AIP-137",
                "ecosystem": "aptos",
                "ableTrait": "PQ-Signable",
                "impliedProbability": 0.65,
                "status": "draft",
            },
            {
                "proposalId": "AIP-129", 
                "ecosystem": "aptos",
                "ableTrait": "Replay-Protectable",
                "impliedProbability": 0.80,
                "status": "draft",
            },
        ]

def generate_signals(markets: list[dict]) -> list[MarketSignal]:
    """Generate trading signals from market data"""
    signals = []
    
    for market in markets:
        prob = market.get("impliedProbability", 0.5)
        wev = calculate_wev(prob)
        
        # Signal generation logic
        if prob > 0.75:
            signal = "BUY"
            confidence = min(prob, 0.95)
        elif prob < 0.25:
            signal = "SELL"
            confidence = min(1 - prob, 0.95)
        else:
            signal = "HOLD"
            confidence = 0.5
        
        signals.append(MarketSignal(
            proposal_id=market["proposalId"],
            ecosystem=market["ecosystem"],
            able_trait=market["ableTrait"],
            implied_probability=prob,
            wev_apt=wev,
            signal=signal,
            confidence=confidence,
        ))
    
    return signals

def kelly_criterion(probability: float, odds: float = 2.0) -> float:
    """
    Kelly Criterion for optimal bet sizing.
    f* = (bp - q) / b
    where b = odds-1, p = win probability, q = 1-p
    """
    if probability <= 0 or probability >= 1:
        return 0.0
    
    b = odds - 1
    p = probability
    q = 1 - p
    
    kelly = (b * p - q) / b
    return max(0, min(kelly, 0.25))  # Cap at 25% of bankroll

def execute_wev_trade(signal: MarketSignal, bankroll_apt: float) -> Optional[dict]:
    """
    Execute WEV trade based on signal.
    Returns execution details or None if trade not taken.
    """
    if signal.signal == "HOLD":
        return None
    
    # Calculate position size using Kelly
    kelly_fraction = kelly_criterion(signal.implied_probability)
    position_size = bankroll_apt * kelly_fraction * signal.confidence
    
    if position_size < 1.0:  # Minimum 1 APT
        return None
    
    # Cap at WEV as maximum rational bet
    position_size = min(position_size, signal.wev_apt * 0.1)  # 10% of WEV
    
    return {
        "timestamp": datetime.now().isoformat(),
        "proposal_id": signal.proposal_id,
        "signal": signal.signal,
        "position_apt": round(position_size, 2),
        "kelly_fraction": round(kelly_fraction, 4),
        "implied_probability": round(signal.implied_probability, 4),
        "wev_apt": round(signal.wev_apt, 2),
        "confidence": round(signal.confidence, 4),
    }

def main():
    print("\n" + "=" * 60)
    print("  *Able Markets - WEV Executor")
    print("  GF(3): Long(+1) + MarketMaker(0) + Short(-1) = 0")
    print("=" * 60 + "\n")
    
    # Fetch market data
    print("📊 Fetching market data...")
    markets = fetch_market_data()
    print(f"   Found {len(markets)} markets\n")
    
    # Generate signals
    print("🎯 Generating signals...")
    signals = generate_signals(markets)
    
    for signal in signals:
        emoji = {"BUY": "🟢", "SELL": "🔴", "HOLD": "⚪"}[signal.signal]
        print(f"   {emoji} {signal.proposal_id}: {signal.signal}")
        print(f"      Probability: {signal.implied_probability:.1%}")
        print(f"      WEV: {signal.wev_apt:,.0f} APT")
        print(f"      Confidence: {signal.confidence:.1%}")
        print()
    
    # Simulate execution (would integrate with aptos-trading in production)
    print("💰 Execution Plan (simulated):")
    print("-" * 40)
    
    bankroll = 1000.0  # Simulated bankroll
    
    for signal in signals:
        trade = execute_wev_trade(signal, bankroll)
        if trade:
            print(f"\n   {trade['proposal_id']}:")
            print(f"      Action: {trade['signal']} {trade['position_apt']} APT")
            print(f"      Kelly: {trade['kelly_fraction']:.2%}")
            print(f"      Max WEV: {trade['wev_apt']:,.0f} APT")
        else:
            print(f"\n   {signal.proposal_id}: No trade (HOLD or size too small)")
    
    print("\n" + "=" * 60)
    print("  ⚠️  To execute live: integrate with aptos-trading skill")
    print("=" * 60 + "\n")
    
    return signals

if __name__ == "__main__":
    main()
