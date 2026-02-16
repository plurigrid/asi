import React, { useState, useEffect } from "react";
import { createRoot } from "react-dom/client";

interface Market {
  proposalId: string;
  ecosystem: string;
  ableTrait: string;
  trit: number;
  color: string;
  yesShares: number;
  noShares: number;
  liquidity: number;
  impliedProbability: number;
  status: string;
  lastCall?: string;
}

interface Trade {
  timestamp: number;
  proposalId: string;
  direction: "yes" | "no";
  shares: number;
  cost: number;
  newPrice: number;
}

const tritColors = {
  [-1]: "#9068DA", // Queryable - MINUS
  [0]: "#E3EF45",  // Derangeable - ERGODIC
  [1]: "#C335A8",  // Colorable - PLUS
};

const tritLabels = {
  [-1]: "MINUS (-1)",
  [0]: "ERGODIC (0)",
  [1]: "PLUS (+1)",
};

function MarketCard({ market, onTrade }: { market: Market; onTrade: (id: string, dir: "yes" | "no", shares: number) => void }) {
  const [shares, setShares] = useState(10);
  const probability = (market.impliedProbability * 100).toFixed(1);
  
  return (
    <div 
      className="bg-gray-800 rounded-lg p-6 border-l-4"
      style={{ borderLeftColor: market.color }}
    >
      <div className="flex justify-between items-start mb-4">
        <div>
          <h3 className="text-xl font-bold">{market.proposalId}</h3>
          <p className="text-gray-400 text-sm">{market.ableTrait}</p>
        </div>
        <span 
          className="px-3 py-1 rounded-full text-xs font-semibold"
          style={{ 
            backgroundColor: tritColors[market.trit as keyof typeof tritColors] + "33",
            color: tritColors[market.trit as keyof typeof tritColors]
          }}
        >
          {tritLabels[market.trit as keyof typeof tritLabels]}
        </span>
      </div>
      
      <div className="mb-4">
        <div className="flex justify-between text-sm mb-1">
          <span>Implied Probability</span>
          <span className="font-mono">{probability}%</span>
        </div>
        <div className="h-3 bg-gray-700 rounded-full overflow-hidden">
          <div 
            className="h-full bg-green-500 transition-all duration-300"
            style={{ width: `${probability}%` }}
          />
        </div>
      </div>
      
      <div className="grid grid-cols-2 gap-4 text-sm mb-4">
        <div>
          <span className="text-gray-400">YES Shares:</span>
          <span className="ml-2 font-mono">{market.yesShares}</span>
        </div>
        <div>
          <span className="text-gray-400">NO Shares:</span>
          <span className="ml-2 font-mono">{market.noShares}</span>
        </div>
        <div>
          <span className="text-gray-400">Status:</span>
          <span className="ml-2 capitalize">{market.status}</span>
        </div>
        <div>
          <span className="text-gray-400">Last Call:</span>
          <span className="ml-2">{market.lastCall || "—"}</span>
        </div>
      </div>
      
      <div className="flex gap-2 items-center">
        <input
          type="number"
          value={shares}
          onChange={(e) => setShares(parseInt(e.target.value) || 0)}
          className="w-20 bg-gray-700 rounded px-2 py-1 text-center"
          min="1"
        />
        <button
          onClick={() => onTrade(market.proposalId, "yes", shares)}
          className="flex-1 bg-green-600 hover:bg-green-700 rounded py-2 font-semibold transition"
        >
          BUY YES
        </button>
        <button
          onClick={() => onTrade(market.proposalId, "no", shares)}
          className="flex-1 bg-red-600 hover:bg-red-700 rounded py-2 font-semibold transition"
        >
          BUY NO
        </button>
      </div>
    </div>
  );
}

function WevDisplay({ proposalId }: { proposalId: string }) {
  const [wev, setWev] = useState<{ wevApt: number; impliedProbability: number } | null>(null);
  
  useEffect(() => {
    fetch(`/api/wev/${proposalId}`)
      .then(r => r.json())
      .then(setWev);
  }, [proposalId]);
  
  if (!wev) return null;
  
  return (
    <div className="bg-gray-800 rounded-lg p-4">
      <h4 className="text-sm text-gray-400 mb-2">World Extractable Value</h4>
      <p className="text-2xl font-bold text-green-400">
        {wev.wevApt.toLocaleString()} APT
      </p>
      <p className="text-xs text-gray-500 mt-1">
        At {(wev.impliedProbability * 100).toFixed(1)}% probability
      </p>
    </div>
  );
}

function ArbitragePanel() {
  const [signals, setSignals] = useState<{ signal: string; markets: string[]; reason: string }[]>([]);
  
  useEffect(() => {
    const fetchSignals = () => {
      fetch("/api/arbitrage")
        .then(r => r.json())
        .then(data => setSignals(data.signals));
    };
    fetchSignals();
    const interval = setInterval(fetchSignals, 5000);
    return () => clearInterval(interval);
  }, []);
  
  return (
    <div className="bg-gray-800 rounded-lg p-4">
      <h3 className="text-lg font-bold mb-3 flex items-center gap-2">
        <span className="text-yellow-400">⚡</span>
        Cross-Ecosystem Arbitrage
      </h3>
      {signals.length === 0 ? (
        <p className="text-gray-500 text-sm">No arbitrage opportunities detected</p>
      ) : (
        <div className="space-y-2">
          {signals.map((s, i) => (
            <div key={i} className="bg-gray-700 rounded p-3">
              <div className="flex items-center gap-2">
                <span className="bg-green-600 px-2 py-0.5 rounded text-xs font-bold">{s.signal}</span>
                <span className="font-mono">{s.markets.join(", ")}</span>
              </div>
              <p className="text-sm text-gray-400 mt-1">{s.reason}</p>
            </div>
          ))}
        </div>
      )}
    </div>
  );
}

function App() {
  const [markets, setMarkets] = useState<Market[]>([]);
  const [loading, setLoading] = useState(true);
  
  const fetchMarkets = () => {
    fetch("/api/markets")
      .then(r => r.json())
      .then(data => {
        setMarkets(data);
        setLoading(false);
      });
  };
  
  useEffect(() => {
    fetchMarkets();
  }, []);
  
  const handleTrade = async (proposalId: string, direction: "yes" | "no", shares: number) => {
    const res = await fetch("/api/trade", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ proposalId, direction, shares }),
    });
    const data = await res.json();
    if (data.success) {
      fetchMarkets();
    }
  };
  
  if (loading) {
    return (
      <div className="flex items-center justify-center min-h-screen">
        <div className="text-xl">Loading markets...</div>
      </div>
    );
  }
  
  return (
    <div className="max-w-6xl mx-auto p-6">
      <header className="mb-8">
        <h1 className="text-4xl font-bold mb-2">
          <span className="text-green-400">*</span>Able Markets
        </h1>
        <p className="text-gray-400">
          Protocol Prediction Markets • GF(3) Conservation • WEV Extraction
        </p>
        <div className="mt-4 h-1 gf3-conservation rounded" />
      </header>
      
      <div className="grid grid-cols-1 lg:grid-cols-3 gap-6 mb-8">
        {markets.map(market => (
          <MarketCard 
            key={market.proposalId} 
            market={market} 
            onTrade={handleTrade}
          />
        ))}
      </div>
      
      <div className="grid grid-cols-1 lg:grid-cols-2 gap-6">
        <div>
          <h3 className="text-lg font-bold mb-3">WEV by Proposal</h3>
          <div className="space-y-3">
            {markets.map(m => (
              <WevDisplay key={m.proposalId} proposalId={m.proposalId} />
            ))}
          </div>
        </div>
        <ArbitragePanel />
      </div>
      
      <footer className="mt-12 pt-6 border-t border-gray-700 text-center text-gray-500 text-sm">
        <p>GF(3): Long(+1) + MarketMaker(0) + Short(-1) = 0</p>
        <p className="mt-1">Seed: 137 • Color: #19A845</p>
      </footer>
    </div>
  );
}

const root = createRoot(document.getElementById("root")!);
root.render(<App />);
