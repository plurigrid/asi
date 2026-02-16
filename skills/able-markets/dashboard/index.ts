// *Able Markets Dashboard - Bun.serve() Frontend
// Real-time prediction market visualization with Gay.jl colors

import index from "./index.html";

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

// Gay.jl color generation (SplitMix64)
function gayColor(seed: number, index: number): string {
  let state = BigInt(seed);
  for (let i = 0; i < index; i++) {
    state = (state + 0x9e3779b97f4a7c15n) & 0xffffffffffffffffn;
    let z = state;
    z = ((z ^ (z >> 30n)) * 0xbf58476d1ce4e5b9n) & 0xffffffffffffffffn;
    z = ((z ^ (z >> 27n)) * 0x94d049bb133111ebn) & 0xffffffffffffffffn;
    z = z ^ (z >> 31n);
    state = z;
  }
  const hue = Number(state % 360n);
  return `hsl(${hue}, 70%, 55%)`;
}

// LMSR calculations
function lmsrPriceYes(yesShares: number, noShares: number, liquidity: number): number {
  const expYes = Math.exp(yesShares / liquidity);
  const expNo = Math.exp(noShares / liquidity);
  return expYes / (expYes + expNo);
}

function lmsrCost(yesShares: number, noShares: number, liquidity: number): number {
  return liquidity * Math.log(
    Math.exp(yesShares / liquidity) + Math.exp(noShares / liquidity)
  );
}

// Mock market data (in production, fetch from Aptos node)
const markets: Market[] = [
  {
    proposalId: "AIP-137",
    ecosystem: "aptos",
    ableTrait: "PQ-Signable",
    trit: 0,
    color: "#19A845",
    yesShares: 150,
    noShares: 80,
    liquidity: 1000,
    impliedProbability: 0,
    status: "draft",
    lastCall: "02/09/2026",
  },
  {
    proposalId: "AIP-129",
    ecosystem: "aptos",
    ableTrait: "Replay-Protectable",
    trit: 1,
    color: "#E2F25B",
    yesShares: 200,
    noShares: 50,
    liquidity: 1000,
    impliedProbability: 0,
    status: "draft",
  },
  {
    proposalId: "SRFI-265",
    ecosystem: "srfi",
    ableTrait: "CFG-Composable",
    trit: -1,
    color: "#9068DA",
    yesShares: 60,
    noShares: 90,
    liquidity: 500,
    impliedProbability: 0,
    status: "draft",
  },
];

// Calculate implied probabilities
markets.forEach(m => {
  m.impliedProbability = lmsrPriceYes(m.yesShares, m.noShares, m.liquidity);
});

const trades: Trade[] = [];

Bun.serve({
  port: 3137, // Seed 137 reference
  
  routes: {
    "/": index,
    
    "/api/markets": {
      GET: () => Response.json(markets),
    },
    
    "/api/market/:id": {
      GET: (req) => {
        const market = markets.find(m => m.proposalId === req.params.id);
        if (!market) {
          return new Response("Market not found", { status: 404 });
        }
        return Response.json(market);
      },
    },
    
    "/api/trade": {
      POST: async (req) => {
        const body = await req.json() as { 
          proposalId: string; 
          direction: "yes" | "no"; 
          shares: number;
        };
        
        const market = markets.find(m => m.proposalId === body.proposalId);
        if (!market) {
          return new Response("Market not found", { status: 404 });
        }
        
        const oldCost = lmsrCost(market.yesShares, market.noShares, market.liquidity);
        
        if (body.direction === "yes") {
          market.yesShares += body.shares;
        } else {
          market.noShares += body.shares;
        }
        
        const newCost = lmsrCost(market.yesShares, market.noShares, market.liquidity);
        const tradeCost = newCost - oldCost;
        const newPrice = lmsrPriceYes(market.yesShares, market.noShares, market.liquidity);
        
        market.impliedProbability = newPrice;
        
        const trade: Trade = {
          timestamp: Date.now(),
          proposalId: body.proposalId,
          direction: body.direction,
          shares: body.shares,
          cost: tradeCost,
          newPrice,
        };
        trades.push(trade);
        
        return Response.json({ 
          success: true, 
          cost: tradeCost, 
          newPrice,
          market 
        });
      },
    },
    
    "/api/trades/:id": {
      GET: (req) => {
        const marketTrades = trades.filter(t => t.proposalId === req.params.id);
        return Response.json(marketTrades);
      },
    },
    
    "/api/wev/:id": {
      GET: (req) => {
        const market = markets.find(m => m.proposalId === req.params.id);
        if (!market) {
          return new Response("Market not found", { status: 404 });
        }
        
        // WEV calculation (AIP-137 specific)
        const accountsAtRisk = 10_000_000;
        const avgValueApt = 100;
        const probability = market.impliedProbability;
        const varRatio = 0.001;
        
        const wev = accountsAtRisk * avgValueApt * probability * varRatio;
        
        return Response.json({
          proposalId: market.proposalId,
          wevApt: wev,
          impliedProbability: probability,
          formula: "WEV = accounts × avg_value × P(accept) × VAR_ratio",
        });
      },
    },
    
    "/api/color/:seed/:index": {
      GET: (req) => {
        const seed = parseInt(req.params.seed);
        const index = parseInt(req.params.index);
        const color = gayColor(seed, index);
        return Response.json({ seed, index, color });
      },
    },
    
    "/api/arbitrage": {
      GET: () => {
        // Cross-ecosystem correlation detection
        const aptosMarkets = markets.filter(m => m.ecosystem === "aptos");
        const srfiMarkets = markets.filter(m => m.ecosystem === "srfi");
        
        const signals: { signal: string; markets: string[]; reason: string }[] = [];
        
        // If SRFI adopts pattern, Aptos might follow
        for (const srfi of srfiMarkets) {
          if (srfi.impliedProbability > 0.7) {
            for (const aptos of aptosMarkets) {
              if (aptos.impliedProbability < 0.4) {
                signals.push({
                  signal: "BUY",
                  markets: [aptos.proposalId],
                  reason: `${srfi.proposalId} leading indicator (${(srfi.impliedProbability * 100).toFixed(1)}%)`,
                });
              }
            }
          }
        }
        
        return Response.json({ signals, timestamp: Date.now() });
      },
    },
  },
  
  development: {
    hmr: true,
    console: true,
  },
});

console.log("🎯 *Able Markets Dashboard running at http://localhost:3137");
