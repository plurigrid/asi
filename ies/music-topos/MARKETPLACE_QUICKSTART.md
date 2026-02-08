# Marketplace Gateway - Quick Start Guide

**Get started with the unified API marketplace in 5 minutes**

---

## Step 1: Start the Server (30 seconds)

```bash
cd /Users/bob/ies/music-topos

# Start server
python marketplace_gateway.py

# You should see:
# INFO - Marketplace Gateway running on http://0.0.0.0:8080
# INFO - Registered 11 applications
```

**Alternative**: Using deployment script
```bash
./deploy_marketplace.sh start
```

---

## Step 2: Test Health Check (15 seconds)

```bash
curl http://localhost:8080/health
```

**Expected output**:
```json
{
  "status": "healthy",
  "apps_count": 11,
  "cached_results": 0
}
```

---

## Step 3: List Applications (30 seconds)

```bash
curl -H "X-API-Key: demo_key" http://localhost:8080/apps
```

**You'll see all 11 apps**:
- market_maker (ALPHA)
- composer, personalizer (BETA)
- consensus, query_engine (GAMMA)
- 6 baseline apps (color_navigator, world_navigator, etc.)

---

## Step 4: Execute Single App (1 minute)

### Example: Market Maker

```bash
curl -H "X-API-Key: demo_key" \
     -H "Content-Type: application/json" \
     -d '{
       "app_name": "market_maker",
       "params": {
         "query_type": "quote",
         "asset": "PROP",
         "amount": 1000.0
       }
     }' \
     http://localhost:8080/execute
```

**Output**:
```json
{
  "result_id": "abc-123",
  "status": "completed",
  "output": {
    "asset": "PROP",
    "bid": 0.995,
    "ask": 1.005,
    "spread": 0.01,
    "mid_price": 1.0
  },
  "execution_time_ms": 100.23,
  "gf3_valid": true
}
```

### Example: Composer

```bash
curl -H "X-API-Key: demo_key" \
     -H "Content-Type: application/json" \
     -d '{
       "app_name": "composer",
       "params": {
         "style": "classical",
         "length": 8,
         "key": "C"
       }
     }' \
     http://localhost:8080/execute
```

**Output**: Melody with 32 notes, 8 chords, tempo 120 BPM

---

## Step 5: Execute Composition Chain (2 minutes)

### Example: Music Personalization

```bash
curl -H "X-API-Key: demo_key" \
     -H "Content-Type: application/json" \
     -d '{
       "steps": [
         {
           "app_name": "composer",
           "input_mapping": {},
           "params": {"style": "jazz", "length": 16, "key": "Am"}
         },
         {
           "app_name": "personalizer",
           "input_mapping": {"key": "context"},
           "params": {"user_id": "user_123", "query_type": "recommend"}
         }
       ]
     }' \
     http://localhost:8080/compose
```

**Output**: Chain with 2 steps completed, composition + personalized recommendations

---

## Step 6: Run Client Examples (2 minutes)

```bash
# Make sure server is still running, then:
python marketplace_client_examples.py
```

**You'll see**:
- 10 example demonstrations
- All 11 applications in action
- 4 composition chain examples
- Real-time execution metrics

---

## Common Commands

### Start/Stop Server
```bash
./deploy_marketplace.sh start    # Start
./deploy_marketplace.sh stop     # Stop
./deploy_marketplace.sh restart  # Restart
./deploy_marketplace.sh status   # Check status
```

### Run Tests
```bash
pytest test_marketplace_gateway.py -v
```

### View Logs
```bash
./deploy_marketplace.sh logs
```

---

## Quick Reference: All 11 Apps

| App Name | Category | Use Case |
|----------|----------|----------|
| market_maker | ALPHA | Get quotes, check liquidity |
| composer | BETA | Generate music |
| personalizer | BETA | Get recommendations |
| consensus | GAMMA | Multi-agent voting |
| query_engine | GAMMA | Batch queries |
| color_navigator | Baseline | Explore GF(3) colors |
| world_navigator | Baseline | Traverse worlds |
| epistemology | Baseline | Query knowledge |
| active_inference | Baseline | Minimize free energy |
| pattern_discovery | Baseline | Find patterns |
| thread_analysis | Baseline | Analyze conversations |

---

## Quick Reference: Composition Chains

### Market Analysis
```
Market Maker → Consensus → Query Engine
```

### Music Personalization
```
Composer → Personalizer → Thread Analysis
```

### World Exploration
```
World Navigator → Epistemology → Pattern Discovery
```

### Active Inference Loop
```
Active Inference → Color Navigator → Consensus
```

---

## Troubleshooting

### "Connection refused"
→ Make sure server is running: `./deploy_marketplace.sh start`

### "Invalid API key"
→ Add header: `-H "X-API-Key: demo_key"`

### "Rate limit exceeded"
→ Wait 60 seconds or use different key

### "Port already in use"
→ Stop existing server: `./deploy_marketplace.sh stop`

---

## Next Steps

1. **Read Full Docs**: `MARKETPLACE_GATEWAY_README.md`
2. **View Examples**: `marketplace_client_examples.py`
3. **Check Tests**: `test_marketplace_gateway.py`
4. **See Delivery**: `MARKETPLACE_GATEWAY_DELIVERY_SUMMARY.md`

---

## Production Deployment

### Docker
```bash
docker build -f Dockerfile.marketplace -t marketplace-gateway .
docker run -p 8080:8080 marketplace-gateway
```

### Docker Compose
```bash
docker-compose -f docker-compose.marketplace.yml up -d
```

---

**That's it! You're ready to use the unified API marketplace.**

For questions, see the full README or run the examples.

---

**Generated with Claude Code**

Co-Authored-By: Claude Haiku 4.5 <noreply@anthropic.com>
