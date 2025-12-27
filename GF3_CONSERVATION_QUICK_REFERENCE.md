# GF(3) Conservation: Quick Reference

**What is GF(3)?**
Galois Field with 3 elements: {-1, 0, +1}, addition mod 3

**Conservation Law:**
```
causality_trit + ergodic_trit + minus_trit ≡ 0 (mod 3)
    +1        +      0       +      -1    = 0 ✓
```

---

## The Three Agents and Their Trits

| Agent | Trit | Role | What It Does |
|-------|------|------|------------|
| **causality** | +1 | PLUS (Generation) | Generates candidate moves, explores possibilities |
| **2-monad** | 0 | ERGODIC (Coordination) | Routes moves, filters, maintains rhythm |
| **amp** | -1 | MINUS (Constraint) | Verifies moves, enforces safety, gates expansion |

---

## What Each Agent Conserves

### PLUS (+1): Generative Energy
- Prevents infinite loops
- Provides novelty and exploration
- Must be balanced by MINUS
- **If unchecked:** White Hole (explosion, incoherent)

### ERGODIC (0): Coordinating Capacity
- Routes between PLUS and MINUS
- Maintains timing and rhythm
- Holds context window
- **If bottlenecked:** System gridlocks, timing skew

### MINUS (-1): Constraining Power
- Verifies coherence
- Enforces invariants
- Prevents corruption
- **If exhausted:** System accepts invalid moves, enters BH

---

## The JSON RPC Protocol Error Explained

**Error:** `jsonrpc2: protocol error: read |0: file already closed`

**Root Causes (in probability order):**

1. **PLUS Overflow** (Most Likely)
   - causality generating faster than 2-monad routing
   - Indicator: Memory/queue pressure signals
   - Fix: Strategy B (throttle PLUS) or Strategy A (boost ERGODIC)

2. **ERGODIC Starvation**
   - 2-monad routing slower than causality rate + amp processing
   - Indicator: Growing latency from 2-monad
   - Fix: Strategy A (increase 2-monad workers/queue)

3. **MINUS Exhaustion**
   - amp verification budget depleted
   - Indicator: Verification failure signals
   - Fix: Strategy C (increase amp budget)

4. **Semantic Violation**
   - One skill violates Bridge Type coherence
   - Indicator: Neighbor-awareness constraints fail
   - Fix: Debug specific skill, reduce strictness, or Strategy D (rebalance)

---

## The Four Fix Strategies

### Strategy A: Increase ERGODIC Capacity
```json
{
  "2-monad": {
    "workers": 4,         // 2→4
    "queue_depth": 1000,  // 500→1000
    "filter_timeout_ms": 200  // 100→200
  }
}
```
**Use when:** latency from 2-monad is growing
**Cost:** More memory, slightly higher latency

---

### Strategy B: Throttle PLUS Generation
```json
{
  "causality": {
    "generation_rate": 5,  // 10→5
    "batch_size": 5,       // 10→5
    "backpressure_enabled": true  // false→true
  }
}
```
**Use when:** Memory/queue overflow detected
**Cost:** 2x slower total time, natural rhythm restored

---

### Strategy C: Increase MINUS Budget
```json
{
  "amp": {
    "verification_budget": 500,     // 100→500
    "parallel_verifiers": 4,        // 2→4
    "proof_cache_size": 10000       // 1000→10000
  }
}
```
**Use when:** Verification failures from amp detected
**Cost:** Higher CPU, larger memory for proof cache

---

### Strategy D: Balanced Reweighting
```json
{
  "causality": {"generation_rate": 8, "batch_size": 8},
  "2-monad": {"workers": 3, "queue_depth": 750},
  "amp": {"verification_budget": 300, "parallel_verifiers": 3}
}
```
**Use when:** Multiple agents showing issues
**Cost:** Moderate across all dimensions

---

## Diagnostic Workflow (5 Minutes)

```bash
# Step 1: Run diagnostic
./scripts/diagnose_gf3_protocol_error.sh .local/share/ies/logs/crush_latest.log

# Step 2: Look for root cause
# Output will show one of:
# - "PLUS OVERFLOW" → Use Strategy B or A
# - "ERGODIC STARVATION" → Use Strategy A
# - "MINUS EXHAUSTION" → Use Strategy C
# - "SEMANTIC VIOLATION" → Use Strategy D or debug skill

# Step 3: Apply fix
cp .claude/mcp-gf3-fixes.json#strategy_X .claude/mcp.json

# Step 4: Retest
npx ai-agent-skills install plurigrid/asi --agent crush

# Step 5: Verify success
grep "protocol error\|json" .local/share/ies/logs/crush_latest.log
# (Should be empty if successful)
```

---

## Operational GF(3) Signatures

### ✓ Coherent System
- Monotonic progress: 0 → 315 skills
- No backpressure signals
- No memory/queue warnings
- Consistent latency across agents
- No protocol errors
- Symmetry: generation ≈ verification + routing

### ✗ Incoherent System (GF(3) Violated)
- Stalled progress (stuck at skill N)
- Memory/queue warnings
- Growing latency
- Backpressure signals
- Protocol error drops connection
- Asymmetry: generation >> verification (or vice versa)

---

## Before/After Formalization

### Before Phase A.0 (Current State)
- System crashes at skill ~N with protocol error
- Cannot prove Bridge Type because system doesn't reach 315 skills
- Formalization would be meaningless

### After Phase A.0 (After Fix & Verification)
- System successfully reaches 315 skills
- All 315 skills installed, verified, coherent
- GF(3) conservation maintained throughout
- Ready for Phase A.1: Formalize the working system

### After Phase A.1-D (Full Implementation)
- Bridge Type formally proven in Lean 4
- Ecosystem proven to satisfy Bridge Type
- Three mechanisms formalized (Valve/Filter/Resurrector)
- Deployed in music-topos, emmy-sicm, UNWORLD federation

---

## The Conservation Equation

In terms of rates (per second):

```
rate(causality generates moves)
- rate(amp verifies moves)
= rate(2-monad routes moves)

10 moves/sec - 7 verified/sec ≈ 3 routed/sec (balanced)

If 10 - 0 = 10 → queue grows unbounded → PLUS OVERFLOW
If 10 - 7 = 3 but 2-monad can only route 2 → ERGODIC bottleneck
If 0 - 0 = 0 but nothing happens → MINUS exhausted or skill complete
```

---

## Success Checklist for Phase A.0

- [ ] Diagnostic script executed successfully
- [ ] Root cause identified (PLUS/ERGODIC/MINUS/Semantic)
- [ ] Appropriate fix strategy chosen
- [ ] MCP configuration updated
- [ ] crush validation rerun
- [ ] All 315 skills installed without error
- [ ] No protocol error in logs
- [ ] GF(3) conservation verified (trit sum = 0 throughout)
- [ ] Operational metrics documented
- [ ] Commit success report
- [ ] Ready for Phase A.1 (formal Lean 4)

---

## Key Insight

**GF(3) conservation is the operational manifestation of Bridge Type coherence.**

- Theoretically: Bridge Type = verified transition between extremes
- Operationally: GF(3) = balance that prevents White Hole (PLUS excess) and Black Hole (MINUS excess)
- When GF(3) is conserved, the system stays alive (rhythmic pulsing)
- When GF(3) is violated, the system dies (protocol error drops connection)

**Phase A.0 restores operational life. Phase A.1 formalizes why it works.**

---

