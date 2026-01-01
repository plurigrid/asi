# Phase A.0 Execution Plan - Operational Validation

**Status:** Ready to Execute

**Date:** 2025-12-27

**Goal:** Identify and fix GF(3) conservation violation, verify 315-skill installation succeeds, establish operational baselines for Phase A.1 formalization.

---

## Quick Start (5 Minutes)

### Step 1: Start Real-Time Monitor
```bash
# In one terminal, start monitoring
cd /Users/bob/ies/asi
./scripts/phase_a0_realtime_monitor.sh &
MONITOR_PID=$!
echo "Monitor running with PID: $MONITOR_PID"
```

### Step 2: Run 315-Skill Installation
```bash
# In another terminal, trigger installation
npx ai-agent-skills install plurigrid/asi --agent crush --verbose
```

### Step 3: Watch for Issues
The monitor will display real-time GF(3) metrics:
```
[Sample 1 @ 2025-12-27T12:34:56Z]
  PLUS (causality):        42 activities
  ERGODIC (2-monad):       38 activities
  MINUS (amp):             40 activities
  GF(3) Imbalance:         2
  Memory Usage:            45%

[Sample 2 @ 2025-12-27T12:35:01Z]
  PLUS (causality):        85 activities
  ERGODIC (2-monad):       75 activities
  MINUS (amp):             78 activities
  GF(3) Imbalance:         1
  Memory Usage:            62%

⚠️ ALERT: Protocol error detected!
   Likely root cause: ERGODIC STARVATION
```

### Step 4: Diagnose Root Cause
```bash
# Once error is detected, analyze logs
./scripts/diagnose_gf3_protocol_error.sh /Users/bob/.crush/logs/crush.log
```

### Step 5: Apply Fix
```bash
# Copy recommended strategy
cp .claude/mcp-gf3-fixes.json#strategy_X .claude/mcp.json

# Commit and retest
git add .claude/mcp.json && git commit -m "fix: Apply GF(3) conservation fix (Strategy X)"
npx ai-agent-skills install plurigrid/asi --agent crush
```

---

## Full Execution Workflow (2 Weeks)

### Week 1: Diagnostics and Root Cause Analysis

#### Days 1-2: Data Gathering
1. **Run baseline installation** with real-time monitoring
   - Capture metrics for full 315-skill installation
   - Note where (if) protocol errors occur
   - Document memory, latency, queue depth

2. **Analyze agent activity patterns**
   ```bash
   # After installation completes or fails:
   ./scripts/diagnose_gf3_protocol_error.sh /Users/bob/.crush/logs/crush.log
   ```
   - Which agent shows first signs of stress?
   - Does memory grow monotonically?
   - Are there latency spikes?

3. **Generate diagnostic report**
   ```
   Root Cause Analysis Report
   ├─ Root Cause: [PLUS/ERGODIC/MINUS/Semantic]
   ├─ Probability: [High/Medium/Low]
   ├─ Operational Signatures: [list of observed failures]
   └─ Recommended Fix: Strategy [A/B/C/D]
   ```

#### Days 3-4: Hypothesis Verification
1. **Run targeted diagnostic queries**
   - If PLUS overflow suspected: Check causality generation rate
   - If ERGODIC starvation: Measure 2-monad latency
   - If MINUS exhaustion: Check verification budget usage
   - If semantic violation: Find which skill causes issue

2. **Confirm root cause with secondary evidence**
   - Measure rates at different time points
   - Correlate failures with specific agents
   - Document exact failure point (which skill triggered error)

---

### Week 1-2: Fix Application and Verification

#### Days 5-7: Fix Strategy Selection and Application

**Strategy A: Increase ERGODIC Capacity** (if 2-monad latency is issue)
```bash
# Edit .claude/mcp.json
cp .claude/mcp-gf3-fixes.json#strategy_A .claude/mcp.json
git add .claude/mcp.json
git commit -m "fix: Apply Strategy A - increase ERGODIC routing capacity"
```

**Strategy B: Throttle PLUS Generation** (if causality rate exceeds capacity)
```bash
cp .claude/mcp-gf3-fixes.json#strategy_B .claude/mcp.json
git add .claude/mcp.json
git commit -m "fix: Apply Strategy B - throttle PLUS generative rate"
```

**Strategy C: Increase MINUS Budget** (if amp verification is bottleneck)
```bash
cp .claude/mcp-gf3-fixes.json#strategy_C .claude/mcp.json
git add .claude/mcp.json
git commit -m "fix: Apply Strategy C - increase MINUS verification budget"
```

**Strategy D: Rebalance All Three** (if multiple agents stressed)
```bash
cp .claude/mcp-gf3-fixes.json#strategy_D .claude/mcp.json
git add .claude/mcp.json
git commit -m "fix: Apply Strategy D - rebalance all three agents"
```

#### Days 8-10: Verification and Baseline Establishment

1. **Rerun 315-skill installation with fixed config**
   ```bash
   # Start monitor again
   ./scripts/phase_a0_realtime_monitor.sh &

   # Run installation
   npx ai-agent-skills install plurigrid/asi --agent crush
   ```

2. **Success Criteria (ALL must pass)**
   - ✅ All 315 skills installed without interruption
   - ✅ No "protocol error" messages in logs
   - ✅ No timeouts or backpressure signals
   - ✅ GF(3) imbalance stays ≤ 1 throughout
   - ✅ Memory usage never exceeds 80%
   - ✅ Installation completes in < 30 minutes

3. **If successful: Document operational baseline**
   ```bash
   # Create report
   cat > PHASE_A0_VALIDATION_REPORT_$(date +%Y%m%d).md << 'EOF'
   # Phase A.0 Operational Validation Report

   ## Configuration Applied
   - Strategy: [A/B/C/D]
   - causality.generation_rate: [X]
   - 2-monad.workers: [X]
   - amp.verification_budget: [X]

   ## Metrics
   - Total installation time: X minutes
   - Peak memory usage: X%
   - Peak queue depth: X% of max
   - GF(3) max imbalance: X
   - Protocol errors: 0 ✓

   ## Status
   ✓ OPERATIONAL - System stable, ready for Phase A.1 formalization
   EOF

   git add PHASE_A0_VALIDATION_REPORT_*.md
   git commit -m "docs: Phase A.0 operational validation completed"
   ```

4. **If unsuccessful: Iterate**
   - If different symptoms: Try next strategy
   - If same symptoms worsen: Combine strategies (e.g., A + B)
   - Document learnings for next iteration

---

## Diagnostic Commands (Reference)

### Real-Time Monitoring
```bash
# Start monitoring in background
./scripts/phase_a0_realtime_monitor.sh &

# Track specific agent activity
tail -f /Users/bob/.crush/logs/crush.log | grep -E "causality|2-monad|amp"
```

### Root Cause Identification
```bash
# Automated diagnosis
./scripts/diagnose_gf3_protocol_error.sh /Users/bob/.crush/logs/crush.log

# Manual analysis
grep "protocol error\|json.*error\|closed" /Users/bob/.crush/logs/crush.log

# Count agent activities
grep -c "causality\|move.*gen" /Users/bob/.crush/logs/crush.log
grep -c "2-monad\|routing" /Users/bob/.crush/logs/crush.log
grep -c "amp\|verification" /Users/bob/.crush/logs/crush.log
```

### Performance Metrics
```bash
# Memory usage during installation
vm_stat | grep "Pages active"

# Check for queue buildup
# (Would need logging in crush agent to measure)

# Verify fix applied
cat .claude/mcp.json | grep -A5 "causality\|2-monad\|amp"
```

---

## Success Indicators

### Phase A.0 Complete ✓
- [ ] Root cause identified (PLUS/ERGODIC/MINUS/Semantic)
- [ ] Fix strategy applied to .claude/mcp.json
- [ ] 315-skill installation completes without protocol errors
- [ ] GF(3) conservation verified (metrics show balance)
- [ ] Operational baseline documented in report
- [ ] All changes committed to git
- [ ] README updated with operational procedures

### Ready for Phase A.1 ✓
- [ ] System runs stably for minimum 1 hour without errors
- [ ] Same configuration can be applied repeatedly with consistent results
- [ ] Monitoring dashboard shows GF(3) balance maintained
- [ ] No degradation observed during extended operation

---

## If Installation Completes Successfully (Best Case)

**This means:** The 315-skill ecosystem is already operating within GF(3) balance.

**Next steps:**
1. Document what was working (no fix needed, but validate metrics)
2. Run extended stability test (24-hour operation)
3. Proceed directly to Phase A.1 (Bridge Type formalization)

---

## If Installation Fails Even After Fixes

**Possible solutions:**
1. **Increase all capacities** (A + B + C combined)
   ```bash
   # Create custom hybrid strategy combining all three
   ```

2. **Reduce verification strictness**
   - Lower `proof_cache_size`
   - Allow more skills to pass without full verification
   - Trade safety for progress (measure impact)

3. **Debug individual skill conflicts**
   - Identify which skill(s) cause the issue
   - Test with partial skill set (100 skills, 200 skills, etc.)
   - Find the breaking point

4. **Escalate to team**
   - Document all diagnostic output
   - Report exact skill count where failure occurs
   - Include full metrics and logs

---

## GF(3) Interpretation During Execution

### What Imbalance Means

**GF(3) Imbalance = 0 or 1:** ✓ Balanced system
- Trit sum ≡ 0 (mod 3)
- System is operating normally

**GF(3) Imbalance = 2:** ⚠️ Warning (minor imbalance)
- System is working but under stress
- Monitor closely, be ready to apply fixes

**GF(3) Imbalance ≥ 3:** ✗ Critical (severe imbalance)
- System entering failure state
- Protocol error likely imminent
- Intervention needed

---

## What Happens After Phase A.0

### Phase A.1: Bridge Type Formalization (Weeks 3-4)
Once operational system is stable, formalize it in Lean 4:
```lean
theorem ecosystem_operational_gf3_conserved :
  ∀ (change : SkillGraph → SkillGraph),
  (operational_system.installed_skills = 315) →
  (operational_system.gf3_conserved) →
  ∃ (proof : BridgeType),
    ecosystem.satisfies change proof
```

### Phase A.2-D: Proof and Instantiation
Build formal proofs that the operational system satisfies Bridge Type properties, then instantiate in music-topos and emmy-sicm.

---

## Timeline Summary

| Week | Days | Activity | Deliverable |
|------|------|----------|------------|
| 1 | 1-2 | Data gathering & monitoring | Metrics file |
| 1 | 3-4 | Root cause analysis | Diagnostic report |
| 2 | 5-7 | Fix strategy application | Updated config |
| 2 | 8-10 | Verification & baseline | Validation report |

**Total: 2 weeks, ready for Phase A.1**

---

**Start now. Execute with confidence. Document thoroughly.**

🚀 Phase A.0 is the foundation upon which all subsequent formalization is built.

