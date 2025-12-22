# Testing Locally with Babashka & Playwright

**Complete guide for running all 11 components locally with automated tests**

---

## Overview

Two testing approaches:

1. **Babashka Tests** (Pure Clojure, no browser needed)
   - Fast unit/integration tests of all components
   - No dependencies beyond Babashka
   - ~30 seconds to complete
   - Perfect for CI/CD

2. **Playwright Tests** (Browser automation)
   - Full end-to-end browser testing
   - Visual regression testing
   - Performance profiling
   - Cross-browser testing (Chrome, Firefox, Safari)
   - ~2 minutes to complete

---

## Quick Start

### Option 1: Babashka Tests (Recommended for Speed)

```bash
# Install Babashka (if not already installed)
brew install babashka

# Run all tests
bb test_local.bb

# Expected output:
# ✓ Component Availability Test (all 11 components)
# ✓ Architecture Layer Distribution (P0, P1, P2)
# ✓ Polarity Semantics (RED, BLUE, GREEN)
# ✓ Phase Hierarchy (Phase 1, 2, 3)
# ✓ Response Latency (P99 < 100ms)
# ✓ Component Routing (11 routes)
# ✓ Binary Artifacts (11 dylibs)
# ✓ Manifest Validity (spin.toml, Cargo.toml)
# ✓ Documentation (8 files)
# ✓ Performance Expectations (documented)
#
# Test Results: 10/10 PASSED
```

### Option 2: Playwright Tests (Full E2E)

```bash
# Install dependencies
npm install -D @playwright/test

# Run Playwright tests
npx playwright test

# Expected output:
# 12 test suites with 50+ tests
# HTML report in playwright-report/
# ~2 minutes total execution
```

### Option 3: Both (Complete Validation)

```bash
# Run Babashka first (fast)
bb test_local.bb

# Then run Playwright (comprehensive)
npx playwright test
```

---

## Detailed Setup

### Babashka Setup (No Additional Dependencies)

**1. Install Babashka**

```bash
brew install babashka
# or
curl -s https://raw.githubusercontent.com/babashka/babashka/master/install | bash
```

**2. Run Tests**

```bash
# Make script executable
chmod +x test_local.bb

# Run with Babashka
bb test_local.bb

# Run with explicit path
/usr/local/bin/bb test_local.bb
```

**3. What It Tests**

- ✅ All 11 components compile
- ✅ All binaries exist in target/debug/deps/
- ✅ Layer distribution (3 P0, 4 P1, 4 P2)
- ✅ Stream polarity semantics
- ✅ Phase hierarchy
- ✅ Response latency
- ✅ Component routing
- ✅ Binary artifacts
- ✅ Manifest validity
- ✅ Documentation completeness
- ✅ Performance expectations

**4. Expected Results**

```
═════════════════════════════════════════════════════════════════════
  Ramanujan CRDT Network - Babashka Local Test Suite
═════════════════════════════════════════════════════════════════════

1. COMPONENT AVAILABILITY TEST
✓ stream-red                  [8ms]
✓ stream-blue                 [7ms]
✓ stream-green                [6ms]
...
Availability: 11/11 components

2. ARCHITECTURE LAYER DISTRIBUTION
P0 Stream Components:     3/3 ✓
P1 Service Components:    4/4 ✓
P2 Interface Components:  4/4 ✓

3. POLARITY SEMANTICS (P0 STREAMS)
✓ stream-red (polarity +1)
✓ stream-blue (polarity -1)
✓ stream-green (polarity 0)

4. PHASE HIERARCHY (P1 SERVICES)
Phase 1 (CRDT Memoization): 1 component(s)
Phase 2 (E-Graph Saturation): 1 component(s)
Phase 3 (Agent Verification): 2 component(s)

5. RESPONSE LATENCY TEST
Min Latency: 5ms
Avg Latency: 8ms
P99 Latency: 12ms
Max Latency: 25ms
✓ P99 Latency SLA ✓ (target < 100ms)

6. COMPONENT ROUTING TEST
stream-red                → /stream/red/...
stream-blue               → /stream/blue/...
... (11 total routes)

7. COMPILED BINARY ARTIFACTS
✓ Found: libstream_red.dylib
✓ Found: libstream_blue.dylib
... (11 total binaries)

8. DEPLOYMENT MANIFEST VALIDITY
✓ spin.toml found
✓ Cargo.toml found
✓ spin.toml has manifest version
✓ spin.toml declares 11 components

9. DOCUMENTATION COMPLETENESS
Documentation files: 8/8
✓ LOCAL_TESTING_GUIDE.md (272 lines)
✓ ARCHITECTURE_GUIDE.md (756 lines)
... (8 total files)

10. PERFORMANCE EXPECTATIONS
Expected Performance Targets:
🧪 Throughput:      6,000-9,000 ops/sec per component
🧪 Total System:    60,000-90,000 ops/sec (11 components)
🧪 Latency P99:     < 100ms
🧪 Cache Hit Rate:  70-90% (CRDT), 10-20% (E-Graph)
🧪 Binary Size:     1.35-1.65 MB (WASM)
🧪 Cold Start:      < 100ms

═════════════════════════════════════════════════════════════════════
  Test Results: 10/10 PASSED
═════════════════════════════════════════════════════════════════════

✓ ALL TESTS PASSED!
```

---

### Playwright Setup (Browser Automation)

**1. Install Node.js and Dependencies**

```bash
# Install Node.js (if needed)
brew install node

# Navigate to project root
cd /Users/bob/ies/music-topos

# Install Playwright
npm install -D @playwright/test

# Install browsers
npx playwright install
```

**2. Run Tests**

```bash
# Run all tests
npx playwright test

# Run specific test file
npx playwright test test_playwright.ts

# Run tests matching pattern
npx playwright test --grep "Component Availability"

# Run in specific browser
npx playwright test --project chromium

# Run with UI mode (interactive)
npx playwright test --ui

# Debug mode
npx playwright test --debug
```

**3. View Results**

```bash
# Open HTML report
npx playwright show-report

# View JSON results
cat test-results.json | jq '.'

# View JUnit XML (for CI)
cat junit-results.xml
```

**4. What Playwright Tests**

- ✅ Component availability (12 tests)
- ✅ Architecture layers (4 tests)
- ✅ Stream polarity (4 tests)
- ✅ Phase hierarchy (4 tests)
- ✅ Interface integration (5 tests)
- ✅ Performance metrics (4 tests)
- ✅ Component routing (11 tests)
- ✅ Error handling (2 tests)
- ✅ Integration flows (3 tests)
- ✅ Visual regression (2 tests)
- ✅ Accessibility (1 test)
- ✅ Deployment readiness (2 tests)

**Total: 12 test suites with 50+ tests**

**5. Cross-Browser Testing**

```bash
# Run across all browsers (default)
npx playwright test

# Run specific browser
npx playwright test --project=chromium
npx playwright test --project=firefox
npx playwright test --project=webkit

# Run only on Linux
npx playwright test --project=chromium --os linux
```

---

## Performance Testing with Playwright

**Measure latency across components:**

```typescript
test('measure component latency', async ({ page }) => {
  const latencies = [];

  for (const component of components) {
    const start = Date.now();
    await page.goto(`${BASE_URL}${component.route}`);
    latencies.push(Date.now() - start);
  }

  const avg = latencies.reduce((a,b) => a+b) / latencies.length;
  const p99 = latencies.sort()[Math.floor(0.99*latencies.length)];

  console.log(`Average: ${avg}ms, P99: ${p99}ms`);
});
```

Expected results:
- P0 Streams: < 50ms average
- P1 Services: < 75ms average
- P2 Interfaces: < 100ms average
- Overall P99: < 100ms

---

## CI/CD Integration

### GitHub Actions Example

```yaml
name: Test Locally

on: [push, pull_request]

jobs:
  test:
    runs-on: macos-latest

    steps:
      - uses: actions/checkout@v3

      - name: Install Babashka
        run: brew install babashka

      - name: Run Babashka Tests
        run: bb test_local.bb

      - name: Setup Node.js
        uses: actions/setup-node@v3
        with:
          node-version: '18'

      - name: Install Playwright
        run: npm install -D @playwright/test && npx playwright install

      - name: Run Playwright Tests
        run: npx playwright test

      - name: Upload Report
        if: always()
        uses: actions/upload-artifact@v3
        with:
          name: playwright-report
          path: playwright-report/
```

---

## Troubleshooting

### Babashka Tests

**Issue**: `bb: command not found`
```bash
# Install Babashka
brew install babashka
```

**Issue**: `Cannot read file test_local.bb`
```bash
# Verify file exists
ls -la test_local.bb

# Make executable
chmod +x test_local.bb

# Run with explicit Babashka
bb test_local.bb
```

**Issue**: Tests timeout
```bash
# Increase timeout in test file
# Change :timeout-ms 5000 to :timeout-ms 10000
```

### Playwright Tests

**Issue**: `npx: command not found`
```bash
# Install Node.js
brew install node

# Verify installation
node --version
npm --version
```

**Issue**: `Failed to launch browser`
```bash
# Install browser dependencies
npx playwright install

# Reinstall all browsers
npx playwright install --with-deps
```

**Issue**: `Connection refused (port 3000)`
```bash
# Ensure components are running
# Spin or other server must be listening on localhost:3000

# Check what's listening
lsof -i :3000

# Start server
./spin up  # or your server command
```

**Issue**: Tests timeout on slow machine
```bash
# Increase timeout in playwright.config.ts
timeout: 60 * 1000  // 60 seconds instead of 30
```

---

## Performance Profiling with Playwright

**Generate detailed performance report:**

```typescript
test('profile component performance', async ({ page }) => {
  const metrics = {};

  for (const component of components) {
    const start = performance.now();
    const response = await page.goto(`${BASE_URL}${component.route}`);
    const elapsed = performance.now() - start;

    const perfData = await page.evaluate(() => ({
      timing: window.performance.timing,
      memory: performance.memory,
    }));

    metrics[component.id] = {
      latency: elapsed,
      performance: perfData,
      status: response?.status(),
    };
  }

  console.table(metrics);
});
```

---

## Complete Test Flow

### Manual Testing Workflow

```bash
# 1. Verify components are compiled
bash verify_local_build.sh

# 2. Run quick Babashka tests
bb test_local.bb

# 3. Setup and run Playwright tests
npm install -D @playwright/test
npx playwright install
npx playwright test

# 4. View detailed report
npx playwright show-report

# 5. Check results
cat test-results.json | jq '.stats'
```

### Automated CI/CD Workflow

```bash
# 1. Install all dependencies
brew install babashka
npm ci

# 2. Run all tests
bb test_local.bb
npx playwright test

# 3. Upload artifacts
# (handled by CI/CD platform)
```

---

## Test Results Summary

**Expected Results After Running All Tests:**

```
Babashka Tests:        10/10 PASSED ✓
Playwright Tests:      50+/50+ PASSED ✓
Total Execution Time:  ~90 seconds
Status:                READY FOR DEPLOYMENT
```

---

## Next Steps After Testing

If all tests pass:

1. **Deploy to Fermyon**
   ```bash
   ./spin deploy
   ```

2. **Monitor Deployment**
   ```bash
   https://app.fermyon.com
   ```

3. **Test Live Endpoints**
   ```bash
   curl https://stream-red.worm.sex/
   curl https://dashboard.worm.sex/
   ```

If tests fail:

1. Check error messages in test output
2. Review `LOCAL_TESTING_GUIDE.md` troubleshooting section
3. Run individual component tests with curl
4. Check component logs

---

## File Reference

**Test Files Created:**
- `test_local.bb` - Babashka test suite (10 tests)
- `test_playwright.ts` - Playwright test suite (50+ tests)
- `playwright.config.ts` - Playwright configuration

**Existing Support Files:**
- `verify_local_build.sh` - Binary verification
- `final_verification.sh` - Final readiness check
- `ARCHITECTURE_GUIDE.md` - Technical specification
- `FERMYON_DEPLOYMENT_GUIDE.md` - Deployment procedures

---

## Support Commands

```bash
# Check Babashka version
bb --version

# Check Node/npm versions
node --version
npm --version

# List installed Playwright browsers
npx playwright install --list

# Run single test
npx playwright test test_playwright.ts -g "Component Availability"

# Debug mode with inspector
npx playwright test --debug

# Run with verbose output
npx playwright test --verbose

# Generate coverage (if enabled)
npx playwright test --reporter=coverage
```

---

**Last Updated**: 2025-12-21
**Babashka Version**: 1.0+
**Playwright Version**: Latest
**Node Version**: 16+

Ready to test locally! 🚀
