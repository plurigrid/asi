# Trail of Bits Skills: Quick Reference Guide

## 🎯 When to Use Each Skill

### BLOCKCHAIN AUDITING (6 Ecosystems)

**Solana/Anchor Programs?**
→ Use `solana-vulnerability-scanner`
- Finds: arbitrary CPI, improper PDA validation, missing signer checks, sysvar spoofing

**Cosmos/CosmWasm?**
→ Use `cosmos-vulnerability-scanner`
- Finds: non-determinism, incorrect signers, ABCI panics, rounding errors

**Substrate/FRAME Pallets?**
→ Use `substrate-vulnerability-scanner`
- Finds: arithmetic overflow, panic DoS, incorrect weights, bad origin checks

**Cairo/StarkNet?**
→ Use `cairo-vulnerability-scanner`
- Finds: felt252 overflow, L1-L2 messaging issues, address conversion bugs, replay attacks

**Algorand/TEAL?**
→ Use `algorand-vulnerability-scanner`
- Finds: rekeying attacks, unchecked fees, missing field validation, access control issues

**TON/FunC?**
→ Use `ton-vulnerability-scanner`
- Finds: integer-as-boolean misuse, fake Jetton contracts, missing gas checks

---

### STATIC ANALYSIS

**Fast Pattern-Based Scanning?**
→ Use `semgrep`
- Custom YAML rules, taint mode, multi-language, quick feedback

**Deep Data Flow Analysis?**
→ Use `codeql`
- Taint tracking, complex queries, CI/CD integration, custom QL

**Multiple Scanner Results?**
→ Use `sarif-parsing`
- Aggregate findings, deduplicate, extract key vulnerabilities

**Need Custom Rules?**
→ Use `semgrep-rule-creator`
- Convert bug patterns into detection rules

---

### FUZZING & TEST GENERATION

**Binary/C/C++?**
→ Use `aflpp` (AFL++)
- Coverage-guided, instrumentation, efficient

**Need Harness?**
→ Use `harness-writing`
- Learn to write effective fuzzing targets

**Rust Project?**
→ Use `cargo-fuzz` or `ruzzy`
- Native Rust fuzzing with libFuzzer/custom frameworks

**Python Code?**
→ Use `atheris`
- Python fuzzing with coverage guidance

**Cryptographic Tests?**
→ Use `wycheproof`
- Standard test vectors from Google's Crypto Team

**Custom Fuzzing Campaigns?**
→ Use `libafl`
- Advanced strategies, parallel execution

**Continuous OSS Fuzzing?**
→ Use `ossfuzz`
- Integration with Google's OSS-Fuzz infrastructure

**Measure Coverage?**
→ Use `coverage-analysis`
- Assess fuzzing thoroughness

---

### CRYPTOGRAPHY

**Side-Channel Vulnerabilities?**
→ Use `constant-time-analysis`
- Detects: secret-dependent branches, division on secrets, timing leaks
- Supports: C, C++, Go, Rust, Swift, Java, Kotlin, C#, PHP, JS, TS, Python, Ruby

**Math Properties?**
→ Use `property-based-testing`
- Define invariants, auto-generate test cases

**Implementation Verification?**
→ Use `constant-time-testing`
- Verify constant-time properties at runtime

---

### SMART CONTRACT BEST PRACTICES

**Assess Code Quality?**
→ Use `code-maturity-assessor`
- 9 dimensions: arithmetic, auditing, access control, complexity, decentralization, docs, MEV, low-level, testing

**Improve Architecture?**
→ Use `guidelines-advisor`
- Upgradeability, implementation patterns, dependencies

**Get Audit Ready?**
→ Use `audit-prep-assistant`
- Checklist, static analysis, coverage, dead code removal

**Analyze Tokens?**
→ Use `token-integration-analyzer`
- ERC20/721 conformity, 20+ weird token patterns, scarcity analysis

**Map Entry Points?**
→ Use `entry-point-analyzer`
- Identify state-changing functions by access level

---

### CODE REVIEW & HUNTING

**Review Pull Requests?**
→ Use `differential-review`
- Security-focused diff analysis

**Hunt Similar Bugs?**
→ Use `variant-analysis`
- Find bug variants after discovering one

**Match Specification?**
→ Use `spec-to-code-compliance`
- Verify whitepaper vs implementation

**Find Dangerous APIs?**
→ Use `sharp-edges`
- Identify error-prone designs and footguns

---

### INFRASTRUCTURE & SPECIALIZED

**Analyze Burp Projects?**
→ Use `burpsuite-project-parser`
- Extract findings from .burp files via CLI

**Parse Debug Info?**
→ Use `dwarf-expert`
- Analyze DWARF debug symbols

**Web App Testing?**
→ Use `burp-suite`
- Full web application security testing

**Team Culture Analysis?**
→ Use `interpreting-culture-index`
- Interpret CI surveys and behavioral profiles

---

## 📋 Audit Checklists

### Pre-Audit Preparation (1-2 days)
```
□ audit-prep-assistant          → Generate checklist
□ code-maturity-assessor        → Score 9 dimensions
□ secure-workflow-guide         → 5-step plan
□ guidelines-advisor            → Best practices review
→ Readiness scorecard generated
```

### Smart Contract Audit (3-5 days)
```
□ entry-point-analyzer          → Map surface
□ code-maturity-assessor        → Deep assessment
□ guidelines-advisor            → Architecture review
□ blockchain-scanner            → Find vulns
□ variant-analysis              → Similar issues
□ semgrep + codeql              → Static analysis
□ sarif-parsing                 → Aggregate
→ Comprehensive audit report
```

### Fuzzing Campaign (1-2 weeks)
```
□ harness-writing               → Create targets
□ Select fuzzer                 → AFL++/libFuzzer/etc
□ property-based-testing        → Define invariants
□ coverage-analysis             → Measure depth
□ wycheproof (if crypto)        → Standard tests
→ Vulnerability report
```

### Cryptography Review (3-5 days)
```
□ constant-time-analysis        → Side-channels
□ property-based-testing        → Math properties
□ constant-time-testing         → Implementation
□ wycheproof                    → Test vectors
→ Crypto certification
```

---

## 🔄 Common Workflows

### Workflow 1: Bug Hunting
```
1. Find initial vulnerability (semgrep/codeql)
2. Use variant-analysis to find similar patterns
3. Create semgrep-rule-creator to formalize
4. Run across codebase
5. Aggregate with sarif-parsing
```

### Workflow 2: New Fuzzer Setup
```
1. Study harness-writing skill
2. Write fuzzing harness for target
3. Select appropriate fuzzer
4. Run fuzzing campaign
5. Use property-based-testing for invariants
6. Measure with coverage-analysis
```

### Workflow 3: Pre-Launch Security
```
1. audit-prep-assistant checklist
2. code-maturity-assessor scorecard
3. semgrep + codeql scanning
4. entry-point-analyzer for attack surface
5. differential-review on recent changes
6. Fix and re-scan
```

### Workflow 4: Blockchain Audit
```
1. Select blockchain ecosystem
2. Run blockchain-specific scanner
3. If EVM: token-integration-analyzer
4. spec-to-code-compliance check
5. Comprehensive audit report
```

---

## 🎓 Learning Resources

Each skill has `/references/` and `/workflows/` subdirectories with:
- Detailed guides
- Step-by-step tutorials
- Examples and case studies
- Best practices from Trail of Bits

Access at: `/Users/bob/i/asi/skills/<skill-name>/`

---

## 📊 Skills by Maturity

### Mature (Most Used)
- `codeql`, `semgrep`, `entry-point-analyzer`
- `solana-vulnerability-scanner`, `cosmos-vulnerability-scanner`
- `constant-time-analysis`, `variant-analysis`

### Advanced (Domain-Specific)
- `cairo-vulnerability-scanner`, `substrate-vulnerability-scanner`
- `libafl`, `property-based-testing`
- `spec-to-code-compliance`

### Specialized (Niche Use)
- `dwarf-expert`, `interpreting-culture-index`
- `burpsuite-project-parser`, `sharp-edges`

---

## 🔧 Integration with Existing Skills

| Trail of Bits | Pairs With |
|---------------|-----------|
| `audit-prep-assistant` | `skill-dispatch` (routing) |
| `semgrep-rule-creator` | `gay-mcp` (color-code rules) |
| `variant-analysis` | `bisimulation-game` (verify findings) |
| `codeql` + `sarif-parsing` | `duckdb-timetravel` (audit history) |
| All auditing skills | `audit-orchestrator` (ERGODIC - NEEDED) |

---

## 🚀 Next High-Value Features

1. **Create `audit-orchestrator` (ERGODIC)**
   - Route to MINUS auditors
   - Coordinate PLUS generators
   - Aggregate to DuckDB

2. **DuckDB Audit Schema**
   - Track findings over time
   - Cross-project comparison
   - GF(3) conservation checks

3. **MCP Servers**
   - solana-mcp (Anchor toolchain)
   - cosmos-mcp (CosmWasm SDK)
   - cairo-mcp (Starknet compiler)

4. **Gay.jl Color Mapping**
   - Critical: Red (0°)
   - High: Orange (30°)
   - Medium: Yellow (60°)
   - Low: Green (120°)
   - Info: Blue (240°)

5. **Bisimulation Verification**
   - Game protocol for fuzzer results
   - GF(3)-conserved verification

---

## 📞 Support

For detailed workflows and examples:
- See `/Users/bob/i/asi/TRAILOFBITS_CAPABILITIES.md`
- Check individual skill directories: `/Users/bob/i/asi/skills/*/`
- Visit: https://github.com/trailofbits/skills

---

**Last Updated**: 2026-01-15
**Total Skills**: 44 (Security-focused)
**Status**: ✅ Integrated and ready to use
