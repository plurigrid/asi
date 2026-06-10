---
name: trailofbits-security
description: '- `codeql` - GitHub''s semantic code analysis'
---
# Trail of Bits Security Bundle

> Provenance: Trail of Bits security research
> GF(3) Trit: **-1 (MINUS)** - Validation/Verification
> Mutual Awareness: `k-dense-ai` bundle (PLUS +1)

## Skills (43)

### Static Analysis
- `codeql` - GitHub's semantic code analysis
- `semgrep` - Fast pattern matching
- `semgrep-rule-creator` - Custom rule authoring
- `sarif-parsing` - SARIF report processing

### Fuzzing
- `aflpp` - AFL++ coverage-guided fuzzing
- `libfuzzer` - In-process fuzzing
- `libafl` - LibAFL framework
- `cargo-fuzz` - Rust fuzzing
- `atheris` - Python fuzzing
- `ruzzy` - Ruby fuzzing
- `ossfuzz` - Google OSS-Fuzz integration
- `harness-writing` - Fuzzing harness design
- `fuzzing-dictionary` - Dictionary optimization
- `fuzzing-obstacles` - Overcoming blockers

### Memory Safety
- `address-sanitizer` - ASan for C/C++
- `constant-time-analysis` - Timing side-channels
- `constant-time-testing` - CT verification

### Smart Contract Security
- `solana-vulnerability-scanner` - Solana programs
- `cairo-vulnerability-scanner` - StarkNet contracts
- `algorand-vulnerability-scanner` - Algorand TEAL
- `cosmos-vulnerability-scanner` - Cosmos SDK
- `substrate-vulnerability-scanner` - Polkadot pallets
- `ton-vulnerability-scanner` - TON contracts
- `move-smith-fuzzer` - Move language fuzzing
- `move-fuzzing` - Move program testing
- `token-integration-analyzer` - ERC20/721 compliance
- `entry-point-analyzer` - Attack surface mapping

### Code Review
- `audit-context-building` - Deep code analysis
- `audit-prep-assistant` - Pre-audit preparation
- `differential-review` - Diff security review
- `fix-review` - Patch verification
- `sharp-edges` - Dangerous API detection
- `code-maturity-assessor` - Codebase quality
- `guidelines-advisor` - Best practices
- `secure-workflow-guide` - SDLC security
- `spec-to-code-compliance` - Spec verification

### Web Security
- `burp-suite` - Web app testing
- `burpsuite-project-parser` - Burp file analysis

### Testing
- `property-based-testing` - Hypothesis/QuickCheck
- `coverage-analysis` - Code coverage
- `wycheproof` - Crypto test vectors

## Mutual Awareness Protocol

```clojure
{:bundle "trailofbits-security"
 :trit :minus
 :aware-of ["k-dense-ai"]
 :interface
 {:audit (fn [code] "Run static analysis + fuzzing")
  :validate (fn [data] "Check for injection/overflow")
  :verify (fn [claim] "Formal verification pathway")}
 :handoff-to "k-dense-ai"
 :handoff-trigger [:molecule-data :protein-sequence :scientific-computation]}
```

## Usage

```bash
# Load bundle
skill trailofbits-security

# Cross-bundle workflow
skill trailofbits-security -> k-dense-ai  # Audit bioinformatics pipeline security
```
