---
name: cryptographic-audit
description: Audit cryptographic implementations for misuse, weak algorithms, improper key management, and TLS/certificate configuration issues. Uses testssl.sh, openssl, sslyze, and code review patterns. For authorized security assessments.
---

# Cryptographic Audit

## When to Use

Use when reviewing cryptographic implementations, auditing TLS configurations, assessing key management practices, or checking for common crypto anti-patterns in source code.

## Tool Reference

| Tool | Package | Purpose |
|------|---------|---------|
| `testssl.sh` | testssl.sh | TLS/SSL configuration scanner |
| `openssl` | openssl | Certificate/cipher inspection |
| `sslyze` | pip:sslyze | Python TLS scanner |
| `certtool` | gnutls | Certificate manipulation |
| `step` | smallstep/cli | CA and certificate toolkit |
| `age` | age | Modern file encryption |
| `minisign` | minisign | Signature verification |
| `hashid` | pip:hashid | Hash type identification |
| `john` | john | Password hash auditing |
| `hashcat` | hashcat | GPU hash cracking |
| `xortool` | pip:xortool | XOR cipher analysis |
| `featherduster` | featherduster | Automated crypto analysis |

## TLS Configuration Audit

### 1. Quick Scan

```bash
# Comprehensive TLS test
testssl.sh --severity HIGH https://target.com

# Check specific issues
testssl.sh --heartbleed --ccs --robot --breach https://target.com

# JSON output for processing
testssl.sh --jsonfile results.json https://target.com
```

### 2. Certificate Chain

```bash
# Download and inspect certificate chain
openssl s_client -connect target.com:443 -showcerts </dev/null 2>/dev/null | \
  openssl x509 -text -noout

# Check certificate expiry
echo | openssl s_client -connect target.com:443 2>/dev/null | \
  openssl x509 -noout -dates

# Verify certificate chain
openssl s_client -connect target.com:443 -verify 5 </dev/null

# Check for CT (Certificate Transparency) logs
openssl s_client -connect target.com:443 </dev/null 2>/dev/null | \
  openssl x509 -noout -ext ct_precert_scts

# SAN (Subject Alternative Names)
echo | openssl s_client -connect target.com:443 2>/dev/null | \
  openssl x509 -noout -ext subjectAltName
```

### 3. Cipher Suite Analysis

```bash
# List supported ciphers
nmap --script ssl-enum-ciphers -p 443 target.com

# Test specific cipher
openssl s_client -connect target.com:443 -cipher 'RC4-SHA'

# Check for weak ciphers
sslyze --regular target.com:443

# TLS 1.3 cipher suites
openssl s_client -connect target.com:443 -tls1_3 -ciphersuites 'TLS_AES_256_GCM_SHA384'
```

### 4. Protocol Version Testing

```bash
# Test each protocol version
for proto in ssl3 tls1 tls1_1 tls1_2 tls1_3; do
  echo -n "$proto: "
  openssl s_client -connect target.com:443 -$proto </dev/null 2>&1 | \
    grep -q "Cipher is" && echo "SUPPORTED" || echo "not supported"
done
```

### 5. HSTS and Security Headers

```bash
# Check HSTS header
curl -sI https://target.com | grep -i strict-transport

# Full security headers check
curl -sI https://target.com | grep -iE \
  'strict-transport|content-security|x-frame|x-content-type|referrer-policy'
```

## Key Management Audit

### 1. Private Key Assessment

```bash
# Check key strength
openssl rsa -in key.pem -text -noout | head -1
# Look for: RSA < 2048 bits = WEAK

# Check EC curve
openssl ec -in ec_key.pem -text -noout | grep ASN1
# Look for: < P-256 = WEAK, P-192 = CRITICAL

# Detect if key is encrypted
openssl rsa -in key.pem -check -noout 2>&1
# "unable to load" = encrypted (good)
# No error = unencrypted (finding)
```

### 2. Entropy Assessment

```bash
# Check /dev/urandom availability
ls -la /dev/urandom /dev/random

# Test PRNG output quality (basic)
dd if=/dev/urandom bs=1M count=10 2>/dev/null | ent

# Check OpenSSL PRNG seeding
openssl rand -hex 32  # Should succeed without errors
```

## Password Hashing Audit

```bash
# Identify hash type
hashid '$2b$12$LJ3...'
# => bcrypt

# Check hash strength
# WEAK: MD5, SHA1, SHA256 (unsalted/fast)
# OK: bcrypt ($2b$), scrypt, argon2
# BEST: argon2id with ≥64MB memory

# Benchmark cracking speed (measure weakness)
hashcat -b -m 0     # MD5: billions/sec = WEAK
hashcat -b -m 3200  # bcrypt: thousands/sec = OK
hashcat -b -m 13100 # argon2: tens/sec = STRONG
```

## Code Review Patterns

### Hardcoded Secrets
```python
# FINDING: Hardcoded cryptographic key
AES_KEY = b"0123456789abcdef"  # Static key in source
SECRET = "my-jwt-secret"       # Hardcoded JWT signing key

# GREP: Find hardcoded secrets
# grep -rn 'SECRET\|KEY\|PASSWORD\|TOKEN.*=.*["\x27]' --include='*.py'
```

### Weak Random Number Generation
```python
# FINDING: Using non-cryptographic PRNG for security
import random
token = random.randint(0, 999999)  # Predictable!
session_id = ''.join(random.choices(string.ascii_letters, k=32))

# FIX: Use secrets module
import secrets
token = secrets.token_hex(32)
```

### ECB Mode Usage
```python
# FINDING: ECB mode leaks patterns
cipher = AES.new(key, AES.MODE_ECB)  # NEVER use ECB

# FIX: Use GCM (authenticated encryption)
cipher = AES.new(key, AES.MODE_GCM, nonce=nonce)
```

### Nonce Reuse
```python
# FINDING: Static or reused nonce/IV
iv = b'\x00' * 16  # Static IV = catastrophic for CTR/GCM
cipher = AES.new(key, AES.MODE_GCM, nonce=iv)

# FIX: Generate fresh nonce per encryption
nonce = os.urandom(12)
```

### Padding Oracle Exposure
```python
# FINDING: Error message reveals padding validity
try:
    plaintext = cipher.decrypt(ciphertext)
    unpad(plaintext)
except PaddingError:
    return "Invalid padding"  # Oracle!
except:
    return "Decryption failed"

# FIX: Use authenticated encryption (GCM/ChaCha20-Poly1305)
# or return identical error for all failures
```

### Insecure Hash for Integrity
```python
# FINDING: MD5/SHA1 for integrity verification
checksum = hashlib.md5(data).hexdigest()  # Collision attacks practical

# FIX: Use SHA-256+ or HMAC
mac = hmac.new(key, data, hashlib.sha256).hexdigest()
```

### Missing Certificate Pinning
```python
# FINDING: No certificate pinning in mobile/API client
requests.get("https://api.example.com", verify=True)  # Trusts any valid CA

# Pin to specific certificate or public key hash
# Use: ssl.SSLContext with load_verify_locations() + custom check
```

### JWT Vulnerabilities
```python
# FINDING: JWT algorithm confusion
token = jwt.decode(token_string, key, algorithms=["HS256", "RS256", "none"])
# "none" algorithm = signature bypass
# HS256+RS256 = algorithm confusion attack

# FIX: Whitelist single algorithm
token = jwt.decode(token_string, key, algorithms=["RS256"])
```

## Grep Patterns for Crypto Issues

```bash
# Find weak algorithms
grep -rn 'MD5\|SHA1\|DES\|RC4\|ECB' --include='*.py' --include='*.js' --include='*.go' --include='*.java'

# Find hardcoded keys/secrets
grep -rn 'SECRET_KEY\|API_KEY\|PRIVATE.*=.*["'"'"']' --include='*.py' --include='*.env'

# Find insecure random
grep -rn 'Math\.random\|random\.randint\|rand()' --include='*.py' --include='*.js' --include='*.go'

# Find disabled TLS verification
grep -rn 'verify.*=.*False\|InsecureSkipVerify.*true\|NODE_TLS_REJECT_UNAUTHORIZED' .

# Find nonce/IV issues
grep -rn 'iv.*=.*b"\|nonce.*=.*b"\|IV.*=.*new byte' --include='*.py' --include='*.java'
```

## Output Format

```markdown
## Cryptographic Audit Report

### TLS Configuration

| Check | Status | Details |
|-------|--------|---------|
| Protocol versions | WARN | TLS 1.0/1.1 enabled |
| Cipher suites | FAIL | RC4, 3DES accepted |
| Certificate | PASS | RSA-2048, valid chain |
| HSTS | FAIL | Header missing |
| Forward secrecy | PASS | ECDHE supported |

### Cryptographic Implementation Findings

| # | Finding | Severity | File:Line |
|---|---------|----------|-----------|
| 1 | Hardcoded AES key | Critical | config.py:42 |
| 2 | ECB mode encryption | High | crypto.py:18 |
| 3 | MD5 for password hashing | High | auth.py:55 |
| 4 | Math.random() for tokens | High | session.js:12 |
| 5 | JWT "none" algorithm accepted | Critical | api.py:89 |

### Recommendations
1. Rotate all hardcoded keys to secrets manager
2. Replace ECB with AES-256-GCM
3. Migrate passwords to argon2id
4. Use crypto.getRandomValues() / secrets module
5. Pin JWT algorithm to RS256 only
```

## 2600 Heritage

Cryptography has been central to 2600 since the magazine's earliest issues. From covering PGP and the Clipper Chip in the 1990s crypto wars, to the DeCSS case (the landmark DMCA lawsuit against 2600 for publishing DVD decryption code), to modern TLS and end-to-end encryption advocacy — the magazine has consistently championed strong cryptography as a civil liberty.
