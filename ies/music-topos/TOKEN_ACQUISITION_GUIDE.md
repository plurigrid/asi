# API Token Acquisition Guide

**Status**: Step-by-step instructions for all required tokens
**Date**: 2025-12-21
**Estimated Time**: 15-30 minutes total

---

## Overview: Tokens Needed

| Service | Purpose | Required | Setup Time | Cost |
|---------|---------|----------|------------|------|
| GitHub | Repository & activity data | Yes | 5 min | Free |
| Firecrawl | Web content scraping | Yes | 10 min | Free tier available |
| Bluesky | Direct API access (optional) | No | 5 min | Free |
| NATS | Real-time updates | No | 0 min | Already configured |

---

## 1. GitHub Personal Access Token

### Step 1: Generate Token
1. Go to: **https://github.com/settings/tokens**
2. Click "Generate new token" → "Generate new token (classic)"
3. Name: `Phase1DataAcquisition`
4. Expiration: `90 days` (or longer)
5. Select scopes:
   - ✅ `repo` (full control of repositories)
   - ✅ `read:user` (read user data)
   - ✅ `read:org` (read organization data)

### Step 2: Copy Token
1. GitHub will show the token once
2. **Copy it immediately** (can't be retrieved later)
3. Keep it safe - never share or commit to git

### Step 3: Set Environment Variable
```bash
# Option A: One-time (current session only)
export GITHUB_TOKEN='github_pat_1234567890abcdef...'

# Option B: Permanent (add to ~/.bashrc or ~/.zshrc)
echo "export GITHUB_TOKEN='github_pat_1234567890abcdef...'" >> ~/.zshrc
source ~/.zshrc

# Option C: Verify it's set
echo $GITHUB_TOKEN  # Should print your token
```

### Step 4: Verify
```bash
# Test the token with curl
curl -H "Authorization: Bearer $GITHUB_TOKEN" \
  https://api.github.com/user
# Should return your GitHub user info
```

**✅ GitHub token is ready!**

---

## 2. Firecrawl API Key

### Step 1: Sign Up
1. Go to: **https://www.firecrawl.dev**
2. Click "Get Started" or "Sign Up"
3. Create account (email required)
4. Verify email

### Step 2: Get API Key
1. Log in to Firecrawl dashboard
2. Go to: **Settings** or **API Keys**
3. Click "Generate API Key"
4. Name it: `Phase1DataAcquisition`
5. Copy the key

### Step 3: Check Your Quota
1. Dashboard shows available crawls/month
2. Free tier typically includes:
   - 100-500 pages/month
   - 2-5 concurrent requests
   - Rate limits: Check dashboard

### Step 4: Set Environment Variable
```bash
# Option A: One-time
export FIRECRAWL_API_KEY='fc_api_1234567890...'

# Option B: Permanent
echo "export FIRECRAWL_API_KEY='fc_api_1234567890...'" >> ~/.zshrc
source ~/.zshrc

# Option C: Verify
echo $FIRECRAWL_API_KEY  # Should print your key
```

### Step 5: Verify
```bash
# Test the API key with curl
curl -X POST https://api.firecrawl.dev/v1/scrape \
  -H "Authorization: Bearer $FIRECRAWL_API_KEY" \
  -H "Content-Type: application/json" \
  -d '{"url": "https://example.com"}'
# Should return page content (or authentication error if key is wrong)
```

**✅ Firecrawl key is ready!**

---

## 3. Bluesky Direct Access (Optional)

### Step 1: Get Your Bluesky Password
- Already have a Bluesky account? Use your login password
- Don't have one? Sign up at **https://bsky.app**

### Step 2: Set Environment Variable
```bash
export BLUESKY_PASSWORD='your_bluesky_password'
```

### Step 3: Note
- If password not set, Phase 1 automatically falls back to Firecrawl profile scraping
- No additional setup needed to access Bluesky data

**✅ Optional - skip if you don't want to set it**

---

## 4. NATS/PulseMCP (Already Configured)

### Current Configuration
```
NATS Server: nats://nonlocal.info:4222
Subjects: ies.*, barton.*
Status: Ready to use (no setup needed)
```

### Optional: Custom NATS Server
If you have your own NATS server:
```bash
export NATS_URL='nats://your.server:4222'
```

**✅ Already configured - no setup needed**

---

## Verification Script

Test all tokens at once:

```bash
#!/bin/bash

echo "🔍 Verifying API Tokens..."

# Check GITHUB_TOKEN
if [ -z "$GITHUB_TOKEN" ]; then
  echo "❌ GITHUB_TOKEN not set"
else
  echo "✅ GITHUB_TOKEN is set"
fi

# Check FIRECRAWL_API_KEY
if [ -z "$FIRECRAWL_API_KEY" ]; then
  echo "❌ FIRECRAWL_API_KEY not set"
else
  echo "✅ FIRECRAWL_API_KEY is set"
fi

# Check BLUESKY_PASSWORD (optional)
if [ -z "$BLUESKY_PASSWORD" ]; then
  echo "⚠️  BLUESKY_PASSWORD not set (optional)"
else
  echo "✅ BLUESKY_PASSWORD is set"
fi

# Check NATS_URL
if [ -z "$NATS_URL" ]; then
  echo "ℹ️  NATS_URL not set (using default: nats://nonlocal.info:4222)"
else
  echo "✅ NATS_URL is set"
fi

echo ""
echo "Ready to execute Phase 1!"
```

Save as `verify_tokens.sh` and run:
```bash
chmod +x verify_tokens.sh
./verify_tokens.sh
```

---

## Clojure Verification

After setting environment variables, verify in Clojure:

```clojure
(require '[agents.phase-1-real-execution :as p1-real])

;; Detect available APIs
(p1-real/detect-available-apis)

;; Should show:
;; ✅ GitHub GraphQL API
;; ✅ Firecrawl Web Scraping
;; ✅ Bluesky Firehose (optional)
;; ✅ PulseMCP Real-time
;; 📊 APIs Ready: 3-4/4
```

---

## Troubleshooting

### "GitHub token invalid"
1. Regenerate at: https://github.com/settings/tokens
2. Ensure scopes include `repo`, `read:user`
3. Token hasn't expired?
4. Check: `curl -H "Authorization: Bearer $GITHUB_TOKEN" https://api.github.com/user`

### "Firecrawl key rejected"
1. Check key at: https://www.firecrawl.dev/dashboard
2. Ensure no extra spaces in key
3. Check rate limits/quota
4. Try regenerating key

### "Can't find GITHUB_TOKEN in environment"
```bash
# Verify it's set:
echo $GITHUB_TOKEN

# If empty, set it:
export GITHUB_TOKEN='your_token'

# Make it permanent (add to shell rc file):
echo "export GITHUB_TOKEN='your_token'" >> ~/.zshrc
source ~/.zshrc
```

### "Rate limit exceeded"
- GitHub: 5000 points/hour (typically enough)
- Firecrawl: Check your plan limits
- Solution: Implement exponential backoff (already in code)

---

## Security Best Practices

### Do's ✅
- ✅ Keep tokens in environment variables
- ✅ Set expiration dates on tokens
- ✅ Regenerate tokens periodically
- ✅ Use token scopes (don't over-permission)
- ✅ Never commit tokens to git

### Don'ts ❌
- ❌ Don't hardcode tokens in code
- ❌ Don't share tokens via Slack/email
- ❌ Don't commit .env files
- ❌ Don't use tokens longer than needed
- ❌ Don't give unnecessary permissions

### Secure Storage
```bash
# NEVER do this:
export GITHUB_TOKEN='token123'  # Visible in shell history

# BETTER: Use .env file (git-ignored)
echo "export GITHUB_TOKEN='token123'" > .env.local
# Add to .gitignore:
echo ".env.local" >> .gitignore

# BEST: Use environment variable manager
# - direnv (.envrc)
# - nix-shell
# - Docker secrets
```

---

## Execute Phase 1 with Tokens

Once tokens are set:

```clojure
;; 1. Verify tokens are available
(require '[agents.phase-1-real-execution :as p1-real])
(p1-real/detect-available-apis)

;; 2. Execute Phase 1 with real APIs
(p1-real/real-quick-start)

;; 3. Monitor progress
; Should see:
; ✅ Phase 1a (Schema): Creating tables...
; ✅ Phase 1b (Real APIs): Acquiring data...
; ✅ Phase 1c (Population): Loading to DuckDB...
; ✅ Phase 1d (Validation): Validating schema...

;; 4. Check results
(require '[agents.duckdb-schema :as db])
(db/validate-schema)
```

---

## Tokens Checklist

Before executing Phase 1:

- [ ] GitHub Personal Access Token created
  - [ ] Has `repo` scope
  - [ ] Has `read:user` scope
  - [ ] Set to environment variable `GITHUB_TOKEN`
  - [ ] Tested with curl/API

- [ ] Firecrawl API Key created
  - [ ] Free account set up
  - [ ] API key generated
  - [ ] Set to environment variable `FIRECRAWL_API_KEY`
  - [ ] Quota checked

- [ ] Optional: Bluesky password set
  - [ ] Have Bluesky account
  - [ ] Password saved to `BLUESKY_PASSWORD`

- [ ] NATS/PulseMCP verified
  - [ ] Default server accessible
  - [ ] Or custom `NATS_URL` set

- [ ] Verification complete
  - [ ] `(p1-real/detect-available-apis)` shows all APIs ready
  - [ ] Ready to execute Phase 1

---

## Quick Setup (5 minutes)

```bash
# 1. Get GitHub token
# → https://github.com/settings/tokens
# → Copy token

# 2. Get Firecrawl key
# → https://www.firecrawl.dev
# → Sign up, copy key

# 3. Set environment variables
export GITHUB_TOKEN='your_github_token'
export FIRECRAWL_API_KEY='your_firecrawl_key'

# 4. Verify
echo "GITHUB_TOKEN: $GITHUB_TOKEN"
echo "FIRECRAWL_API_KEY: $FIRECRAWL_API_KEY"

# 5. Execute Phase 1
clj -r "
(require '[agents.phase-1-real-execution :as p1-real])
(p1-real/real-quick-start)
"
```

---

## Summary

| Token | Status | Setup Time | Cost | Required |
|-------|--------|------------|------|----------|
| GitHub | Setup | 5 min | Free | Yes |
| Firecrawl | Setup | 10 min | Free | Yes |
| Bluesky | Optional | 0 min | Free | No |
| NATS | Ready | 0 min | Free | No |

---

**Next**: Set your tokens and run Phase 1!

```clojure
(require '[agents.phase-1-real-execution :as p1-real])
(p1-real/real-quick-start)
```

**Status**: Ready for production data acquisition
