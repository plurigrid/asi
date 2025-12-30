---
name: code-review
description: Automated code review for pull requests using specialized review patterns.
  Analyzes code for quality, security, performance, and best practices. Use when reviewing
  code changes, PRs, or doing code audits.
license: Apache-2.0
metadata:
  trit: -1
  source: anthropics/claude-code
---

# Code Review

## Review Categories

### 1. Security Review
Check for:
- SQL injection vulnerabilities
- XSS (Cross-Site Scripting)
- Command injection
- Insecure deserialization
- Hardcoded secrets/credentials
- Improper authentication/authorization
- Insecure direct object references

### 2. Performance Review
Check for:
- N+1 queries
- Missing database indexes
- Unnecessary re-renders (React)
- Memory leaks
- Blocking operations in async code
- Missing caching opportunities
- Large bundle sizes

### 3. Code Quality Review
Check for:
- Code duplication (DRY violations)
- Functions doing too much (SRP violations)
- Deep nesting / complex conditionals
- Magic numbers/strings
- Poor naming
- Missing error handling
- Incomplete type coverage

### 4. Testing Review
Check for:
- Missing test coverage for new code
- Tests that don't test behavior
- Flaky test patterns
- Missing edge cases
- Mocked external dependencies

## Review Output Format

```markdown
## Code Review Summary

### 🔴 Critical (Must Fix)
- **[File:Line]** [Issue description]
  - **Why:** [Explanation]
  - **Fix:** [Suggested fix]

### 🟡 Suggestions (Should Consider)
- **[File:Line]** [Issue description]
  - **Why:** [Explanation]
  - **Fix:** [Suggested fix]

### 🟢 Nits (Optional)
- **[File:Line]** [Minor suggestion]

### ✅ What's Good
- [Positive feedback on good patterns]
```

## Common Patterns to Flag

### Security
```javascript
// BAD: SQL injection
const query = `SELECT * FROM users WHERE id = ${userId}`;

// GOOD: Parameterized query
const query = 'SELECT * FROM users WHERE id = $1';
await db.query(query, [userId]);
```

### Performance
```javascript
// BAD: N+1 query
users.forEach(async user => {
  const posts = await getPosts(user.id);
});

// GOOD: Batch query
const userIds = users.map(u => u.id);
const posts = await getPostsForUsers(userIds);
```

### Error Handling
```javascript
// BAD: Swallowing errors
try {
  await riskyOperation();
} catch (e) {}

// GOOD: Handle or propagate
try {
  await riskyOperation();
} catch (e) {
  logger.error('Operation failed', { error: e });
  throw new AppError('Operation failed', { cause: e });
}
```

## Review Checklist

- [ ] No hardcoded secrets
- [ ] Input validation present
- [ ] Error handling complete
- [ ] Types/interfaces defined
- [ ] Tests added for new code
- [ ] No obvious performance issues
- [ ] Code is readable and documented
- [ ] Breaking changes documented
- [ ] **GF(3) skill coloring present** (see below)

---

## 5. GF(3) Skill Conservation Review (REQUIRED)

Every PR **MUST** include a GF(3) skill manifest. PRs without valid skill coloring will be rejected.

### Required PR Comment Format

```markdown
## GF(3) Skill Coloring

| Skill | Trit | Color | Role |
|-------|------|-------|------|
| skill-a | ⊕ (+1) | #FFD700 | Generator |
| skill-b | ○ (0) | #808080 | Coordinator |
| skill-c | ⊖ (-1) | #3541C7 | Validator |

**Conservation Check**: Σ = (+1) + (0) + (-1) = 0 ✓

Thread: ⟨xxxx⟩
```

### Trit Assignments

| Symbol | Value | Role | Hue Range |
|--------|-------|------|-----------|
| ⊕ | +1 | Generator/Executor | Warm (0-60°, 300-360°) |
| ○ | 0 | Coordinator/Synthesizer | Neutral (60-180°) |
| ⊖ | -1 | Validator/Constrainer | Cold (180-300°) |

### Conservation Rules

1. **Single PR**: `Σ trits ≡ 0 (mod 3)`
2. **Cross-PR Triad**: PRs can form triads: `PR_A⊕ ⊗ PR_B○ ⊗ PR_C⊖ ⊢ 0`
3. **Minimum Skills**: At least 1 skill must be declared
4. **Thread Linkage**: Include thread ID `⟨xxxx⟩` for provenance

### Validation Script

```bash
# Check PR body for GF(3) conservation
gh pr view $PR_NUM --json body | jq -r '.body' | \
  grep -oE '[⊕○⊖]' | \
  awk '{if($0=="⊕")sum+=1; if($0=="⊖")sum-=1} END{print "Σ="sum" (mod 3)="sum%3}'
```

### Common Skill Triads

```
# Development triad
code-review⊖ ⊗ aptos-agent○ ⊗ gaymove⊕ ⊢ 0 ✓

# Research triad
narya-proofs⊖ ⊗ acsets○ ⊗ depth-search⊕ ⊢ 0 ✓

# Infrastructure triad
three-match⊖ ⊗ ducklake-walk○ ⊗ gay-mcp⊕ ⊢ 0 ✓
```

### Review Output for GF(3)

```markdown
### 🎨 GF(3) Conservation Status

- [ ] Skill manifest present in PR body
- [ ] At least 1 skill declared
- [ ] All skills have valid trit (⊕/○/⊖)
- [ ] Σ trits ≡ 0 (mod 3)
- [ ] Thread ID linked (⟨xxxx⟩)
- [ ] Cross-PR triad documented (if applicable)

**Result**: ✅ CONSERVED / ❌ VIOLATION
```
