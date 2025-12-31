# Remediation Strategies

Fix strategies organized by token type.

## Critical Tokens

### TODO / FIXME

**Detection**: `\bTODO\b`, `\bFIXME\b`

**Remediation Options**:

1. **Implement Now**
   - Read surrounding context
   - Identify what's needed
   - Implement the missing functionality

2. **Convert to Tracked Issue**
   ```python
   # Before:
   # TODO: add rate limiting

   # After:
   # See: https://github.com/org/repo/issues/123
   def rate_limited_call():
       ...actual implementation...
   ```

3. **Remove if Obsolete**
   - Check git blame for age
   - Verify if already implemented elsewhere
   - Delete stale TODO

### placeholder

**Detection**: `\bplaceholder\b`

**Remediation**:
- Identify what actual value should be
- Query user/config for real value
- Replace entirely (no partial fix)

### xxx/yyy markers

**Detection**: `\bx{3,}\b`, `\by{3,}\b`

**Remediation**:
- These are always incomplete work
- Find surrounding context for intent
- Replace with actual implementation or delete

## Warning Tokens

### mock-* / fake-* / stub-* (outside tests)

**Detection**: `\bmock[-_]\w*`, `\bfake[-_]\w*`, `\bstub[-_]\w*`

**Remediation Options**:

1. **Move to Test File**
   ```python
   # If legitimate test helper, move to:
   # tests/conftest.py or tests/fixtures.py
   ```

2. **Replace with Real Implementation**
   ```python
   # Before:
   client = mock_http_client()

   # After:
   client = HTTPClient(config.api_url)
   ```

3. **Mark as Intentional** (if truly needed):
   ```python
   # SUBSTITUTE-OK: mock for local development without API access
   client = mock_http_client() if config.dev_mode else HTTPClient()
   ```

### skeleton / boilerplate

**Detection**: `\bskeleton\b`, `\bboilerplate\b`

**Remediation**:
- Flesh out the skeleton with actual logic
- Remove boilerplate comments after customization
- If template file, move to `/templates/` directory

## Info Tokens

### example_* / demo_* / sample_*

**Detection**: `\bexample[-_]\w+`, `\bdemo[-_]\w+`, `\bsample[-_]\w+`

**Remediation Options**:

1. **Keep if Intentional Documentation**
   - Ensure in `/docs/`, `/examples/`, or README
   - Verify examples are accurate and working

2. **Remove from Production Code**
   ```python
   # Before:
   API_KEY = "example_key_12345"

   # After:
   API_KEY = os.environ["API_KEY"]
   ```

3. **Rename to Production Values**
   ```python
   # Before:
   example_config = {...}

   # After:
   default_config = {...}
   ```

### Metasyntactic (foo/bar/baz)

**Detection**: `\b(foo|bar|baz|qux)\b`

**Remediation**:
- Replace with meaningful names
- `foo` → descriptive variable name
- `bar` → actual function name
- Exception: Algorithm explanations in comments

## Remediation Report Format

```markdown
## Remediation Plan: {filepath}

### Critical (Must Fix)

#### 1. Line 42: TODO
- **Token**: `TODO: implement auth`
- **Context**: `# TODO: implement auth before deploy`
- **Suggested Fix**: Implement OAuth2 flow using existing `auth_client`
- **Effort**: Medium
- **Related Files**: `src/auth/client.py`, `config/oauth.yaml`

### Warning (Should Review)

#### 2. Line 88: mock_client
- **Token**: `mock_client`
- **Context**: `client = mock_client()`
- **Suggested Fix**: Move to `tests/fixtures.py` or replace with real client
- **Effort**: Low
```

## Batch Remediation

For large-scale cleanup:

```bash
# Generate all tasks as GitHub issues
just substitute-tasks src/ --output=github --create

# Generate Linear tickets
just substitute-tasks src/ --output=linear --create

# Dry run (preview only)
just substitute-tasks src/ --dry-run
```

## Priority Matrix

| Token | In Production | In Tests | In Docs |
|-------|--------------|----------|---------|
| TODO/FIXME | CRITICAL | WARNING | INFO |
| placeholder | CRITICAL | WARNING | WARNING |
| mock-* | CRITICAL | OK | WARNING |
| example_* | CRITICAL | OK | OK |
| xxx/yyy | CRITICAL | CRITICAL | WARNING |
