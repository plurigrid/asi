# User Interview Templates

Question templates for different substitution categories.

## Generic Interview Structure

```
[SUBSTITUTION DETECTED]
Token: {token}
Location: {context}
Category: {category}

This indicates uncertainty that requires your input:

1. {primary_question}
2. {detail_question}
3. {research_question}
```

## Category-Specific Templates

### Authentication/Security Substitutions

**Triggers**: `fake-auth`, `mock-credentials`, `dummy-token`

```
Authentication placeholder detected: "{token}"

Clarification needed:
1. Which authentication provider are you using? (OAuth, JWT, API key, etc.)
2. What is the token format and validation requirements?
3. Should I research the provider's documentation first?
```

### Data Substitutions

**Triggers**: `mock-data`, `fake-response`, `dummy-payload`

```
Data placeholder detected: "{token}"

Clarification needed:
1. What is the actual data schema/structure?
2. Where should the real data come from? (API, database, file)
3. Are there sample data files I should reference?
```

### Implementation Substitutions

**Triggers**: `pseudo-code`, `skeleton`, `TODO: implement`

```
Implementation placeholder detected: "{token}"

Clarification needed:
1. What specific functionality is needed here?
2. Are there existing patterns in this codebase to follow?
3. What are the edge cases and error conditions?
```

### Configuration Substitutions

**Triggers**: `example_config`, `demo_settings`, `placeholder_value`

```
Configuration placeholder detected: "{token}"

Clarification needed:
1. What are the actual configuration values?
2. Should these come from environment variables?
3. Is there a secrets management system in use?
```

### API Substitutions

**Triggers**: `mock-endpoint`, `fake-api`, `stub-service`

```
API placeholder detected: "{token}"

Clarification needed:
1. What is the actual API endpoint/service?
2. What authentication does it require?
3. Should I fetch the API documentation first?
```

## Deferral Signal Templates

### "Later" Signals

**Triggers**: `add this later`, `implement eventually`, `for now`

```
Deferral language detected: "{token}"

This signals incomplete work. Options:
1. Implement it now - what are the requirements?
2. Create a tracked issue - what details should be captured?
3. Clarify scope - is this actually out of scope?
```

### "Quick Hack" Signals

**Triggers**: `quick hack`, `workaround`, `temporary fix`

```
Workaround language detected: "{token}"

Workarounds accumulate technical debt. Options:
1. Implement the proper solution - what should it look like?
2. Document the limitation - what constraints prevent proper solution?
3. Accept explicitly - with what timeline for proper fix?
```

## Interview Response Handling

After user responds:

| Response Type | Action |
|---------------|--------|
| Provides details | Proceed with implementation using provided info |
| Requests research | Use web search/documentation tools, then re-ask |
| Defers decision | Create explicit TODO with tracking number |
| Marks out of scope | Remove the placeholder entirely |

## Example Dialogue

**Agent output** (would be rejected):
```python
def get_user_data(user_id):
    # TODO: implement database query
    return {"id": user_id, "name": "placeholder"}
```

**Interview**:
```
Implementation placeholder detected: "TODO: implement database query"
Data placeholder detected: "placeholder"

Clarification needed:
1. What database system is being used? (PostgreSQL, MongoDB, etc.)
2. What is the user data schema?
3. Should I examine existing database queries in this codebase?
```

**User response**: "PostgreSQL, check src/db/models.py for the User model"

**Agent proceeds** with actual implementation using provided context.
