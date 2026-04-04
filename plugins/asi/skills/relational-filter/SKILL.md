# Relational Filter

> "Is this something one expects someone who cares about them to do?"

**Version**: 1.0.0
**Trit**: -1 (Validator — checks actions against relational norms)
**Bundle**: verify
**Source**: Miller, R.S. *Intimate Relationships*, 9th ed. (McGraw-Hill, 2021)

## Overview

Relational Filter evaluates messages, actions, and behavioral patterns against 23 empirically-grounded relational norms distilled from relationship science. It takes an action + social context and returns a relational assessment: does this action align with how someone who genuinely cares would behave?

This is NOT a morality judge. It's a pattern matcher against decades of research on what sustains vs. destroys intimate bonds.

## When to Use This Skill

- Evaluating whether a message draft sounds caring or inadvertently harmful
- Checking if a request to/from someone reflects healthy relational dynamics
- Filtering communication through Beeper/messages before sending
- Assessing patterns in conversation history (e.g., "is this person stonewalling?")
- Self-check: "am I about to do something that erodes trust?"
- Analyzing conflict patterns between people in project context

## Database

```
/Users/alice/worlds/intimate_relationships.duckdb
```

### Tables

| Table | Rows | Purpose |
|-------|------|---------|
| `relational_norms` | 23 | Core filter rules with domain, norm, violation, severity |
| `satisfaction_suggestions` | 32 | Miller's applied advice per chapter |
| `chapters` | 14 | Full chapter text for deep lookup |

### Norm Domains (7)

| Domain | Core Norms | Key Principle |
|--------|-----------|---------------|
| **responsiveness** | 2 | Attend to bids; celebrate good news |
| **trust** | 2 | Be honest; follow through; deceiver's distrust |
| **respect** | 4 | No contempt (strongest divorce predictor); complain don't criticize; accept influence; balance power |
| **care** | 1 | Regular positive interaction satisfies need to belong |
| **commitment** | 2 | Think "us"; invest; derogate alternatives; accommodate |
| **repair** | 2 | Softened startup; 5:1 positive ratio; forgiveness |
| **boundary** | 2 | Distinguish reactive/suspicious jealousy; violence is never acceptable |

## How to Apply the Filter

### Step 1: Identify the action and context

```
ACTION: What is being done/said?
CONTEXT: What is the relationship? What history exists? What was the bid?
```

### Step 2: Query relevant norms

```sql
-- Find applicable norms for a given situation
SELECT domain, norm, violation, severity, valence
FROM relational_norms
WHERE severity = 'core'  -- start with core norms
ORDER BY domain;
```

For specific domains:
```sql
-- If the situation involves conflict
SELECT norm, violation FROM relational_norms 
WHERE domain IN ('respect', 'repair') AND severity = 'core';

-- If the situation involves trust/honesty
SELECT norm, violation FROM relational_norms
WHERE domain = 'trust';

-- If the situation involves someone being distant/unresponsive
SELECT norm, violation FROM relational_norms
WHERE domain IN ('responsiveness', 'care', 'commitment');
```

### Step 3: Assess alignment

For each relevant norm, evaluate:

| Score | Meaning |
|-------|---------|
| **+1** | Action *exemplifies* the norm |
| **0** | Neutral / insufficient information |
| **-1** | Action *violates* the norm |

### Step 4: Generate assessment

Report format:
```
RELATIONAL FILTER: [action summary]
Context: [relationship + history]

Norms checked:
  [+1] responsiveness: Attending to partner's bid ✓
  [-1] respect: Criticism of character, not behavior ✗
  [ 0] trust: Insufficient information

Assessment: [ALIGNED / MIXED / MISALIGNED]
Core violations: [list any severity='core' norms scored -1]
Note: [brief explanation grounded in Miller's research]
```

## Quick-Reference: The 15 Core Norms

These are the relationship-defining ones. Chronic violation of ANY predicts relationship failure.

### DO (things someone who cares does)
1. **Respond to bids** — when someone reaches out, turn toward them
2. **Celebrate wins** — enthusiastic response to partner's good news
3. **Be honest** — small lies erode trust disproportionately
4. **Follow through** — reliability IS caring
5. **Complain about behavior, not character** — "I feel X when Y" not "you always"
6. **Accept influence** — let your partner change your mind sometimes
7. **Think "us"** — cognitive interdependence, not scorekeeping
8. **Soft startup** — begin hard conversations gently
9. **5:1 ratio** — five positive interactions per negative one
10. **Satisfy the need to belong** — show up regularly with warmth

### DON'T (things that signal you don't care, even if you think you do)
11. **Never express contempt** — #1 predictor of relationship death
12. **Don't stonewall** — withdrawing from engagement is devastating
13. **Don't betray then minimize** — "it wasn't a big deal" IS the second betrayal
14. **Don't use power coercively** — unilateral control is abuse
15. **Never use violence** — no exceptions, no excuses

## Integration with Beeper MCP

When filtering messages before sending or evaluating received messages:

```python
# Pseudocode for message filter
def relational_check(message, relationship_context):
    """
    Run before sending a message or when evaluating received behavior.
    """
    norms = query_relevant_norms(message, relationship_context)
    
    scores = []
    for norm in norms:
        score = assess_alignment(message, norm)
        scores.append((norm.domain, score, norm))
    
    core_violations = [s for s in scores if s[1] == -1 and s[2].severity == 'core']
    
    if core_violations:
        return f"⚠️ PAUSE — core norm violation: {core_violations[0][2].norm}"
    
    avg = sum(s[1] for s in scores) / len(scores) if scores else 0
    if avg > 0.3:
        return "✓ aligned"
    elif avg > -0.3:
        return "~ mixed signals"
    else:
        return "✗ misaligned — reconsider"
```

## Integration with DuckDB-IES

The relational filter can be applied to interaction history:

```sql
-- Assess communication patterns over time
WITH message_norms AS (
    SELECT 
        m.timestamp,
        m.content,
        n.domain,
        n.norm,
        CASE 
            WHEN m.content ILIKE '%you always%' OR m.content ILIKE '%you never%' 
                THEN -1  -- criticism pattern
            WHEN m.content ILIKE '%I feel%' OR m.content ILIKE '%I need%'
                THEN 1   -- healthy complaint pattern
            ELSE 0
        END as alignment
    FROM messages m
    CROSS JOIN relational_norms n
    WHERE n.domain = 'respect'
)
SELECT 
    DATE_TRUNC('week', timestamp) as week,
    AVG(alignment) as avg_respect_alignment,
    COUNT(*) FILTER (WHERE alignment = -1) as violations
FROM message_norms
GROUP BY 1
ORDER BY 1;
```

## CatColab Connection

This skill maps to **ThSignedCategory** in the intimate-relationships-catcolab distillation:
- Each norm is a morphism with a sign (+1 do, -1 don't)
- Composition reveals cascades (one contempt → defensive → stonewall)
- The 5:1 ratio is the sign-balance threshold

## GF(3) Triads

```
relational-filter (-1) ⊗ beeper-poly (0) ⊗ artifacts-builder (+1) = 0 ✓
intent-sink (-1) ⊗ relational-filter (-1) ⊗ scientific-visualization (+1) = needs +1 partner
relational-filter (-1) ⊗ statistical-analysis (0) ⊗ duckdb-ies (+1) = 0 ✓
```

## Examples

### Example 1: Checking a message before sending

**Action:** "You said you'd handle the cables three days ago and nothing happened."
**Context:** barton, co-founder, physically manages GX10 hardware, often unresponsive

**Filter:**
- `respect`: This is a complaint about behavior (good), not character attack ✓
- `trust`: References broken commitment — legitimate concern ✓  
- `responsiveness`: Could add a bid — "can you update me on timing?" would be better
- `repair`: Startup is moderately hard — softening with "hey, checking in on..." would improve

**Assessment:** MIXED → suggest softened version: "Hey, checking in — any update on the cables? Let me know if something's blocking you."

### Example 2: Evaluating received behavior

**Action:** Partner hasn't responded to 3 messages over 2 days
**Context:** Usually responsive, no stated conflict

**Filter:**
- `responsiveness`: Failing to turn toward bids [-1 if pattern, 0 if one-off]
- `care`: Not satisfying need to belong through regular contact [-1]
- `boundary`: Could be reactive jealousy on your end if you're catastrophizing [check]

**Assessment:** Before escalating, check — are they overwhelmed? (invisible support norm). One message: "Hey, haven't heard from you — everything ok?" respects their autonomy while expressing care.

---

**Skill Name**: relational-filter  
**Type**: Message/Action Validator  
**Trit**: -1 (MINUS — VALIDATOR)  
**GF(3)**: Checks relational alignment before execution  
**Database**: /Users/alice/worlds/intimate_relationships.duckdb  
**Source**: Miller 9th ed., Gottman, Rusbult, Baumeister & Leary
