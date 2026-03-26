---
name: deep-debug
description: >
  Multi-agent investigation for stubborn bugs.
  Triggers: going in circles debugging, complex bugs resisting normal debugging,
  symptoms don't match expectations, need parallel investigation,
  browser+API interaction bugs, deep investigation.
---

# Deep Debug - Multi-Agent Investigation

## When to Use

- Going in circles -- multiple fix attempts, nothing works
- Browser + API interaction bugs -- need to see Network tab, console logs
- Symptoms don't match expectations -- something deeper is wrong
- Complex state management bugs -- React hooks, closures, race conditions

## The Process

### Phase 1: Gather Evidence (Before Hypothesizing)

**For browser-related bugs**, use Chrome MCP tools:

```typescript
mcp__claude-in-chrome__read_network_requests  // duplicates, failures, timing
mcp__claude-in-chrome__read_console_messages  // errors, warnings, debug output
mcp__claude-in-chrome__read_page              // page state
```

**For backend bugs**, gather: error logs, stack traces, request/response payloads, database query logs, timing information.

### Phase 2: Launch Parallel Investigation (3 Agents)

#### Agent 1: Execution Tracer (debugger)
```
Task(subagent_type="debugger", prompt="""
EVIDENCE: [paste network/console evidence]

Trace the execution path that leads to this bug. Find:
1. Where the bug originates
2. What triggers it
3. The exact line/function causing the issue

Focus on TRACING, not guessing.
""")
```

#### Agent 2: Pattern Analyzer (code-reviewer)
```
Task(subagent_type="code-reviewer", prompt="""
EVIDENCE: [paste evidence]

Review the relevant code for common bug patterns:
- React useCallback/useMemo dependency issues
- Stale closures
- Race conditions
- State update ordering
- Missing error handling

Find patterns that EXPLAIN the evidence.
""")
```

#### Agent 3: Entry Point Mapper (Explore)
```
Task(subagent_type="Explore", prompt="""
EVIDENCE: [paste evidence]

Map all entry points that could trigger this behavior:
- All places [function] is called
- All event handlers involved
- All state updates that affect this

Find if something is being called MULTIPLE TIMES or from UNEXPECTED places.
""")
```

### Phase 3: Cross-Reference Findings

| Signal | Meaning |
|--------|---------|
| All 3 agree on root cause | High confidence -- fix it |
| 2 agree, 1 different | Investigate the difference |
| All 3 different | Need more evidence |

### Phase 4: Verify Fix

Re-gather the same evidence to confirm: network tab shows expected behavior, console has no errors, state updates correctly.

## Real Example: Duplicate API Calls Bug

**Evidence**: Network tab showed 2 fetch requests for the same message.

| Agent | Finding |
|-------|---------|
| debugger | `state.messages` in useCallback deps causes callback recreation |
| code-reviewer | Same finding + explained React pattern causing it |
| Explore | Verified UI layer wasn't double-calling (ruled out) |

**Root Cause**: `sendMessage` useCallback had `state.messages` in dependency array. Every state update recreated the callback, causing duplicate calls during re-renders.

**Fix**:
```typescript
const stateRef = useRef(state);
stateRef.current = state;

const sendMessage = useCallback(async (text) => {
  const messages = stateRef.current.messages;
  // ...
}, [/* state.messages removed */]);
```

## Common Bug Patterns

**React Hook Issues**: state in useCallback dependencies, missing dependencies causing stale closures, useEffect running multiple times.

**API/Network Issues**: duplicate requests, race conditions, CORS failures, timeout handling.

**State Management Issues**: updates not batching correctly, optimistic updates conflicting with server response, multiple sources of truth.
