# Substitution Detection Patterns

Complete regex patterns for detecting forbidden placeholder tokens.

## Python Detection Module

```python
import re
from typing import List, Tuple

SUBSTITUTION_PATTERNS = {
    # Prefix substitutions
    "pseudo": r'\bpseudo[-_]?\w*',
    "mock": r'\bmock[-_]?\w*',
    "fake": r'\bfake[-_]?\w*',
    "stub": r'\bstub[-_]?\w*',
    "dummy": r'\bdummy[-_]?\w*',

    # Completeness evasions
    "temporary": r'\btemporary\b',
    "placeholder": r'\bplaceholder\b',
    "todo": r'\bTODO\b',
    "fixme": r'\bFIXME\b',
    "tbd": r'\bTBD\b',
    "tba": r'\bTBA\b',
    "wip": r'\bWIP\b',

    # Deferral signals
    "later": r'\blater\b.*(?:add|implement|fix|do)',
    "eventually": r'\beventually\b',
    "for_now": r'\bfor\s+now\b',
    "quick_hack": r'\bquick\s+hack\b',
    "workaround": r'\bworkaround\b',
    "skeleton": r'\bskeleton\b',
    "boilerplate": r'\bboilerplate\b',

    # Example/demo evasions
    "example_prefix": r'\bexample[-_]\w+',
    "demo_prefix": r'\bdemo[-_]\w+',
    "sample_prefix": r'\bsample[-_]\w+',
    "test_prefix": r'\btest[-_]\w+(?!ing\b)',  # exclude "testing"

    # Metasyntactic variables in production context
    "metasyntactic": r'\b(foo|bar|baz|qux|quux|corge|grault)\b',

    # Placeholder markers
    "xxx_marker": r'\bx{3,}\b',
    "yyy_marker": r'\by{3,}\b',
    "zzz_marker": r'\bz{3,}\b',

    # Ellipsis evasions
    "ellipsis_code": r'\.{3,}(?!\s*$)',  # ... not at end of line
    "pass_only": r'^\s*pass\s*$',  # bare pass statement
}

def detect_substitutions(text: str) -> List[Tuple[str, str, int]]:
    """
    Detect substitution tokens in text.

    Returns:
        List of (pattern_name, matched_text, line_number) tuples
    """
    violations = []
    lines = text.split('\n')

    for line_num, line in enumerate(lines, 1):
        for pattern_name, pattern in SUBSTITUTION_PATTERNS.items():
            matches = re.finditer(pattern, line, re.IGNORECASE)
            for match in matches:
                violations.append((pattern_name, match.group(), line_num))

    return violations

def severity_level(pattern_name: str) -> str:
    """
    Classify violation severity.

    Returns: "critical" | "warning" | "info"
    """
    critical = {"todo", "fixme", "temporary", "placeholder", "pass_only"}
    warning = {"pseudo", "mock", "fake", "stub", "dummy", "skeleton"}

    if pattern_name in critical:
        return "critical"
    elif pattern_name in warning:
        return "warning"
    return "info"
```

## Contextual Exceptions

Some patterns are acceptable in specific contexts:

| Pattern | Acceptable When |
|---------|-----------------|
| `mock-*` | In test files (`*_test.py`, `test_*.py`) |
| `fake-*` | In test fixtures directory |
| `example_*` | In documentation/README files |
| `demo_*` | In demo/ directory explicitly labeled |
| `TODO` | In issue tracker references |

## Exception Detection

```python
def is_exception_context(filepath: str, pattern_name: str) -> bool:
    """Check if pattern is acceptable in this file context."""

    test_patterns = {"mock", "fake", "stub", "dummy"}
    doc_patterns = {"example_prefix", "demo_prefix", "sample_prefix"}

    # Test files can use mocking patterns
    if pattern_name in test_patterns:
        if re.search(r'(test_|_test\.py|/tests/|/test/)', filepath):
            return True

    # Documentation can use example patterns
    if pattern_name in doc_patterns:
        if re.search(r'(README|docs/|\.md$)', filepath):
            return True

    return False
```

## Shell One-Liner Detection

```bash
# Quick scan for substitution tokens
grep -rniE '(pseudo|mock|fake|stub|dummy|temporary|placeholder|TODO|FIXME|TBD|WIP|skeleton|xxx|yyy)' --include='*.py' --include='*.js' --include='*.ts' .
```

## Integration with GF(3)

When detection fires, emit MINUS (-1) signal:

```python
def emit_rejection(violations: List[Tuple[str, str, int]]) -> dict:
    return {
        "trit": -1,
        "action": "REJECT",
        "violations": violations,
        "next_step": "user_interview"
    }
```
