#!/usr/bin/env python3
"""
Substitution token detector for accept-no-substitutes skill.

Usage:
    python detect.py <file_or_text>
    echo "some text" | python detect.py -
    python detect.py --scan <directory>
"""

import re
import sys
import json
from pathlib import Path
from typing import List, Dict, Tuple, Optional

SUBSTITUTION_PATTERNS = {
    # Prefix substitutions (CRITICAL)
    "pseudo": (r'\bpseudo[-_]?\w*', "critical"),
    "mock": (r'\bmock[-_]?\w*', "warning"),
    "fake": (r'\bfake[-_]?\w*', "warning"),
    "stub": (r'\bstub[-_]?\w*', "warning"),
    "dummy": (r'\bdummy[-_]?\w*', "warning"),

    # Completeness evasions (CRITICAL)
    "temporary": (r'\btemporary\b', "critical"),
    "placeholder": (r'\bplaceholder\b', "critical"),
    "todo": (r'\bTODO\b', "critical"),
    "fixme": (r'\bFIXME\b', "critical"),
    "tbd": (r'\bTBD\b', "critical"),
    "tba": (r'\bTBA\b', "warning"),
    "wip": (r'\bWIP\b', "warning"),

    # Deferral signals (WARNING)
    "later": (r'\blater\b', "warning"),
    "eventually": (r'\beventually\b', "warning"),
    "for_now": (r'\bfor\s+now\b', "warning"),
    "skeleton": (r'\bskeleton\b', "warning"),
    "boilerplate": (r'\bboilerplate\b', "info"),

    # Example/demo evasions (WARNING)
    "example_prefix": (r'\bexample[-_]\w+', "warning"),
    "demo_prefix": (r'\bdemo[-_]\w+', "warning"),
    "sample_prefix": (r'\bsample[-_]\w+', "info"),

    # Metasyntactic (INFO unless in production code)
    "metasyntactic": (r'\b(foo|bar|baz|qux)\b', "info"),

    # Placeholder markers (CRITICAL)
    "xxx_marker": (r'\bx{3,}\b', "critical"),
    "yyy_marker": (r'\by{3,}\b', "critical"),
}

# Files where certain patterns are acceptable
EXCEPTION_RULES = {
    "mock": [r'test_', r'_test\.py', r'/tests/', r'\.test\.'],
    "fake": [r'test_', r'_test\.py', r'/tests/', r'\.test\.'],
    "stub": [r'test_', r'_test\.py', r'/tests/', r'\.test\.'],
    "example_prefix": [r'README', r'\.md$', r'/docs/'],
    "demo_prefix": [r'/demo/', r'README', r'\.md$'],
}


def is_exception(pattern_name: str, filepath: str) -> bool:
    """Check if pattern is acceptable in this file context."""
    if pattern_name not in EXCEPTION_RULES:
        return False

    for exception_pattern in EXCEPTION_RULES[pattern_name]:
        if re.search(exception_pattern, filepath, re.IGNORECASE):
            return True
    return False


def detect(text: str, filepath: Optional[str] = None) -> List[Dict]:
    """
    Detect substitution tokens in text.

    Returns list of violation dicts with:
        - pattern: name of pattern matched
        - match: the matched text
        - line: line number (1-indexed)
        - severity: critical|warning|info
        - context: surrounding text
    """
    violations = []
    lines = text.split('\n')

    for line_num, line in enumerate(lines, 1):
        for pattern_name, (pattern, severity) in SUBSTITUTION_PATTERNS.items():
            # Skip if exception applies
            if filepath and is_exception(pattern_name, filepath):
                continue

            for match in re.finditer(pattern, line, re.IGNORECASE):
                violations.append({
                    "pattern": pattern_name,
                    "match": match.group(),
                    "line": line_num,
                    "severity": severity,
                    "context": line.strip()[:80],
                })

    return violations


def scan_directory(path: Path, extensions: List[str] = None) -> Dict[str, List[Dict]]:
    """Scan directory for substitution tokens."""
    if extensions is None:
        extensions = ['.py', '.js', '.ts', '.jsx', '.tsx', '.go', '.rs', '.java']

    results = {}

    for file_path in path.rglob('*'):
        if not file_path.is_file():
            continue
        if file_path.suffix not in extensions:
            continue
        # Skip common non-source directories
        if any(part.startswith('.') or part in ('node_modules', 'venv', '__pycache__')
               for part in file_path.parts):
            continue

        try:
            text = file_path.read_text(encoding='utf-8')
            violations = detect(text, str(file_path))
            if violations:
                results[str(file_path)] = violations
        except (UnicodeDecodeError, PermissionError):
            continue

    return results


def format_output(violations: List[Dict], filepath: str = "<stdin>") -> str:
    """Format violations for display."""
    if not violations:
        return f"✓ {filepath}: No substitutions detected"

    critical = [v for v in violations if v['severity'] == 'critical']
    warnings = [v for v in violations if v['severity'] == 'warning']

    lines = [f"✗ {filepath}: {len(violations)} substitution(s) detected"]

    if critical:
        lines.append(f"  CRITICAL ({len(critical)}):")
        for v in critical:
            lines.append(f"    L{v['line']}: {v['match']} ({v['pattern']})")

    if warnings:
        lines.append(f"  WARNING ({len(warnings)}):")
        for v in warnings:
            lines.append(f"    L{v['line']}: {v['match']} ({v['pattern']})")

    return '\n'.join(lines)


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)

    if sys.argv[1] == '--scan':
        # Directory scan mode
        path = Path(sys.argv[2]) if len(sys.argv) > 2 else Path('.')
        results = scan_directory(path)

        if not results:
            print("✓ No substitutions detected")
            sys.exit(0)

        total = sum(len(v) for v in results.values())
        print(f"Found {total} substitution(s) in {len(results)} file(s):\n")

        for filepath, violations in sorted(results.items()):
            print(format_output(violations, filepath))
            print()

        sys.exit(1)  # Non-zero exit for CI

    elif sys.argv[1] == '-':
        # Stdin mode
        text = sys.stdin.read()
        violations = detect(text)
        print(format_output(violations))
        sys.exit(1 if violations else 0)

    elif sys.argv[1] == '--json':
        # JSON output mode
        text = sys.stdin.read() if len(sys.argv) == 2 else Path(sys.argv[2]).read_text()
        violations = detect(text, sys.argv[2] if len(sys.argv) > 2 else None)
        print(json.dumps(violations, indent=2))
        sys.exit(1 if violations else 0)

    else:
        # File mode
        filepath = sys.argv[1]
        text = Path(filepath).read_text()
        violations = detect(text, filepath)
        print(format_output(violations, filepath))
        sys.exit(1 if violations else 0)


if __name__ == '__main__':
    main()
