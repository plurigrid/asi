#!/usr/bin/env python3
"""
Substitute Eraser - Scan existing codebase for placeholder tokens.

Usage:
    python scan.py <path>              # Scan directory or file
    python scan.py <path> --critical   # Critical only (CI mode)
    python scan.py <path> --json       # JSON output
    python scan.py <path> --fix        # Interactive fix mode
"""

import re
import sys
import json
from pathlib import Path
from typing import List, Dict, Optional
from dataclasses import dataclass, asdict

@dataclass
class Violation:
    file: str
    line: int
    column: int
    token: str
    pattern: str
    severity: str
    context: str
    suggestion: str = ""

PATTERNS = {
    # Critical
    "todo": (r'\bTODO\b', "critical", "Implement or convert to tracked issue"),
    "fixme": (r'\bFIXME\b', "critical", "Fix the issue or document why deferred"),
    "placeholder": (r'\bplaceholder\b', "critical", "Replace with actual value"),
    "xxx": (r'\bx{3,}\b', "critical", "Complete the implementation"),
    "yyy": (r'\by{3,}\b', "critical", "Complete the implementation"),
    "temporary": (r'\btemporary\b', "critical", "Make permanent or remove"),
    "pseudo": (r'\bpseudo[-_]\w*', "critical", "Implement real version"),

    # Warning
    "mock": (r'\bmock[-_]\w*', "warning", "Move to tests or replace with real"),
    "fake": (r'\bfake[-_]\w*', "warning", "Move to tests or replace with real"),
    "stub": (r'\bstub[-_]\w*', "warning", "Implement full version"),
    "dummy": (r'\bdummy[-_]\w*', "warning", "Replace with meaningful value"),
    "skeleton": (r'\bskeleton\b', "warning", "Flesh out implementation"),
    "tbd": (r'\bTBD\b', "warning", "Determine and document"),
    "wip": (r'\bWIP\b', "warning", "Complete or remove"),

    # Info
    "example": (r'\bexample[-_]\w+', "info", "Verify intentional or rename"),
    "demo": (r'\bdemo[-_]\w+', "info", "Move to demo/ or remove"),
    "sample": (r'\bsample[-_]\w+', "info", "Verify intentional or rename"),
    "foo": (r'\b(foo|bar|baz|qux)\b', "info", "Use meaningful names"),
}

# Context-based exceptions
EXCEPTION_RULES = {
    "mock": [r'_test\.py$', r'^test_', r'/tests/', r'conftest\.py$'],
    "fake": [r'_test\.py$', r'^test_', r'/tests/', r'conftest\.py$'],
    "stub": [r'_test\.py$', r'^test_', r'/tests/', r'conftest\.py$'],
    "example": [r'README', r'/docs/', r'/examples/', r'\.md$'],
    "demo": [r'/demo/', r'README', r'/docs/', r'\.md$'],
    "sample": [r'/docs/', r'/examples/', r'\.md$'],
}

SKIP_DIRS = {'.git', 'node_modules', 'venv', '.venv', '__pycache__',
             '.mypy_cache', '.pytest_cache', 'dist', 'build', '.tox'}

EXTENSIONS = {'.py', '.js', '.ts', '.jsx', '.tsx', '.go', '.rs', '.java',
              '.rb', '.php', '.c', '.cpp', '.h', '.hpp', '.cs', '.swift',
              '.kt', '.scala', '.sh', '.bash', '.zsh', '.yaml', '.yml',
              '.json', '.toml', '.ini', '.cfg', '.md', '.txt'}


def is_exception(pattern_name: str, filepath: str) -> bool:
    """Check if pattern is acceptable in this file context."""
    if pattern_name not in EXCEPTION_RULES:
        return False
    for rule in EXCEPTION_RULES[pattern_name]:
        if re.search(rule, filepath, re.IGNORECASE):
            return True
    return False


def has_exception_marker(line: str) -> bool:
    """Check for SUBSTITUTE-OK marker."""
    return 'SUBSTITUTE-OK' in line or 'substitute-ok' in line


def scan_file(filepath: Path) -> List[Violation]:
    """Scan a single file for violations."""
    violations = []

    try:
        content = filepath.read_text(encoding='utf-8')
    except (UnicodeDecodeError, PermissionError):
        return violations

    lines = content.split('\n')
    str_path = str(filepath)

    for line_num, line in enumerate(lines, 1):
        # Skip lines with exception marker
        if has_exception_marker(line):
            continue

        for pattern_name, (regex, severity, suggestion) in PATTERNS.items():
            # Skip if context exception applies
            if is_exception(pattern_name, str_path):
                continue

            for match in re.finditer(regex, line, re.IGNORECASE):
                violations.append(Violation(
                    file=str_path,
                    line=line_num,
                    column=match.start() + 1,
                    token=match.group(),
                    pattern=pattern_name,
                    severity=severity,
                    context=line.strip()[:100],
                    suggestion=suggestion,
                ))

    return violations


def scan_directory(path: Path) -> List[Violation]:
    """Recursively scan directory for violations."""
    violations = []

    for item in path.rglob('*'):
        # Skip directories
        if item.is_dir():
            continue
        # Skip excluded directories
        if any(skip in item.parts for skip in SKIP_DIRS):
            continue
        # Only scan known extensions
        if item.suffix.lower() not in EXTENSIONS:
            continue

        violations.extend(scan_file(item))

    return violations


def format_report(violations: List[Violation], path: str) -> str:
    """Format violations as human-readable report."""
    if not violations:
        return f"✓ No substitutions found in {path}"

    critical = [v for v in violations if v.severity == 'critical']
    warning = [v for v in violations if v.severity == 'warning']
    info = [v for v in violations if v.severity == 'info']

    lines = [
        "SUBSTITUTE ERASER REPORT",
        "=" * 50,
        f"Scanned: {path}",
        f"Found: {len(violations)} substitution(s)",
        "",
    ]

    if critical:
        lines.append(f"CRITICAL ({len(critical)}):")
        for v in critical:
            lines.append(f"  {v.file}:{v.line}:{v.column}")
            lines.append(f"    Token: {v.token}")
            lines.append(f"    Context: {v.context}")
            lines.append(f"    Fix: {v.suggestion}")
            lines.append("")

    if warning:
        lines.append(f"WARNING ({len(warning)}):")
        for v in warning:
            lines.append(f"  {v.file}:{v.line} - {v.token} ({v.pattern})")
        lines.append("")

    if info:
        lines.append(f"INFO ({len(info)}):")
        for v in info[:10]:  # Limit info output
            lines.append(f"  {v.file}:{v.line} - {v.token}")
        if len(info) > 10:
            lines.append(f"  ... and {len(info) - 10} more")
        lines.append("")

    # Summary
    lines.append("-" * 50)
    if critical:
        lines.append(f"✗ BLOCKED: {len(critical)} critical issue(s) require remediation")
    elif warning:
        lines.append(f"⚠ WARNING: {len(warning)} issue(s) should be reviewed")
    else:
        lines.append(f"ℹ INFO: {len(info)} minor issue(s) detected")

    return '\n'.join(lines)


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)

    path = Path(sys.argv[1])
    critical_only = '--critical' in sys.argv
    json_output = '--json' in sys.argv

    if not path.exists():
        print(f"Path not found: {path}")
        sys.exit(1)

    # Scan
    if path.is_file():
        violations = scan_file(path)
    else:
        violations = scan_directory(path)

    # Filter if critical only
    if critical_only:
        violations = [v for v in violations if v.severity == 'critical']

    # Output
    if json_output:
        print(json.dumps([asdict(v) for v in violations], indent=2))
    else:
        print(format_report(violations, str(path)))

    # Exit code
    critical_count = len([v for v in violations if v.severity == 'critical'])
    sys.exit(1 if critical_count > 0 else 0)


if __name__ == '__main__':
    main()
