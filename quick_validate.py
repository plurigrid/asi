#!/usr/bin/env python3
"""Quick validation script for SKILL.md files."""

import os
import re
import sys
from pathlib import Path

def validate_skill(skill_dir: Path) -> tuple[bool, str]:
    """Validate a single skill directory."""
    skill_md = skill_dir / "SKILL.md"
    
    if not skill_md.exists():
        return False, f"Missing SKILL.md"
    
    content = skill_md.read_text()
    
    # Check YAML frontmatter
    if not content.startswith("---"):
        return False, "Missing YAML frontmatter"
    
    # Find end of frontmatter
    end_match = content.find("---", 3)
    if end_match == -1:
        return False, "Unclosed YAML frontmatter"
    
    frontmatter = content[3:end_match]
    
    # Check required fields
    if "name:" not in frontmatter:
        return False, "Missing 'name' in frontmatter"
    if "description:" not in frontmatter:
        return False, "Missing 'description' in frontmatter"
    
    # Check for common YAML issues
    if '"""' in frontmatter:
        return False, "Invalid triple quotes in YAML"
    
    # Check for unbalanced quotes
    double_quotes = frontmatter.count('"')
    if double_quotes % 2 != 0:
        return False, "Unbalanced double quotes in frontmatter"
    
    return True, "OK"

def main():
    skills_dir = Path(__file__).parent / "skills"
    
    if not skills_dir.exists():
        print(f"Skills directory not found: {skills_dir}")
        sys.exit(1)
    
    results = {"pass": 0, "fail": 0}
    failures = []
    
    for skill_dir in sorted(skills_dir.iterdir()):
        if not skill_dir.is_dir():
            continue
        if skill_dir.name.startswith("."):
            continue
        
        ok, msg = validate_skill(skill_dir)
        if ok:
            results["pass"] += 1
            print(f"  ✓ {skill_dir.name}")
        else:
            results["fail"] += 1
            failures.append((skill_dir.name, msg))
            print(f"  ✗ {skill_dir.name}: {msg}")
    
    print()
    print(f"Passed: {results['pass']}, Failed: {results['fail']}")
    
    if failures:
        print("\nFailures:")
        for name, msg in failures:
            print(f"  - {name}: {msg}")
        sys.exit(1)
    
    sys.exit(0)

if __name__ == "__main__":
    main()
