#!/usr/bin/env python3
"""
SKILL.md CI Validator - MINUS (-1) agent contribution
Seed: 0x42D | Trit: -1 (verification/constraint)

Validates SKILL.md files for:
- Required YAML frontmatter (name, description)
- Valid YAML syntax
- No broken internal links
- Proper markdown structure
"""

import os
import re
import sys
import yaml
from pathlib import Path
from dataclasses import dataclass
from typing import Optional

# GF(3) trit constants for validation states
TRIT_PASS = 1    # +1: constraint satisfied
TRIT_WARN = 0    #  0: neutral/unknown
TRIT_FAIL = -1   # -1: constraint violated

@dataclass
class ValidationResult:
    skill_path: str
    trit: int
    errors: list[str]
    warnings: list[str]
    
    @property
    def passed(self) -> bool:
        return self.trit != TRIT_FAIL

def extract_frontmatter(content: str) -> tuple[Optional[dict], str]:
    """Extract YAML frontmatter from markdown content."""
    pattern = r'^---\s*\n(.*?)\n---\s*\n(.*)$'
    match = re.match(pattern, content, re.DOTALL)
    if not match:
        return None, content
    try:
        frontmatter = yaml.safe_load(match.group(1))
        body = match.group(2)
        return frontmatter, body
    except yaml.YAMLError as e:
        return {'_yaml_error': str(e)}, content

def find_internal_links(content: str) -> list[str]:
    """Find all relative markdown links."""
    pattern = r'\[([^\]]+)\]\(([^)]+)\)'
    links = []
    for match in re.finditer(pattern, content):
        link = match.group(2)
        if not link.startswith(('http://', 'https://', 'mailto:', '#')):
            links.append(link)
    return links

def validate_skill(skill_dir: Path) -> ValidationResult:
    """Validate a single SKILL.md file."""
    skill_md = skill_dir / "SKILL.md"
    errors = []
    warnings = []
    
    if not skill_md.exists():
        return ValidationResult(
            skill_path=str(skill_dir),
            trit=TRIT_FAIL,
            errors=["SKILL.md not found"],
            warnings=[]
        )
    
    try:
        content = skill_md.read_text(encoding='utf-8')
    except Exception as e:
        return ValidationResult(
            skill_path=str(skill_dir),
            trit=TRIT_FAIL,
            errors=[f"Cannot read file: {e}"],
            warnings=[]
        )
    
    # Check frontmatter
    frontmatter, body = extract_frontmatter(content)
    
    if frontmatter is None:
        errors.append("Missing YAML frontmatter (must start with ---)")
    elif '_yaml_error' in frontmatter:
        errors.append(f"Invalid YAML syntax: {frontmatter['_yaml_error']}")
    else:
        # Check required fields
        if 'name' not in frontmatter:
            errors.append("Missing required field: 'name'")
        elif not isinstance(frontmatter['name'], str):
            errors.append("Field 'name' must be a string")
            
        if 'description' not in frontmatter:
            errors.append("Missing required field: 'description'")
        elif not isinstance(frontmatter['description'], str):
            errors.append("Field 'description' must be a string")
        elif len(frontmatter['description']) < 10:
            warnings.append("Description is very short (< 10 chars)")
    
    # Check internal links
    links = find_internal_links(content)
    for link in links:
        link_path = skill_dir / link
        if not link_path.exists():
            errors.append(f"Broken link: {link}")
    
    # Check markdown structure
    if body:
        # Should have at least one heading
        if not re.search(r'^#+ ', body, re.MULTILINE):
            warnings.append("No markdown headings found")
        
        # Check for empty content
        if len(body.strip()) < 50:
            warnings.append("Content is very short (< 50 chars after frontmatter)")
    
    # Line count warning (progressive disclosure)
    line_count = len(content.splitlines())
    if line_count > 500:
        warnings.append(f"SKILL.md exceeds 500 lines ({line_count} lines) - consider progressive disclosure")
    
    # Compute trit
    if errors:
        trit = TRIT_FAIL
    elif warnings:
        trit = TRIT_WARN
    else:
        trit = TRIT_PASS
    
    return ValidationResult(
        skill_path=str(skill_dir),
        trit=trit,
        errors=errors,
        warnings=warnings
    )

def validate_skills_directory(skills_dir: Path) -> list[ValidationResult]:
    """Validate all skills in a directory."""
    results = []
    
    if not skills_dir.exists():
        print(f"Error: Directory not found: {skills_dir}", file=sys.stderr)
        sys.exit(1)
    
    for item in sorted(skills_dir.iterdir()):
        if item.is_dir() and not item.name.startswith('.'):
            result = validate_skill(item)
            results.append(result)
    
    return results

def print_results(results: list[ValidationResult], verbose: bool = False) -> int:
    """Print validation results with GF(3) annotations."""
    trit_symbols = {TRIT_PASS: '⊕', TRIT_WARN: '○', TRIT_FAIL: '⊖'}
    trit_names = {TRIT_PASS: '+1', TRIT_WARN: ' 0', TRIT_FAIL: '-1'}
    
    total_trit = 0
    failed = 0
    
    print("=" * 60)
    print("SKILL.md Validation Report | Agent: MINUS (-1)")
    print("=" * 60)
    
    for result in results:
        skill_name = Path(result.skill_path).name
        sym = trit_symbols[result.trit]
        trit_str = trit_names[result.trit]
        
        if result.trit == TRIT_FAIL or verbose:
            print(f"\n{sym} [{trit_str}] {skill_name}")
            
            for error in result.errors:
                print(f"  ✗ ERROR: {error}")
            for warning in result.warnings:
                print(f"  ⚠ WARN:  {warning}")
        
        total_trit = (total_trit + result.trit) % 3  # GF(3) sum
        if result.trit == TRIT_FAIL:
            failed += 1
    
    print("\n" + "=" * 60)
    print(f"Summary: {len(results)} skills validated")
    print(f"  Passed (⊕): {sum(1 for r in results if r.trit == TRIT_PASS)}")
    print(f"  Warnings (○): {sum(1 for r in results if r.trit == TRIT_WARN)}")
    print(f"  Failed (⊖): {failed}")
    print(f"  GF(3) sum: {total_trit}")
    print("=" * 60)
    
    return failed

def main():
    import argparse
    parser = argparse.ArgumentParser(
        description="Validate SKILL.md files with GF(3) trit annotations"
    )
    parser.add_argument(
        "skills_dir",
        type=Path,
        nargs="?",
        default=Path(__file__).parent.parent / "skills",
        help="Path to skills directory"
    )
    parser.add_argument(
        "-v", "--verbose",
        action="store_true",
        help="Show all results, not just failures"
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output as JSON"
    )
    
    args = parser.parse_args()
    
    results = validate_skills_directory(args.skills_dir)
    
    if args.json:
        import json
        output = [
            {
                "skill": Path(r.skill_path).name,
                "trit": r.trit,
                "errors": r.errors,
                "warnings": r.warnings
            }
            for r in results
        ]
        print(json.dumps(output, indent=2))
        failed = sum(1 for r in results if r.trit == TRIT_FAIL)
    else:
        failed = print_results(results, args.verbose)
    
    sys.exit(1 if failed > 0 else 0)

if __name__ == "__main__":
    main()
