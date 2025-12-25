#!/usr/bin/env python3
"""
Skill Validation for GF(3) Conservation

XIP Color: #4857D5
Role: SLAVE (-1)
Gay.jl Index: 8
"""

import os
import re
import json
from pathlib import Path
from dataclasses import dataclass
from typing import Optional

@dataclass
class SkillValidation:
    name: str
    valid: bool
    role: Optional[str] = None
    trit: Optional[int] = None
    color: Optional[str] = None
    error: Optional[str] = None

def validate_skill(skill_path: Path) -> SkillValidation:
    """Validate a single skill directory."""
    skill_md = skill_path / "SKILL.md"
    
    if not skill_md.exists():
        return SkillValidation(
            name=skill_path.name,
            valid=False,
            error="Missing SKILL.md"
        )
    
    try:
        content = skill_md.read_text()
    except Exception as e:
        return SkillValidation(
            name=skill_path.name,
            valid=False,
            error=f"Read error: {e}"
        )
    
    # Extract role
    role_patterns = [
        r'\*\*Role\*\*\s*\|\s*`?(GAY|MASTER|SLAVE)',
        r'Role:\s*(GAY|MASTER|SLAVE)',
        r'role["\']?\s*:\s*["\']?(GAY|MASTER|SLAVE)',
    ]
    
    role = None
    for pattern in role_patterns:
        match = re.search(pattern, content, re.IGNORECASE)
        if match:
            role = match.group(1).upper()
            break
    
    # Infer role from trit if not explicit
    trit_match = re.search(r'[Tt]rit["\']?\s*[:=]\s*([+-]?1|0)', content)
    if trit_match and not role:
        trit_val = int(trit_match.group(1))
        role = {1: "GAY", 0: "MASTER", -1: "SLAVE"}.get(trit_val)
    
    trit = {"GAY": 1, "MASTER": 0, "SLAVE": -1}.get(role) if role else None
    
    # Extract color
    color_match = re.search(r'#([0-9A-Fa-f]{6})', content)
    color = f"#{color_match.group(1).upper()}" if color_match else None
    
    return SkillValidation(
        name=skill_path.name,
        valid=True,
        role=role,
        trit=trit,
        color=color
    )

def check_gf3_conservation(skills: list[SkillValidation]) -> list[dict]:
    """Check GF(3) conservation: every triad must sum to 0 (mod 3)."""
    violations = []
    
    # Filter to skills with trit assignments
    with_trits = [s for s in skills if s.trit is not None]
    
    # Check overall conservation
    total = sum(s.trit for s in with_trits)
    if total % 3 != 0:
        violations.append({
            "type": "global",
            "sum": total,
            "mod3": total % 3,
            "message": f"Global trit sum {total} ≢ 0 (mod 3)"
        })
    
    # Group into triads and check each
    for i in range(0, len(with_trits) - 2, 3):
        triad = with_trits[i:i+3]
        triad_sum = sum(s.trit for s in triad)
        
        if triad_sum % 3 != 0:
            violations.append({
                "type": "triad",
                "skills": [s.name for s in triad],
                "trits": [s.trit for s in triad],
                "sum": triad_sum,
                "message": f"Triad {[s.name for s in triad]} sums to {triad_sum}"
            })
    
    return violations

def main():
    import argparse
    
    parser = argparse.ArgumentParser(description="Validate skills for GF(3) conservation")
    parser.add_argument("--skills-dir", default="skills", help="Path to skills directory")
    parser.add_argument("--json", action="store_true", help="Output as JSON")
    args = parser.parse_args()
    
    skills_dir = Path(args.skills_dir)
    
    if not skills_dir.exists():
        print(f"Error: Skills directory '{skills_dir}' not found")
        return 1
    
    # Validate all skills
    results = []
    for skill_path in sorted(skills_dir.iterdir()):
        if skill_path.is_dir() and not skill_path.name.startswith('.'):
            result = validate_skill(skill_path)
            results.append(result)
    
    # Check GF(3)
    violations = check_gf3_conservation(results)
    
    if args.json:
        output = {
            "skills": [vars(r) for r in results],
            "violations": violations,
            "summary": {
                "total": len(results),
                "valid": sum(1 for r in results if r.valid),
                "with_role": sum(1 for r in results if r.role),
                "gf3_conserved": len(violations) == 0
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("=" * 60)
        print("SKILL VALIDATION - GF(3) Conservation Check")
        print("=" * 60)
        print()
        
        # Summary by role
        role_counts = {"GAY": 0, "MASTER": 0, "SLAVE": 0, None: 0}
        for r in results:
            role_counts[r.role] = role_counts.get(r.role, 0) + 1
        
        print(f"Skills found: {len(results)}")
        print(f"  GAY (+1):    {role_counts['GAY']}")
        print(f"  MASTER (0):  {role_counts['MASTER']}")
        print(f"  SLAVE (-1):  {role_counts['SLAVE']}")
        print(f"  Unassigned:  {role_counts[None]}")
        print()
        
        # List skills
        for r in results:
            status = "✓" if r.valid else "✗"
            role_str = f"{r.role or 'N/A':6} ({r.trit if r.trit is not None else '?':>2})"
            color_str = r.color or "N/A"
            print(f"  {status} {r.name:40} {role_str} {color_str}")
        
        print()
        
        # GF(3) status
        if violations:
            print(f"⚠️  GF(3) VIOLATIONS: {len(violations)}")
            for v in violations:
                print(f"  - {v['message']}")
            return 1
        else:
            total_trit = sum(r.trit for r in results if r.trit is not None)
            print(f"✓ GF(3) CONSERVED: Total trit sum = {total_trit} ≡ 0 (mod 3)")
            return 0

if __name__ == "__main__":
    exit(main())
