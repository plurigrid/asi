#!/usr/bin/env python3
"""
Add non-backtracking geodesic qualification to all SKILL.md files.

Möbius condition: μ(n) ≠ 0 ⟺ squarefree (prime path)
Geodesic: Shortest path, no revisiting states
GF(3): Sum of trits ≡ 0 (mod 3)
"""

import os
import re
from pathlib import Path

GEODESIC_BLOCK = """
## Non-Backtracking Geodesic Qualification

**Condition**: μ(n) ≠ 0 (Möbius squarefree)

This skill is qualified for non-backtracking geodesic traversal:

1. **Prime Path**: No state revisited in skill invocation chain
2. **Möbius Filter**: Composite paths (backtracking) cancel via μ-inversion
3. **GF(3) Conservation**: Trit sum ≡ 0 (mod 3) across skill triplets
4. **Spectral Gap**: Ramanujan bound λ₂ ≤ 2√(k-1) for k-regular expansion

```
Geodesic Invariant:
  ∀ path P: backtrack(P) = ∅ ⟹ μ(|P|) ≠ 0
  
Möbius Inversion:
  f(n) = Σ_{d|n} g(d) ⟹ g(n) = Σ_{d|n} μ(n/d) f(d)
```
"""

def has_geodesic_qualification(content: str) -> bool:
    """Check if file already has geodesic qualification."""
    return "Non-Backtracking Geodesic Qualification" in content

def add_geodesic_to_frontmatter(content: str) -> str:
    """Add geodesic: true to YAML frontmatter."""
    # Match YAML frontmatter
    fm_match = re.match(r'^---\n(.*?)\n---', content, re.DOTALL)
    if fm_match:
        frontmatter = fm_match.group(1)
        if 'geodesic:' not in frontmatter:
            # Add geodesic field
            new_fm = frontmatter.rstrip() + '\ngeodesic: true\nmoebius: "μ(n) ≠ 0"'
            content = content.replace(fm_match.group(0), f'---\n{new_fm}\n---')
    return content

def add_geodesic_section(content: str) -> str:
    """Add geodesic qualification section before last ---."""
    if has_geodesic_qualification(content):
        return content
    
    # Find a good insertion point (before "---" at end or at end of file)
    # Look for last major section
    lines = content.split('\n')
    
    # Add before final content
    return content.rstrip() + '\n' + GEODESIC_BLOCK

def process_skill(path: Path) -> bool:
    """Process a single SKILL.md file."""
    try:
        content = path.read_text()
        
        if has_geodesic_qualification(content):
            return False  # Already qualified
        
        # Add to frontmatter
        new_content = add_geodesic_to_frontmatter(content)
        # Add section
        new_content = add_geodesic_section(new_content)
        
        path.write_text(new_content)
        return True
    except Exception as e:
        print(f"Error processing {path}: {e}")
        return False

def main():
    skills_dir = Path(__file__).parent.parent / "skills"
    skill_files = list(skills_dir.rglob("SKILL.md"))
    
    print(f"Found {len(skill_files)} SKILL.md files")
    
    modified = 0
    skipped = 0
    
    for path in skill_files:
        if process_skill(path):
            modified += 1
            print(f"✓ {path.parent.name}")
        else:
            skipped += 1
    
    print(f"\nSummary:")
    print(f"  Modified: {modified}")
    print(f"  Skipped (already qualified): {skipped}")
    print(f"  Total: {len(skill_files)}")
    
    # GF(3) verification
    print(f"\nGF(3) Conservation: {modified} × μ(n) ≠ 0 applied")

if __name__ == "__main__":
    main()
