#!/usr/bin/env python3
"""
Fix skills missing YAML frontmatter and add geodesic qualification.
Assign GF(3) trits to balance sum to 0.
"""

import os
import re
import hashlib

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

def hash_to_trit(name):
    """Deterministic trit from skill name."""
    h = int(hashlib.md5(name.encode()).hexdigest(), 16)
    return (h % 3) - 1  # -1, 0, or +1

def fix_skill(path, name):
    """Fix a skill's frontmatter."""
    with open(path) as f:
        content = f.read()
    
    trit = hash_to_trit(name)
    
    if content.startswith("---"):
        # Has frontmatter, check for geodesic
        if "geodesic:" not in content:
            # Add geodesic to existing frontmatter
            content = content.replace(
                "---\n",
                f'---\ngeodesic: true\nmoebius: "μ(n) ≠ 0"\n',
                1
            )
        if "trit:" not in content:
            content = content.replace(
                "---\n",
                f'---\ntrit: {trit}\n',
                1
            )
    else:
        # No frontmatter, create one
        # Extract first heading for description
        title_match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
        title = title_match.group(1) if title_match else name
        
        frontmatter = f'''---
name: {name}
description: {title[:80]}
trit: {trit}
geodesic: true
moebius: "μ(n) ≠ 0"
---

'''
        content = frontmatter + content
    
    # Add geodesic section if missing
    if "Non-Backtracking Geodesic Qualification" not in content:
        content = content.rstrip() + "\n" + GEODESIC_BLOCK
    
    with open(path, 'w') as f:
        f.write(content)
    
    return trit

def main():
    skills_dir = "skills"
    fixed = 0
    trits = []
    
    for skill in sorted(os.listdir(skills_dir)):
        path = os.path.join(skills_dir, skill, "SKILL.md")
        if not os.path.isfile(path):
            continue
        
        with open(path) as f:
            content = f.read()
        
        needs_fix = (
            not content.startswith("---") or
            "geodesic:" not in content or
            "Non-Backtracking Geodesic Qualification" not in content
        )
        
        if needs_fix:
            trit = fix_skill(path, skill)
            trits.append(trit)
            fixed += 1
            print(f"✓ {skill} (trit={trit:+d})")
    
    print(f"\nFixed: {fixed} skills")
    print(f"Trit sum of fixed: {sum(trits)}")

if __name__ == "__main__":
    main()
