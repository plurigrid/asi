#!/usr/bin/env python3
"""
Path Equivalence Tests: py-acset ↔ ACSets.jl

Verifies that:
1. Schema definitions are equivalent across Python and Julia
2. Morphism paths compose correctly (f ∘ g in both languages)
3. Incident queries return same results
4. Attribute lookups are consistent
5. ACSet operations preserve categorical structure

Based on patterns from:
- zip_acset_skill/extract_agent_o_rama.py (PyACSet)
- hatchery_repos/plurigrid__ACSets.jl/src/ACSetInterface.jl
- plurigrid-asi-skillz/skills/acsets/SKILL.md (Specter navigation)
"""

import json
import subprocess
import tempfile
import os
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Any, Tuple
from enum import Enum

# ═══════════════════════════════════════════════════════════════════════════════
# PyACSet Implementation (matches ACSets.jl interface)
# ═══════════════════════════════════════════════════════════════════════════════

@dataclass
class Schema:
    """Schema definition compatible with ACSets.jl BasicSchema."""
    name: str
    objects: List[str]
    homs: Dict[str, Tuple[str, str]]  # name -> (dom, codom)
    attrs: Dict[str, Tuple[str, str]]  # name -> (dom, attrtype)
    attrtypes: List[str] = field(default_factory=list)
    
    def to_julia(self) -> str:
        """Generate Julia @present macro for this schema."""
        lines = [f"@present Sch{self.name}(FreeSchema) begin"]
        
        # Objects
        for ob in self.objects:
            lines.append(f"    {ob}::Ob")
        
        # Attribute types
        for at in self.attrtypes:
            lines.append(f"    {at}::AttrType")
        
        # Homs
        for name, (dom, codom) in self.homs.items():
            lines.append(f"    {name}::Hom({dom}, {codom})")
        
        # Attrs
        for name, (dom, attrtype) in self.attrs.items():
            lines.append(f"    {name}::Attr({dom}, {attrtype})")
        
        lines.append("end")
        return "\n".join(lines)
    
    def to_dict(self) -> dict:
        """JSON-serializable representation."""
        return {
            "name": self.name,
            "objects": self.objects,
            "homs": {k: list(v) for k, v in self.homs.items()},
            "attrs": {k: list(v) for k, v in self.attrs.items()},
            "attrtypes": self.attrtypes
        }

@dataclass
class PyACSet:
    """Python ACSet implementation matching ACSets.jl interface."""
    schema: Schema
    parts: Dict[str, List[int]] = field(default_factory=dict)
    subparts: Dict[str, List[Any]] = field(default_factory=dict)
    
    def __post_init__(self):
        for ob in self.schema.objects:
            self.parts[ob] = []
        for hom in self.schema.homs:
            self.subparts[hom] = []
        for attr in self.schema.attrs:
            self.subparts[attr] = []
    
    def nparts(self, ob: str) -> int:
        """Number of parts of given type."""
        return len(self.parts.get(ob, []))
    
    def add_part(self, ob: str) -> int:
        """Add a part, return its ID (1-indexed like Julia)."""
        idx = len(self.parts[ob]) + 1  # 1-indexed to match Julia
        self.parts[ob].append(idx)
        # Initialize subparts for this part
        for hom, (dom, _) in self.schema.homs.items():
            if dom == ob:
                self.subparts[hom].append(None)
        for attr, (dom, _) in self.schema.attrs.items():
            if dom == ob:
                self.subparts[attr].append(None)
        return idx
    
    def add_parts(self, ob: str, n: int) -> List[int]:
        """Add n parts, return their IDs."""
        return [self.add_part(ob) for _ in range(n)]
    
    def set_subpart(self, part: int, hom_or_attr: str, value: Any):
        """Set subpart (morphism or attribute value)."""
        if hom_or_attr in self.schema.homs:
            dom, _ = self.schema.homs[hom_or_attr]
        elif hom_or_attr in self.schema.attrs:
            dom, _ = self.schema.attrs[hom_or_attr]
        else:
            raise ValueError(f"Unknown hom/attr: {hom_or_attr}")
        
        # Extend list if needed
        while len(self.subparts[hom_or_attr]) < part:
            self.subparts[hom_or_attr].append(None)
        self.subparts[hom_or_attr][part - 1] = value  # Convert to 0-indexed
    
    def subpart(self, part: int, hom_or_attr: str) -> Any:
        """Get subpart value."""
        if part < 1 or part > len(self.subparts[hom_or_attr]):
            return None
        return self.subparts[hom_or_attr][part - 1]
    
    def incident(self, target: int, hom: str) -> List[int]:
        """Find all parts that map to target via hom."""
        result = []
        for i, val in enumerate(self.subparts.get(hom, [])):
            if val == target:
                result.append(i + 1)  # 1-indexed
        return result
    
    def path(self, start: int, *homs: str) -> Any:
        """Follow a path of morphisms from start."""
        current = start
        for hom in homs:
            if current is None:
                return None
            current = self.subpart(current, hom)
        return current
    
    def to_json(self) -> dict:
        """Export to JSON format compatible with ACSets.jl."""
        return {
            "schema": self.schema.to_dict(),
            "parts": {k: list(v) for k, v in self.parts.items()},
            "subparts": {k: list(v) for k, v in self.subparts.items()}
        }
    
    @classmethod
    def from_json(cls, data: dict) -> 'PyACSet':
        """Import from JSON format."""
        schema = Schema(
            name=data["schema"]["name"],
            objects=data["schema"]["objects"],
            homs={k: tuple(v) for k, v in data["schema"]["homs"].items()},
            attrs={k: tuple(v) for k, v in data["schema"]["attrs"].items()},
            attrtypes=data["schema"].get("attrtypes", [])
        )
        acset = cls(schema=schema)
        acset.parts = {k: list(v) for k, v in data["parts"].items()}
        acset.subparts = {k: list(v) for k, v in data["subparts"].items()}
        return acset

# ═══════════════════════════════════════════════════════════════════════════════
# Test Schema: Browser History (matching SKILL.md patterns)
# ═══════════════════════════════════════════════════════════════════════════════

BROWSER_SCHEMA = Schema(
    name="BrowserHistory",
    objects=["Browser", "URL", "Visit", "Domain"],
    homs={
        "browser_of": ("URL", "Browser"),
        "domain_of": ("URL", "Domain"),
        "url_of": ("Visit", "URL"),
        "from_visit": ("Visit", "Visit"),
    },
    attrs={
        "browser_name": ("Browser", "String"),
        "url_text": ("URL", "String"),
        "visit_time": ("Visit", "Int"),
        "domain_name": ("Domain", "String"),
    },
    attrtypes=["String", "Int"]
)

# ═══════════════════════════════════════════════════════════════════════════════
# Path Equivalence Tests
# ═══════════════════════════════════════════════════════════════════════════════

class PathEquivalenceTest:
    """Test suite for py-acset ↔ ACSets.jl path equivalence."""
    
    def __init__(self, schema: Schema):
        self.schema = schema
        self.acset = PyACSet(schema)
        self.results: List[Tuple[str, bool, str]] = []
    
    def build_test_data(self):
        """Build test ACSet with known structure."""
        # Add browsers
        b1 = self.acset.add_part("Browser")
        b2 = self.acset.add_part("Browser")
        self.acset.set_subpart(b1, "browser_name", "ChatGPT Atlas")
        self.acset.set_subpart(b2, "browser_name", "Safari")
        
        # Add domains
        d1 = self.acset.add_part("Domain")
        d2 = self.acset.add_part("Domain")
        d3 = self.acset.add_part("Domain")
        self.acset.set_subpart(d1, "domain_name", "github.com")
        self.acset.set_subpart(d2, "domain_name", "ampcode.com")
        self.acset.set_subpart(d3, "domain_name", "chatgpt.com")
        
        # Add URLs
        u1 = self.acset.add_part("URL")
        u2 = self.acset.add_part("URL")
        u3 = self.acset.add_part("URL")
        u4 = self.acset.add_part("URL")
        
        self.acset.set_subpart(u1, "url_text", "https://github.com/bmorphism/Gay.jl")
        self.acset.set_subpart(u1, "browser_of", b1)
        self.acset.set_subpart(u1, "domain_of", d1)
        
        self.acset.set_subpart(u2, "url_text", "https://ampcode.com/workspaces/ies")
        self.acset.set_subpart(u2, "browser_of", b1)
        self.acset.set_subpart(u2, "domain_of", d2)
        
        self.acset.set_subpart(u3, "url_text", "https://chatgpt.com/")
        self.acset.set_subpart(u3, "browser_of", b1)
        self.acset.set_subpart(u3, "domain_of", d3)
        
        self.acset.set_subpart(u4, "url_text", "https://github.com/AlgebraicJulia")
        self.acset.set_subpart(u4, "browser_of", b2)
        self.acset.set_subpart(u4, "domain_of", d1)
        
        # Add visits with temporal ordering
        v1 = self.acset.add_part("Visit")
        v2 = self.acset.add_part("Visit")
        v3 = self.acset.add_part("Visit")
        v4 = self.acset.add_part("Visit")
        v5 = self.acset.add_part("Visit")
        
        self.acset.set_subpart(v1, "url_of", u1)
        self.acset.set_subpart(v1, "visit_time", 1000)
        
        self.acset.set_subpart(v2, "url_of", u2)
        self.acset.set_subpart(v2, "visit_time", 1001)
        self.acset.set_subpart(v2, "from_visit", v1)  # Navigated from v1
        
        self.acset.set_subpart(v3, "url_of", u3)
        self.acset.set_subpart(v3, "visit_time", 1002)
        self.acset.set_subpart(v3, "from_visit", v2)  # Navigated from v2
        
        self.acset.set_subpart(v4, "url_of", u1)
        self.acset.set_subpart(v4, "visit_time", 1003)
        self.acset.set_subpart(v4, "from_visit", v3)  # Back to github
        
        self.acset.set_subpart(v5, "url_of", u4)
        self.acset.set_subpart(v5, "visit_time", 1004)
        # v5 is independent (new session)
        
        return self.acset
    
    def test_nparts(self) -> bool:
        """Test 1: Part counts match schema objects."""
        expected = {"Browser": 2, "URL": 4, "Visit": 5, "Domain": 3}
        for ob, count in expected.items():
            actual = self.acset.nparts(ob)
            if actual != count:
                self.results.append((f"nparts({ob})", False, f"expected {count}, got {actual}"))
                return False
        self.results.append(("nparts", True, f"All counts correct: {expected}"))
        return True
    
    def test_subpart_lookup(self) -> bool:
        """Test 2: Subpart lookups return correct values."""
        # Test hom lookup
        browser = self.acset.subpart(1, "browser_of")  # URL 1 -> Browser
        if browser != 1:
            self.results.append(("subpart_hom", False, f"URL 1 browser_of expected 1, got {browser}"))
            return False
        
        # Test attr lookup
        name = self.acset.subpart(1, "browser_name")
        if name != "ChatGPT Atlas":
            self.results.append(("subpart_attr", False, f"Browser 1 name expected 'ChatGPT Atlas', got {name}"))
            return False
        
        self.results.append(("subpart_lookup", True, "Hom and attr lookups correct"))
        return True
    
    def test_incident(self) -> bool:
        """Test 3: Incident queries find all sources."""
        # Find all URLs in Browser 1
        urls_in_b1 = self.acset.incident(1, "browser_of")
        expected = [1, 2, 3]  # URLs 1, 2, 3 are in Browser 1
        if sorted(urls_in_b1) != expected:
            self.results.append(("incident", False, f"expected {expected}, got {sorted(urls_in_b1)}"))
            return False
        
        # Find all URLs in Domain 1 (github.com)
        urls_in_d1 = self.acset.incident(1, "domain_of")
        expected_d1 = [1, 4]  # URLs 1 and 4 are github.com
        if sorted(urls_in_d1) != expected_d1:
            self.results.append(("incident", False, f"domain incident expected {expected_d1}, got {sorted(urls_in_d1)}"))
            return False
        
        self.results.append(("incident", True, f"Incident queries correct"))
        return True
    
    def test_path_composition(self) -> bool:
        """Test 4: Path composition (f ∘ g) works correctly."""
        # Path: Visit -> URL -> Domain
        # Visit 1 -> URL 1 -> Domain 1 (github.com)
        url = self.acset.path(1, "url_of")
        domain = self.acset.path(1, "url_of", "domain_of")
        
        if url != 1:
            self.results.append(("path_single", False, f"Visit 1 url_of expected 1, got {url}"))
            return False
        
        if domain != 1:
            self.results.append(("path_compose", False, f"Visit 1 url_of;domain_of expected 1, got {domain}"))
            return False
        
        # Path: Visit -> URL -> Browser
        browser = self.acset.path(2, "url_of", "browser_of")
        if browser != 1:
            self.results.append(("path_compose_2", False, f"Visit 2 url_of;browser_of expected 1, got {browser}"))
            return False
        
        self.results.append(("path_composition", True, "Path composition correct"))
        return True
    
    def test_reflexive_hom(self) -> bool:
        """Test 5: Reflexive morphism (from_visit: Visit -> Visit) works."""
        # Follow navigation chain: v1 <- v2 <- v3 <- v4
        v2_from = self.acset.subpart(2, "from_visit")
        v3_from = self.acset.subpart(3, "from_visit")
        v4_from = self.acset.subpart(4, "from_visit")
        v5_from = self.acset.subpart(5, "from_visit")  # Should be None
        
        if v2_from != 1:
            self.results.append(("reflexive", False, f"v2 from_visit expected 1, got {v2_from}"))
            return False
        if v3_from != 2:
            self.results.append(("reflexive", False, f"v3 from_visit expected 2, got {v3_from}"))
            return False
        if v4_from != 3:
            self.results.append(("reflexive", False, f"v4 from_visit expected 3, got {v4_from}"))
            return False
        if v5_from is not None:
            self.results.append(("reflexive", False, f"v5 from_visit expected None, got {v5_from}"))
            return False
        
        self.results.append(("reflexive_hom", True, "Reflexive from_visit chain correct"))
        return True
    
    def test_path_chain(self) -> bool:
        """Test 6: Multi-step reflexive path."""
        # Follow chain: v4 -> v3 -> v2 -> v1
        step1 = self.acset.subpart(4, "from_visit")  # -> v3
        step2 = self.acset.subpart(step1, "from_visit") if step1 else None  # -> v2
        step3 = self.acset.subpart(step2, "from_visit") if step2 else None  # -> v1
        step4 = self.acset.subpart(step3, "from_visit") if step3 else None  # -> None
        
        if (step1, step2, step3, step4) != (3, 2, 1, None):
            self.results.append(("path_chain", False, 
                f"expected (3,2,1,None), got ({step1},{step2},{step3},{step4})"))
            return False
        
        self.results.append(("path_chain", True, "Multi-step reflexive path correct"))
        return True
    
    def test_json_roundtrip(self) -> bool:
        """Test 7: JSON serialization roundtrip preserves structure."""
        json_data = self.acset.to_json()
        reconstructed = PyACSet.from_json(json_data)
        
        # Compare parts
        for ob in self.schema.objects:
            if reconstructed.nparts(ob) != self.acset.nparts(ob):
                self.results.append(("json_roundtrip", False, 
                    f"{ob} parts mismatch after roundtrip"))
                return False
        
        # Compare subparts
        for hom in self.schema.homs:
            if reconstructed.subparts[hom] != self.acset.subparts[hom]:
                self.results.append(("json_roundtrip", False,
                    f"{hom} subparts mismatch after roundtrip"))
                return False
        
        self.results.append(("json_roundtrip", True, "JSON roundtrip preserves structure"))
        return True
    
    def generate_julia_test(self) -> str:
        """Generate equivalent Julia test code."""
        return f'''
# Julia ACSets.jl Path Equivalence Test
# Auto-generated from Python test suite

using ACSets

# Schema definition
{self.schema.to_julia()}

@acset_type BrowserHistoryACSet(SchBrowserHistory)

# Build test data
acs = BrowserHistoryACSet()

# Add browsers
b1 = add_part!(acs, :Browser; browser_name="ChatGPT Atlas")
b2 = add_part!(acs, :Browser; browser_name="Safari")

# Add domains
d1 = add_part!(acs, :Domain; domain_name="github.com")
d2 = add_part!(acs, :Domain; domain_name="ampcode.com")
d3 = add_part!(acs, :Domain; domain_name="chatgpt.com")

# Add URLs
u1 = add_part!(acs, :URL; url_text="https://github.com/bmorphism/Gay.jl", browser_of=b1, domain_of=d1)
u2 = add_part!(acs, :URL; url_text="https://ampcode.com/workspaces/ies", browser_of=b1, domain_of=d2)
u3 = add_part!(acs, :URL; url_text="https://chatgpt.com/", browser_of=b1, domain_of=d3)
u4 = add_part!(acs, :URL; url_text="https://github.com/AlgebraicJulia", browser_of=b2, domain_of=d1)

# Add visits
v1 = add_part!(acs, :Visit; url_of=u1, visit_time=1000)
v2 = add_part!(acs, :Visit; url_of=u2, visit_time=1001, from_visit=v1)
v3 = add_part!(acs, :Visit; url_of=u3, visit_time=1002, from_visit=v2)
v4 = add_part!(acs, :Visit; url_of=u1, visit_time=1003, from_visit=v3)
v5 = add_part!(acs, :Visit; url_of=u4, visit_time=1004)

# Tests
@assert nparts(acs, :Browser) == 2
@assert nparts(acs, :URL) == 4
@assert nparts(acs, :Visit) == 5
@assert nparts(acs, :Domain) == 3

# Subpart lookup
@assert subpart(acs, 1, :browser_of) == 1
@assert subpart(acs, 1, :browser_name) == "ChatGPT Atlas"

# Incident
@assert sort(incident(acs, 1, :browser_of)) == [1, 2, 3]
@assert sort(incident(acs, 1, :domain_of)) == [1, 4]

# Path composition
@assert subpart(acs, 1, :url_of) == 1
@assert subpart(acs, subpart(acs, 1, :url_of), :domain_of) == 1

# Reflexive hom chain
@assert subpart(acs, 2, :from_visit) == 1
@assert subpart(acs, 3, :from_visit) == 2
@assert subpart(acs, 4, :from_visit) == 3

println("✓ All ACSets.jl path equivalence tests passed!")
'''
    
    def run_all(self) -> bool:
        """Run all tests."""
        self.build_test_data()
        
        all_passed = True
        tests = [
            self.test_nparts,
            self.test_subpart_lookup,
            self.test_incident,
            self.test_path_composition,
            self.test_reflexive_hom,
            self.test_path_chain,
            self.test_json_roundtrip,
        ]
        
        for test in tests:
            if not test():
                all_passed = False
        
        return all_passed
    
    def report(self) -> str:
        """Generate test report."""
        lines = [
            "═" * 70,
            "PATH EQUIVALENCE TEST REPORT",
            "py-acset ↔ ACSets.jl Compatibility",
            "═" * 70,
        ]
        
        passed = sum(1 for _, ok, _ in self.results if ok)
        total = len(self.results)
        
        for name, ok, msg in self.results:
            status = "✓" if ok else "✗"
            lines.append(f"  {status} {name}: {msg}")
        
        lines.append("─" * 70)
        lines.append(f"  {passed}/{total} tests passed")
        lines.append("═" * 70)
        
        return "\n".join(lines)

def main():
    """Run path equivalence tests."""
    print("=" * 70)
    print("PY-ACSET ↔ ACSETS.JL PATH EQUIVALENCE TESTS")
    print("=" * 70)
    
    # Run Python tests
    test = PathEquivalenceTest(BROWSER_SCHEMA)
    all_passed = test.run_all()
    print(test.report())
    
    # Export Julia test
    julia_code = test.generate_julia_test()
    with open("path_equivalence_test.jl", "w") as f:
        f.write(julia_code)
    print("\n✓ Julia test code exported to path_equivalence_test.jl")
    
    # Export test ACSet as JSON
    json_data = test.acset.to_json()
    with open("test_acset.json", "w") as f:
        json.dump(json_data, f, indent=2)
    print("✓ Test ACSet exported to test_acset.json")
    
    # Summary
    if all_passed:
        print("\n✓ All Python path equivalence tests PASSED")
    else:
        print("\n✗ Some tests FAILED")
    
    return all_passed

if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)
