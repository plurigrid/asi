#!/usr/bin/env python3
"""Skills registry -> PyACSet JSON.

Builds a small categorical representation of `skills.json` in the same JSON shape
used by `skills/browser-history-acset/path_equivalence_test.py` (Schema + parts + subparts).

Usage:
  python3 ies/skills_acset.py --skills-json skills.json --out ies/skills_acset.json
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, List, Tuple


@dataclass
class Schema:
    name: str
    objects: List[str]
    homs: Dict[str, Tuple[str, str]]
    attrs: Dict[str, Tuple[str, str]]
    attrtypes: List[str] = field(default_factory=list)

    def to_dict(self) -> dict:
        return {
            "name": self.name,
            "objects": self.objects,
            "homs": {k: list(v) for k, v in self.homs.items()},
            "attrs": {k: list(v) for k, v in self.attrs.items()},
            "attrtypes": self.attrtypes,
        }


@dataclass
class PyACSet:
    """Python ACSet implementation matching ACSets.jl-style interface (1-indexed parts)."""

    schema: Schema
    parts: Dict[str, List[int]] = field(default_factory=dict)
    subparts: Dict[str, List[Any]] = field(default_factory=dict)

    def __post_init__(self) -> None:
        for ob in self.schema.objects:
            self.parts[ob] = []
        for hom in self.schema.homs:
            self.subparts[hom] = []
        for attr in self.schema.attrs:
            self.subparts[attr] = []

    def nparts(self, ob: str) -> int:
        return len(self.parts.get(ob, []))

    def add_part(self, ob: str) -> int:
        idx = len(self.parts[ob]) + 1
        self.parts[ob].append(idx)
        for hom, (dom, _) in self.schema.homs.items():
            if dom == ob:
                self.subparts[hom].append(None)
        for attr, (dom, _) in self.schema.attrs.items():
            if dom == ob:
                self.subparts[attr].append(None)
        return idx

    def set_subpart(self, part: int, hom_or_attr: str, value: Any) -> None:
        while len(self.subparts[hom_or_attr]) < part:
            self.subparts[hom_or_attr].append(None)
        self.subparts[hom_or_attr][part - 1] = value

    def subpart(self, part: int, hom_or_attr: str) -> Any:
        if part < 1 or part > len(self.subparts[hom_or_attr]):
            return None
        return self.subparts[hom_or_attr][part - 1]

    def to_json(self) -> dict:
        return {
            "schema": self.schema.to_dict(),
            "parts": {k: list(v) for k, v in self.parts.items()},
            "subparts": {k: list(v) for k, v in self.subparts.items()},
        }

    @classmethod
    def from_json(cls, data: dict) -> "PyACSet":
        schema = Schema(
            name=data["schema"]["name"],
            objects=data["schema"]["objects"],
            homs={k: tuple(v) for k, v in data["schema"]["homs"].items()},
            attrs={k: tuple(v) for k, v in data["schema"]["attrs"].items()},
            attrtypes=data["schema"].get("attrtypes", []),
        )
        acset = cls(schema=schema)
        acset.parts = {k: list(v) for k, v in data["parts"].items()}
        acset.subparts = {k: list(v) for k, v in data["subparts"].items()}
        return acset


SKILLS_SCHEMA = Schema(
    name="SkillsRegistry",
    objects=["Skill", "Category", "Author", "Source", "License"],
    homs={
        "has_category": ("Skill", "Category"),
        "authored_by": ("Skill", "Author"),
        "sourced_from": ("Skill", "Source"),
        "licensed_under": ("Skill", "License"),
    },
    attrs={
        "skill_name": ("Skill", "String"),
        "description": ("Skill", "String"),
        "path": ("Skill", "String"),
        "stars": ("Skill", "Int"),
        "downloads": ("Skill", "Int"),
        "featured": ("Skill", "Bool"),
        "verified": ("Skill", "Bool"),
        "category_name": ("Category", "String"),
        "author_name": ("Author", "String"),
        "source_name": ("Source", "String"),
        "license_name": ("License", "String"),
    },
    attrtypes=["String", "Int", "Bool"],
)


def build_skills_registry_acset(skills_json: dict) -> PyACSet:
    skills = skills_json.get("skills", [])

    acs = PyACSet(SKILLS_SCHEMA)

    cat_idx: Dict[str, int] = {}
    author_idx: Dict[str, int] = {}
    source_idx: Dict[str, int] = {}
    license_idx: Dict[str, int] = {}

    def get_or_add(ob: str, key: str, attr: str, table: Dict[str, int]) -> int:
        if key in table:
            return table[key]
        pid = acs.add_part(ob)
        acs.set_subpart(pid, attr, key)
        table[key] = pid
        return pid

    for s in skills:
        sid = acs.add_part("Skill")

        name = str(s.get("name", ""))
        description = str(s.get("description", ""))
        path = str(s.get("path", ""))

        category = str(s.get("category", ""))
        author = str(s.get("author", ""))
        source = str(s.get("source", ""))
        license_name = str(s.get("license", ""))

        stars = int(s.get("stars", 0) or 0)
        downloads = int(s.get("downloads", 0) or 0)
        featured = bool(s.get("featured", False))
        verified = bool(s.get("verified", False))

        acs.set_subpart(sid, "skill_name", name)
        acs.set_subpart(sid, "description", description)
        acs.set_subpart(sid, "path", path)
        acs.set_subpart(sid, "stars", stars)
        acs.set_subpart(sid, "downloads", downloads)
        acs.set_subpart(sid, "featured", featured)
        acs.set_subpart(sid, "verified", verified)

        c = get_or_add("Category", category, "category_name", cat_idx)
        a = get_or_add("Author", author, "author_name", author_idx)
        so = get_or_add("Source", source, "source_name", source_idx)
        li = get_or_add("License", license_name, "license_name", license_idx)

        acs.set_subpart(sid, "has_category", c)
        acs.set_subpart(sid, "authored_by", a)
        acs.set_subpart(sid, "sourced_from", so)
        acs.set_subpart(sid, "licensed_under", li)

    return acs


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--skills-json", default="skills.json")
    ap.add_argument("--out", default="ies/skills_acset.json")
    args = ap.parse_args()

    root = Path(__file__).resolve().parents[1]
    skills_path = (root / args.skills_json).resolve()
    out_path = (root / args.out).resolve()

    data = json.loads(skills_path.read_text(encoding="utf-8"))
    acs = build_skills_registry_acset(data)

    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(acs.to_json(), indent=2), encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
