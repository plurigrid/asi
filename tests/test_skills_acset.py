import json
from pathlib import Path

from ies.skills_acset import PyACSet, build_skills_registry_acset


def test_build_skills_registry_acset_counts_match_skills_json():
    root = Path(__file__).resolve().parents[1]
    skills = json.loads((root / "skills.json").read_text(encoding="utf-8"))

    acs = build_skills_registry_acset(skills)

    assert acs.schema.name == "SkillsRegistry"
    assert acs.nparts("Skill") == len(skills.get("skills", []))


def test_build_skills_registry_acset_has_required_morphisms_populated():
    root = Path(__file__).resolve().parents[1]
    skills = json.loads((root / "skills.json").read_text(encoding="utf-8"))

    acs = build_skills_registry_acset(skills)

    # Check first few skills have all morphisms set
    n = min(10, acs.nparts("Skill"))
    for sid in range(1, n + 1):
        assert acs.subpart(sid, "has_category") is not None
        assert acs.subpart(sid, "authored_by") is not None
        assert acs.subpart(sid, "sourced_from") is not None
        assert acs.subpart(sid, "licensed_under") is not None


def test_roundtrip_json_preserves_part_counts():
    root = Path(__file__).resolve().parents[1]
    skills = json.loads((root / "skills.json").read_text(encoding="utf-8"))

    acs = build_skills_registry_acset(skills)
    recon = PyACSet.from_json(acs.to_json())

    assert recon.nparts("Skill") == acs.nparts("Skill")
    assert recon.nparts("Category") == acs.nparts("Category")
    assert recon.nparts("Author") == acs.nparts("Author")
    assert recon.nparts("Source") == acs.nparts("Source")
    assert recon.nparts("License") == acs.nparts("License")
