#!/usr/bin/env python3
"""Skill finder and verifier — identifies locally-created and modified skills."""
import os
import sys
import hashlib
import json
from pathlib import Path
from difflib import unified_diff

ASI_SKILLS = Path("/Users/alice/v/asi/skills")

SKILL_DIRS = {
    "agents": Path("/Users/alice/v/.agents/skills"),
    "claude": Path("/Users/alice/.claude/skills"),
    "codex": Path("/Users/alice/.codex/skills"),
    "goose": Path("/Users/alice/.config/goose/skills"),
    "copilot": Path("/Users/alice/.copilot/skills"),
    "openhands": Path("/Users/alice/.openhands/skills"),
}

# Known standalone skill locations
STANDALONE = [
    Path("/Users/alice/repos/skills/skill-codex"),
    Path("/Users/alice/ies/mcp/topos"),
    Path("/Users/alice/v/gay-terminal-colors"),
]

# Skip these (meta/system entries, not real skills)
SKIP = {"_integrated", "init", "dist", "_archive", "a", "b", "c", "d", "e", "f",
        "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t",
        "u", "v", "w", "x", "y", "z", "external", "assets"}


def file_hash(path):
    if not path.exists():
        return None
    return hashlib.sha256(path.read_bytes()).hexdigest()


def diff_lines(asi_path, local_path):
    """Count added/removed lines between asi and local SKILL.md."""
    if not asi_path.exists() or not local_path.exists():
        return None
    asi = asi_path.read_text(errors="replace").splitlines(keepends=True)
    local = local_path.read_text(errors="replace").splitlines(keepends=True)
    diff = list(unified_diff(asi, local, n=0))
    added = sum(1 for l in diff if l.startswith("+") and not l.startswith("+++"))
    removed = sum(1 for l in diff if l.startswith("-") and not l.startswith("---"))
    return {"added": added, "removed": removed, "total_change": added + removed}


def has_scripts(skill_dir):
    """Check if skill has scripts/ directory with content."""
    scripts = skill_dir / "scripts"
    if scripts.is_dir():
        return len(list(scripts.iterdir())) > 0
    return False


def local_extras(skill_dir, asi_dir):
    """Find files in local skill that don't exist in asi version."""
    if not asi_dir.exists():
        return []
    local_files = set()
    asi_files = set()
    for f in skill_dir.rglob("*"):
        if f.is_file():
            local_files.add(f.relative_to(skill_dir))
    for f in asi_dir.rglob("*"):
        if f.is_file():
            asi_files.add(f.relative_to(asi_dir))
    return sorted(str(f) for f in local_files - asi_files)


def classify_skill(name, local_dir):
    """Classify a skill as local-only, identical, or modified."""
    asi_dir = ASI_SKILLS / name
    skill_md = local_dir / "SKILL.md"
    skill_md_lower = local_dir / "skill.md"
    local_md = skill_md if skill_md.exists() else (skill_md_lower if skill_md_lower.exists() else None)

    if not local_md:
        return {"status": "no-skill-md", "name": name}

    if not asi_dir.exists():
        return {
            "status": "local-only",
            "name": name,
            "has_scripts": has_scripts(local_dir),
            "lines": sum(1 for _ in local_md.read_text(errors="replace").splitlines()),
        }

    asi_md = asi_dir / "SKILL.md"
    if not asi_md.exists():
        return {"status": "local-only", "name": name, "has_scripts": has_scripts(local_dir),
                "lines": sum(1 for _ in local_md.read_text(errors="replace").splitlines())}

    if file_hash(asi_md) == file_hash(local_md):
        extras = local_extras(local_dir, asi_dir)
        if extras:
            return {"status": "identical-md-extra-files", "name": name, "extras": extras}
        return {"status": "identical", "name": name}

    delta = diff_lines(asi_md, local_md)
    extras = local_extras(local_dir, asi_dir)
    return {
        "status": "modified",
        "name": name,
        "diff": delta,
        "extras": extras,
        "has_scripts": has_scripts(local_dir),
        "local_lines": sum(1 for _ in local_md.read_text(errors="replace").splitlines()),
        "asi_lines": sum(1 for _ in asi_md.read_text(errors="replace").splitlines()),
    }


def scan(location=None, show_all=False):
    """Scan skill directories and classify each skill."""
    dirs = {location: SKILL_DIRS[location]} if location else SKILL_DIRS
    local_only = []
    modified = []
    identical_count = 0

    for loc, base in dirs.items():
        if not base.exists():
            continue
        for entry in sorted(base.iterdir()):
            if not entry.is_dir() or entry.name in SKIP or entry.name.startswith("."):
                continue
            result = classify_skill(entry.name, entry)
            result["location"] = loc
            if result["status"] == "local-only":
                local_only.append(result)
            elif result["status"] in ("modified", "identical-md-extra-files"):
                modified.append(result)
            elif result["status"] == "identical":
                identical_count += 1

    # Standalone
    for sd in STANDALONE:
        if sd.exists():
            result = classify_skill(sd.name, sd)
            result["location"] = "standalone"
            if result["status"] == "local-only":
                local_only.append(result)

    # Deduplicate by name (keep first occurrence)
    seen = set()
    deduped_local = []
    for s in local_only:
        if s["name"] not in seen:
            seen.add(s["name"])
            deduped_local.append(s)
    deduped_modified = []
    for s in modified:
        if s["name"] not in seen:
            seen.add(s["name"])
            deduped_modified.append(s)

    print(f"\n=== Locally Created (not in asi) === [{len(deduped_local)} unique]")
    for s in deduped_local:
        scripts = " +scripts" if s.get("has_scripts") else ""
        print(f"  {s['name']:50s} ({s['location']}, {s.get('lines', '?')} lines{scripts})")

    print(f"\n=== Modified from asi === [{len(deduped_modified)} unique]")
    for s in deduped_modified:
        if s["status"] == "identical-md-extra-files":
            print(f"  {s['name']:50s} ({s['location']}, SKILL.md identical, extras: {s['extras']})")
        else:
            d = s.get("diff", {})
            extras = f", extras: {s['extras']}" if s.get("extras") else ""
            print(f"  {s['name']:50s} ({s['location']}, +{d.get('added', 0)}/-{d.get('removed', 0)} lines{extras})")

    print(f"\n=== Identical to asi === {identical_count} skills (batch-installed, unmodified)")
    print(f"\nTotal unique local/modified: {len(deduped_local) + len(deduped_modified)}")


def verify(name):
    """Verify a single skill's provenance across all directories."""
    print(f"\n=== Verifying: {name} ===\n")
    found = []
    for loc, base in SKILL_DIRS.items():
        skill_dir = base / name
        if skill_dir.exists():
            result = classify_skill(name, skill_dir)
            result["location"] = loc
            found.append(result)

    # Check standalone
    for sd in STANDALONE:
        if sd.name == name and sd.exists():
            result = classify_skill(name, sd)
            result["location"] = "standalone"
            found.append(result)

    if not found:
        print(f"  Skill '{name}' not found in any directory.")
        return

    asi_dir = ASI_SKILLS / name
    print(f"  In asi upstream: {'YES' if asi_dir.exists() else 'NO'}")
    print(f"  Found in {len(found)} location(s):\n")

    for r in found:
        print(f"  [{r['location']}] status={r['status']}")
        if r["status"] == "modified":
            d = r.get("diff", {})
            print(f"    SKILL.md: {r.get('asi_lines', '?')} -> {r.get('local_lines', '?')} lines (+{d.get('added', 0)}/-{d.get('removed', 0)})")
            if r.get("extras"):
                print(f"    Extra files: {r['extras']}")
        elif r["status"] == "local-only":
            print(f"    Lines: {r.get('lines', '?')}, scripts: {r.get('has_scripts', False)}")


def diff_skill(name):
    """Show the actual diff between asi and local version."""
    for loc, base in SKILL_DIRS.items():
        local_md = base / name / "SKILL.md"
        asi_md = ASI_SKILLS / name / "SKILL.md"
        if local_md.exists() and asi_md.exists():
            asi = asi_md.read_text(errors="replace").splitlines(keepends=True)
            local = local_md.read_text(errors="replace").splitlines(keepends=True)
            diff = unified_diff(asi, local, fromfile=f"asi/{name}/SKILL.md", tofile=f"{loc}/{name}/SKILL.md")
            output = "".join(diff)
            if output:
                print(f"\n=== {loc}/{name} vs asi ===")
                print(output)
            else:
                print(f"\n=== {loc}/{name}: identical to asi ===")
            return
    print(f"Cannot diff: {name} not found in both asi and local.")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "scan"
    if cmd == "scan":
        location = sys.argv[2] if len(sys.argv) > 2 else None
        scan(location)
    elif cmd == "verify":
        if len(sys.argv) < 3:
            print("Usage: finder.py verify <skill-name>")
        else:
            verify(sys.argv[2])
    elif cmd == "diff":
        if len(sys.argv) < 3:
            print("Usage: finder.py diff <skill-name>")
        else:
            diff_skill(sys.argv[2])
    else:
        print(f"Usage: {sys.argv[0]} [scan [location]|verify <name>|diff <name>]")
