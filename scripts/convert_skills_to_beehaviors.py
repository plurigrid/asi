#!/usr/bin/env python3
"""Convert ASI skills into beehavior records (lossless + scenario views)."""

from __future__ import annotations

import json
import os
import re
import datetime
from dataclasses import dataclass
from typing import Any, Dict, Iterable, List, Optional, Tuple

ASI_ROOT = "/Users/bob/i/asi"
SKILLS_DIR = os.path.join(ASI_ROOT, "skills")
TRIT_ASSIGNMENTS_PATH = os.path.join(
    SKILLS_DIR, "coequalizers", "skill_trit_assignments.json"
)
OUTPUT_PATH = os.path.join(ASI_ROOT, "behaviors", "beehaviors.jsonl")

ORG_EXTENSIONS = (".org",)
GEODESIC_DIRNAME = "geodesics"
TANGLED_EXTENSIONS = (".jl", ".py", ".clj", ".scm", ".ts", ".js", ".hy")


@dataclass
class Representation:
    rep_type: str  # org, geodesic, tangled
    path: str
    exists: bool
    line_count: int
    size_bytes: int


@dataclass
class BehavioralSignature:
    has_code: bool
    primary_language: str
    code_block_count: int
    trit: Optional[int]
    execution_path_length: int


@dataclass
class SkillNode:
    name: str
    skill_dir: str
    representations: List[Representation]
    behavior: BehavioralSignature
    cites: List[str]
    cited_by: List[str]
    trit_neighbors: List[str]
    behavior_neighbors: List[str]


def read_text(path: str) -> str:
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        return f.read()


def split_frontmatter(text: str) -> Tuple[Optional[str], str]:
    if not text.startswith("---"):
        return None, text
    parts = text.split("---", 2)
    if len(parts) < 3:
        return None, text
    frontmatter = parts[1].strip("\n")
    body = parts[2].lstrip("\n")
    return frontmatter, body


def parse_frontmatter(frontmatter: Optional[str]) -> Dict[str, Any]:
    if not frontmatter:
        return {}
    # Try YAML if available; fallback to a minimal parser.
    try:
        import yaml  # type: ignore

        data = yaml.safe_load(frontmatter)
        return data if isinstance(data, dict) else {}
    except Exception:
        parsed: Dict[str, Any] = {}
        for line in frontmatter.splitlines():
            if not line.strip() or line.strip().startswith("#"):
                continue
            if ":" not in line:
                continue
            key, value = line.split(":", 1)
            parsed[key.strip()] = value.strip().strip('"')
        return parsed


def detect_representations(skill_dir: str) -> List[Representation]:
    reps: List[Representation] = []

    for entry in os.listdir(skill_dir):
        path = os.path.join(skill_dir, entry)
        if os.path.isfile(path) and entry.endswith(ORG_EXTENSIONS):
            stats = os.stat(path)
            reps.append(
                Representation(
                    rep_type="org",
                    path=path,
                    exists=True,
                    line_count=count_lines(path),
                    size_bytes=stats.st_size,
                )
            )

    geodesic_dir = os.path.join(skill_dir, GEODESIC_DIRNAME)
    if os.path.isdir(geodesic_dir):
        for entry in os.listdir(geodesic_dir):
            path = os.path.join(geodesic_dir, entry)
            if os.path.isfile(path) and ".geodesic." in entry:
                stats = os.stat(path)
                reps.append(
                    Representation(
                        rep_type="geodesic",
                        path=path,
                        exists=True,
                        line_count=count_lines(path),
                        size_bytes=stats.st_size,
                    )
                )

    for entry in os.listdir(skill_dir):
        path = os.path.join(skill_dir, entry)
        if os.path.isfile(path) and entry.endswith(TANGLED_EXTENSIONS):
            if GEODESIC_DIRNAME in path:
                continue
            stats = os.stat(path)
            reps.append(
                Representation(
                    rep_type="tangled",
                    path=path,
                    exists=True,
                    line_count=count_lines(path),
                    size_bytes=stats.st_size,
                )
            )

    return reps


def count_lines(path: str) -> int:
    count = 0
    with open(path, "r", encoding="utf-8", errors="replace") as f:
        for _ in f:
            count += 1
    return count


def infer_primary_language(reps: Iterable[Representation]) -> str:
    counts: Dict[str, int] = {}
    for rep in reps:
        if rep.rep_type != "geodesic":
            continue
        if rep.path.endswith(".jl"):
            counts["julia"] = counts.get("julia", 0) + 1
        elif rep.path.endswith(".py"):
            counts["python"] = counts.get("python", 0) + 1
        elif rep.path.endswith(".clj"):
            counts["clojure"] = counts.get("clojure", 0) + 1
        elif rep.path.endswith(".ts") or rep.path.endswith(".js"):
            counts["javascript"] = counts.get("javascript", 0) + 1
        elif rep.path.endswith(".hy"):
            counts["hy"] = counts.get("hy", 0) + 1
    if not counts:
        return "none"
    return sorted(counts.items(), key=lambda kv: kv[1], reverse=True)[0][0]


def infer_behavior(
    reps: List[Representation],
    skill_name: str,
    trit_map: Dict[str, int],
    frontmatter: Dict[str, Any],
) -> BehavioralSignature:
    has_code = any(r.rep_type in {"org", "geodesic", "tangled"} for r in reps)
    primary_language = infer_primary_language(reps)
    code_block_count = sum(1 for r in reps if r.rep_type == "org")

    trit = trit_map.get(skill_name)
    if trit is None:
        fm_trit = frontmatter.get("trit")
        if fm_trit is None and isinstance(frontmatter.get("metadata"), dict):
            fm_trit = frontmatter.get("metadata", {}).get("trit")
        if isinstance(fm_trit, str) and fm_trit.strip().lstrip("+-").isdigit():
            trit = int(fm_trit)
        elif isinstance(fm_trit, int):
            trit = fm_trit

    has_geodesic = any(r.rep_type == "geodesic" for r in reps)
    exec_path_length = 1 if has_geodesic else 2

    return BehavioralSignature(
        has_code=has_code,
        primary_language=primary_language,
        code_block_count=code_block_count,
        trit=trit,
        execution_path_length=exec_path_length,
    )


def extract_citations(skill_dir: str) -> List[str]:
    skill_md = os.path.join(skill_dir, "SKILL.md")
    if not os.path.isfile(skill_md):
        return []

    cites: List[str] = []
    in_related = False
    for line in read_text(skill_md).splitlines():
        if re.match(r"^##\s+Related Skills", line):
            in_related = True
            continue
        if in_related and line.startswith("##"):
            break
        if in_related:
            for m in re.finditer(r"`([a-z0-9\-]+)`", line):
                cites.append(m.group(1))

    return sorted(set(cites))


def load_trit_assignments(path: str) -> Dict[str, int]:
    if not os.path.isfile(path):
        return {}
    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)
    trit_map: Dict[str, int] = {}
    for trit_str, skills in data.items():
        try:
            trit_val = int(trit_str)
        except ValueError:
            continue
        for skill in skills:
            trit_map[skill] = trit_val
    return trit_map


def find_trit_neighbors(skill: str, trit: Optional[int], trit_map: Dict[str, int]) -> List[str]:
    if trit is None:
        return []
    neighbors = [other for other, other_trit in trit_map.items() if other != skill and other_trit == trit]
    return sorted(neighbors)


def find_behavioral_neighbors(node: SkillNode, all_nodes: Dict[str, SkillNode], threshold: float = 0.5) -> List[str]:
    neighbors: List[str] = []
    for other_name, other in all_nodes.items():
        if other_name == node.name:
            continue
        similarity = 0.0
        if node.behavior.primary_language == other.behavior.primary_language and node.behavior.primary_language != "none":
            similarity += 0.4
        if node.behavior.code_block_count > 0 and other.behavior.code_block_count > 0:
            ratio = min(node.behavior.code_block_count, other.behavior.code_block_count) / max(
                node.behavior.code_block_count, other.behavior.code_block_count
            )
            similarity += 0.3 * ratio
        if node.behavior.execution_path_length == other.behavior.execution_path_length:
            similarity += 0.3
        if similarity >= threshold:
            neighbors.append(other_name)
    return sorted(neighbors)


def build_graph(skills_dir: str, trit_map: Dict[str, int]) -> Dict[str, SkillNode]:
    nodes: Dict[str, SkillNode] = {}

    for entry in sorted(os.listdir(skills_dir)):
        if entry.startswith("."):
            continue
        skill_path = os.path.join(skills_dir, entry)
        if not os.path.isdir(skill_path):
            continue

        skill_md = os.path.join(skill_path, "SKILL.md")
        frontmatter_raw = None
        frontmatter: Dict[str, Any] = {}
        if os.path.isfile(skill_md):
            fm_raw, _ = split_frontmatter(read_text(skill_md))
            frontmatter_raw = fm_raw
            frontmatter = parse_frontmatter(frontmatter_raw)

        reps = detect_representations(skill_path)
        behavior = infer_behavior(reps, entry, trit_map, frontmatter)
        cites = extract_citations(skill_path)
        trit_neighbors = find_trit_neighbors(entry, behavior.trit, trit_map)

        nodes[entry] = SkillNode(
            name=entry,
            skill_dir=skill_path,
            representations=reps,
            behavior=behavior,
            cites=cites,
            cited_by=[],
            trit_neighbors=trit_neighbors,
            behavior_neighbors=[],
        )

    for name, node in nodes.items():
        for cited in node.cites:
            if cited in nodes:
                nodes[cited].cited_by.append(name)

    for node in nodes.values():
        node.cited_by = sorted(set(node.cited_by))

    for node in nodes.values():
        node.behavior_neighbors = find_behavioral_neighbors(node, nodes)

    return nodes


def build_scenarios(node: SkillNode) -> Dict[str, Any]:
    reachable = {
        "citation_out": node.cites,
        "citation_in": node.cited_by,
        "behavior_neighbors": node.behavior_neighbors,
        "trit_neighbors": node.trit_neighbors,
    }

    isotropic_all = sorted(
        set(
            reachable["citation_out"]
            + reachable["citation_in"]
            + reachable["behavior_neighbors"]
            + reachable["trit_neighbors"]
        )
    )

    anisotropic: Dict[str, Any] = {
        "by_edge_type": reachable,
        "by_trit": {},
    }

    return {
        "reachable": reachable,
        "isotropic": {"all_neighbors": isotropic_all},
        "anisotropic": anisotropic,
    }


def enrich_anisotropic_by_trit(scenarios: Dict[str, Any], node: SkillNode, nodes: Dict[str, SkillNode]) -> None:
    by_trit: Dict[str, List[str]] = {"-1": [], "0": [], "+1": [], "unknown": []}

    all_neighbors = scenarios["isotropic"]["all_neighbors"]
    for neighbor in all_neighbors:
        other = nodes.get(neighbor)
        trit = other.behavior.trit if other else None
        if trit in (-1, 0, 1):
            key = "+1" if trit == 1 else str(trit)
            by_trit[key].append(neighbor)
        else:
            by_trit["unknown"].append(neighbor)

    for key in list(by_trit.keys()):
        by_trit[key] = sorted(set(by_trit[key]))

    scenarios["anisotropic"]["by_trit"] = by_trit


def build_record(node: SkillNode, nodes: Dict[str, SkillNode]) -> Dict[str, Any]:
    skill_md = os.path.join(node.skill_dir, "SKILL.md")
    frontmatter_raw = None
    body_raw = ""
    frontmatter = {}

    if os.path.isfile(skill_md):
        text = read_text(skill_md)
        frontmatter_raw, body_raw = split_frontmatter(text)
        frontmatter = parse_frontmatter(frontmatter_raw)

    scenarios = build_scenarios(node)
    enrich_anisotropic_by_trit(scenarios, node, nodes)

    return {
        "name": node.name,
        "skill_dir": node.skill_dir,
        "skill_md": skill_md if os.path.isfile(skill_md) else None,
        "frontmatter_raw": frontmatter_raw,
        "frontmatter": frontmatter,
        "body_raw": body_raw,
        "representations": [
            {
                "type": r.rep_type,
                "path": r.path,
                "exists": r.exists,
                "line_count": r.line_count,
                "size_bytes": r.size_bytes,
            }
            for r in node.representations
        ],
        "behavior": {
            "has_code": node.behavior.has_code,
            "primary_language": node.behavior.primary_language,
            "code_block_count": node.behavior.code_block_count,
            "trit": node.behavior.trit,
            "execution_path_length": node.behavior.execution_path_length,
        },
        "citations": {
            "cites": node.cites,
            "cited_by": node.cited_by,
        },
        "scenarios": scenarios,
    }


def _json_default(value: Any) -> Any:
    if isinstance(value, (datetime.date, datetime.datetime)):
        return value.isoformat()
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return str(value)


def write_jsonl(records: Iterable[Dict[str, Any]], path: str) -> None:
    with open(path, "w", encoding="utf-8") as f:
        for record in records:
            f.write(json.dumps(record, ensure_ascii=True, default=_json_default) + "\n")



def main() -> int:
    if not os.path.isdir(SKILLS_DIR):
        raise SystemExit(f"Missing skills dir: {SKILLS_DIR}")

    trit_map = load_trit_assignments(TRIT_ASSIGNMENTS_PATH)
    nodes = build_graph(SKILLS_DIR, trit_map)

    records = [build_record(node, nodes) for node in nodes.values()]
    write_jsonl(records, OUTPUT_PATH)

    print(f"Wrote {len(records)} beehavior records to {OUTPUT_PATH}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
