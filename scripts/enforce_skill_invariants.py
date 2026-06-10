#!/usr/bin/env python3
"""
Enforce ASI skill invariants.

Invariants:
1. Skill count is non-decreasing unless explicit human oversight is present.
2. Reachability cost is non-increasing, and strictly decreases when skill count
   grows, unless explicit human oversight is present.

Reachability cost is computed from the skill graph induced by:
- Explicit references in SKILL.md / NEIGHBOR_SKILLS.md / CONCOMITANT_SKILLS.md
- Configured seed edges
- Configured pattern-based edges (glob expansion)
"""

from __future__ import annotations

import argparse
import fnmatch
import hashlib
import json
import os
import re
import subprocess
import sys
from collections import deque
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


DEFAULT_CONFIG_PATH = Path("invariants/skill_invariants_config.json")
DEFAULT_STATE_PATH = Path("invariants/skill_invariants_state.json")
DEFAULT_SKILLS_DIR = Path("skills")


BACKTICK_RE = re.compile(r"`([^`]+)`")
SLASH_RE = re.compile(r"/([a-z0-9][a-z0-9-]{0,80})")
ARROW_RE = re.compile(r"(?:->|→)\s*([a-z0-9][a-z0-9-]{0,80})")
HYPHENATED_RE = re.compile(r"(?<![a-z0-9-])([a-z0-9]+(?:-[a-z0-9]+)+)(?![a-z0-9-])")
WORD_RE = re.compile(r"[a-z0-9][a-z0-9-]{0,80}")


@dataclass
class InvariantEvaluation:
    violations: list[str]
    warnings: list[str]

    @property
    def ok(self) -> bool:
        return len(self.violations) == 0


def _load_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def _dump_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        json.dump(payload, handle, indent=2, sort_keys=True)
        handle.write("\n")


def _tracked_skill_names(skills_dir: Path) -> set[str] | None:
    """
    Return tracked skill directory names from git, or None if unavailable.
    """
    repo_root = skills_dir.parent
    try:
        result = subprocess.run(
            ["git", "-C", str(repo_root), "ls-files", "-z", str(skills_dir.name)],
            capture_output=True,
            text=False,
            check=False,
        )
    except OSError:
        return None

    if result.returncode != 0:
        return None

    tracked: set[str] = set()
    for raw in result.stdout.split(b"\x00"):
        if not raw:
            continue
        rel = raw.decode("utf-8", errors="ignore")
        parts = Path(rel).parts
        if len(parts) >= 2 and parts[0] == skills_dir.name:
            tracked.add(parts[1])
    return tracked


def _load_loadable_manifest(path: Path | None) -> set[str] | None:
    """
    Load the set of loadable skill directory names emitted by
    scripts/skillmd_lint.bb --manifest=PATH. This makes loadability (the codex-rs
    SKILL.md acceptance rules) the single source of truth for "what is a skill":
    a directory whose SKILL.md cannot load in codex/claude/agy is not counted as
    a skill, so the reachability graph and monotone invariants are computed over
    exactly the skills the agent runtimes can actually see. Returns None if no
    manifest is provided (fail-open: fall back to existence-based discovery).
    """
    if path is None:
        return None
    try:
        payload = _load_json(path)
    except (OSError, json.JSONDecodeError):
        print(
            f"WARN: could not read loadable manifest {path}; "
            "falling back to existence-based discovery.",
            file=sys.stderr,
        )
        return None
    loadable = payload.get("loadable")
    if not isinstance(loadable, list):
        print(
            f"WARN: loadable manifest {path} has no `loadable` list; "
            "falling back to existence-based discovery.",
            file=sys.stderr,
        )
        return None
    return {str(name) for name in loadable}


def discover_skills(
    skills_dir: Path,
    include_untracked: bool = False,
    loadable_names: set[str] | None = None,
) -> dict[str, dict[str, Any]]:
    skills: dict[str, dict[str, Any]] = {}
    tracked_names = None if include_untracked else _tracked_skill_names(skills_dir)
    for entry in sorted(skills_dir.iterdir()):
        if not entry.is_dir() or entry.name.startswith("."):
            continue
        if tracked_names is not None and entry.name not in tracked_names:
            continue
        # Loadability is the single oracle for membership: a skill the runtimes
        # cannot load is not a skill. The hard SKILL.md lint job fails CI before
        # this runs, so in steady state loadable_names covers every skill and
        # this filter is a no-op; it only excludes anything when frontmatter is
        # already broken (and that case has already failed the gate).
        if loadable_names is not None and entry.name not in loadable_names:
            continue
        files: list[Path] = []
        skill_md = entry / "SKILL.md"
        if skill_md.exists():
            files.append(skill_md)
        for extra in ("NEIGHBOR_SKILLS.md", "CONCOMITANT_SKILLS.md"):
            extra_path = entry / extra
            if extra_path.exists():
                files.append(extra_path)
        skills[entry.name] = {
            "path": entry,
            "has_skill_md": skill_md.exists(),
            "files": files,
        }
    return skills


def extract_references(text: str, known_skills: set[str]) -> set[str]:
    refs: set[str] = set()
    lowered = text.lower()

    for snippet in BACKTICK_RE.findall(lowered):
        for token in WORD_RE.findall(snippet):
            if token in known_skills:
                refs.add(token)

    for token in SLASH_RE.findall(lowered):
        if token in known_skills:
            refs.add(token)

    for token in ARROW_RE.findall(lowered):
        if token in known_skills:
            refs.add(token)

    for token in HYPHENATED_RE.findall(lowered):
        if token in known_skills:
            refs.add(token)

    return refs


def _resolve_pattern_edges(
    pattern_edges: dict[str, list[str]],
    known_skills: set[str],
) -> dict[str, set[str]]:
    resolved: dict[str, set[str]] = {}
    for source, patterns in pattern_edges.items():
        if source not in known_skills:
            continue
        for pattern in patterns:
            for candidate in known_skills:
                if candidate == source:
                    continue
                if fnmatch.fnmatch(candidate, pattern):
                    resolved.setdefault(source, set()).add(candidate)
    return resolved


def build_graph(skills: dict[str, dict[str, Any]], config: dict[str, Any]) -> dict[str, set[str]]:
    known_skills = set(skills.keys())
    graph: dict[str, set[str]] = {name: set() for name in known_skills}

    for source, meta in skills.items():
        for file_path in meta["files"]:
            try:
                content = file_path.read_text(encoding="utf-8", errors="ignore")
            except OSError:
                continue
            refs = extract_references(content, known_skills)
            refs.discard(source)
            graph[source].update(refs)

    seed_edges: dict[str, list[str]] = config.get("seed_edges", {})
    for source, destinations in seed_edges.items():
        if source not in known_skills:
            continue
        for destination in destinations:
            if destination in known_skills and destination != source:
                graph[source].add(destination)

    pattern_edges: dict[str, list[str]] = config.get("pattern_edges", {})
    resolved_pattern_edges = _resolve_pattern_edges(pattern_edges, known_skills)
    for source, destinations in resolved_pattern_edges.items():
        graph[source].update(destinations)

    return graph


def compute_reachability(
    graph: dict[str, set[str]],
    hubs: list[str],
) -> dict[str, int]:
    dist: dict[str, int] = {}
    queue: deque[str] = deque()

    for hub in hubs:
        if hub in graph and hub not in dist:
            dist[hub] = 0
            queue.append(hub)

    while queue:
        node = queue.popleft()
        for nxt in graph[node]:
            if nxt not in dist:
                dist[nxt] = dist[node] + 1
                queue.append(nxt)

    return dist


def percentile(values: list[int], pct: float) -> float:
    if not values:
        return 0.0
    if pct <= 0:
        return float(min(values))
    if pct >= 100:
        return float(max(values))
    ordered = sorted(values)
    rank = (len(ordered) - 1) * (pct / 100.0)
    low = int(rank)
    high = min(low + 1, len(ordered) - 1)
    if low == high:
        return float(ordered[low])
    weight = rank - low
    return (1.0 - weight) * ordered[low] + weight * ordered[high]


def compute_metrics(
    skills: dict[str, dict[str, Any]],
    graph: dict[str, set[str]],
    hubs: list[str],
) -> dict[str, Any]:
    total_dirs = len(skills)
    total_with_skill_md = sum(1 for meta in skills.values() if meta["has_skill_md"])
    total_edges = sum(len(edges) for edges in graph.values())
    dist = compute_reachability(graph, hubs)
    reachable = len(dist)
    unreachable = total_dirs - reachable

    reachable_distances = [d for d in dist.values() if d > 0]
    mean_hops = (
        sum(reachable_distances) / len(reachable_distances)
        if reachable_distances
        else 0.0
    )
    p95_hops = percentile(reachable_distances, 95.0)
    coverage = (reachable / total_dirs) if total_dirs else 0.0

    # Integer-valued optimization objective for policy checks.
    # Heavily penalize unreachable nodes, then long average paths.
    reachability_cost = int(unreachable * 1000 + round(mean_hops * 100) + round(p95_hops * 10))

    return {
        "skill_dirs": total_dirs,
        "skills_with_skill_md": total_with_skill_md,
        "graph_nodes": len(graph),
        "graph_edges": total_edges,
        "hubs_present": [hub for hub in hubs if hub in skills],
        "reachable": reachable,
        "unreachable": unreachable,
        "coverage": round(coverage, 6),
        "mean_hops": round(mean_hops, 6),
        "p95_hops": round(p95_hops, 6),
        "reachability_cost": reachability_cost,
    }


def _truthy(value: str | None) -> bool:
    if value is None:
        return False
    return value.strip().lower() in {"1", "true", "yes", "y", "on"}


def _parse_iso_datetime(value: str | None) -> datetime | None:
    if not value:
        return None
    try:
        parsed = datetime.fromisoformat(value)
    except ValueError:
        return None
    if parsed.tzinfo is None:
        return parsed.replace(tzinfo=timezone.utc)
    return parsed.astimezone(timezone.utc)


def evaluate_invariants(
    current: dict[str, Any],
    previous: dict[str, Any] | None,
    metrics_changed: bool,
    strict_cost_decrease_on_skill_growth: bool,
    max_seconds_between_snapshots: int | None,
    current_generated_at: datetime,
    previous_generated_at: str | None,
    human_oversight: bool,
    oversight_note: str | None,
) -> InvariantEvaluation:
    violations: list[str] = []
    warnings: list[str] = []

    if human_oversight and not oversight_note:
        violations.append("Human oversight enabled but no oversight note was provided.")

    if previous is None:
        warnings.append("No previous state file found; running in bootstrap mode.")
        return InvariantEvaluation(violations=violations, warnings=warnings)

    prev_metrics = previous.get("metrics", {})
    prev_count = int(prev_metrics.get("skill_dirs", 0))
    prev_cost = int(prev_metrics.get("reachability_cost", 0))

    curr_count = int(current.get("skill_dirs", 0))
    curr_cost = int(current.get("reachability_cost", 0))

    if curr_count < prev_count:
        violations.append(
            f"Skill count decreased: {curr_count} < {prev_count}. "
            "This requires human oversight."
        )

    if curr_count > prev_count and strict_cost_decrease_on_skill_growth:
        if curr_cost >= prev_cost:
            violations.append(
                f"Reachability cost did not strictly decrease while skill count grew: "
                f"{curr_cost} >= {prev_cost}."
            )
    else:
        if curr_cost > prev_cost:
            violations.append(
                f"Reachability cost increased: {curr_cost} > {prev_cost}."
            )

    if curr_count > prev_count and curr_cost < prev_cost:
        warnings.append(
            f"Skill count grew ({prev_count} -> {curr_count}) and reachability cost improved "
            f"({prev_cost} -> {curr_cost})."
        )

    if max_seconds_between_snapshots is not None and metrics_changed:
        if max_seconds_between_snapshots < 0:
            warnings.append(
                "Negative max_seconds_between_snapshots in policy; ignoring temporal density check."
            )
        elif not human_oversight:
            prev_dt = _parse_iso_datetime(previous_generated_at)
            if prev_dt is None:
                warnings.append(
                    "Could not parse previous generated_at timestamp; skipping temporal density check."
                )
            else:
                delta_seconds = int((current_generated_at - prev_dt).total_seconds())
                if delta_seconds < 0:
                    warnings.append(
                        "Current timestamp is earlier than previous snapshot timestamp; skipping temporal density check."
                    )
                elif delta_seconds > max_seconds_between_snapshots:
                    violations.append(
                        f"Time density violation: snapshot gap {delta_seconds}s exceeds "
                        f"limit {max_seconds_between_snapshots}s."
                    )

    if human_oversight:
        warnings.append("Human oversight waiver requested; invariant violations will be waived.")

    return InvariantEvaluation(violations=violations, warnings=warnings)


def config_digest(config: dict[str, Any]) -> str:
    payload = json.dumps(config, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _intent_witness(payload: dict[str, Any]) -> str:
    packed = json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return hashlib.sha256(packed).hexdigest()


def build_transition_intent(
    *,
    previous_state: dict[str, Any] | None,
    current_metrics: dict[str, Any],
    strict_cost_decrease_on_skill_growth: bool,
    max_seconds_between_snapshots: int | None,
    metrics_changed: bool,
    now_utc: datetime,
    human_oversight: bool,
    oversight_note: str | None,
    evaluation_ok_or_waived: bool,
) -> dict[str, Any]:
    prev_metrics = previous_state.get("metrics", {}) if previous_state else {}
    prev_count = int(prev_metrics.get("skill_dirs", 0))
    prev_cost = int(prev_metrics.get("reachability_cost", 0))
    curr_count = int(current_metrics.get("skill_dirs", 0))
    curr_cost = int(current_metrics.get("reachability_cost", 0))

    prev_generated_at = previous_state.get("generated_at") if previous_state else None
    prev_dt = _parse_iso_datetime(prev_generated_at)
    curr_tick = int(now_utc.timestamp())
    prev_tick = int(prev_dt.timestamp()) if prev_dt else None

    count_constraint_raw = curr_count >= prev_count if previous_state else True
    if previous_state:
        if curr_count > prev_count and strict_cost_decrease_on_skill_growth:
            cost_constraint_raw = curr_cost < prev_cost
        else:
            cost_constraint_raw = curr_cost <= prev_cost
    else:
        cost_constraint_raw = True

    if previous_state and max_seconds_between_snapshots is not None and metrics_changed and prev_tick is not None:
        delta_seconds = curr_tick - prev_tick
        time_constraint_raw = 0 <= delta_seconds <= max_seconds_between_snapshots
    else:
        delta_seconds = None
        time_constraint_raw = True

    intent_core = {
        "type": "ReachabilityInvariantIntent",
        "policy": {
            "strict_cost_decrease_on_skill_growth": strict_cost_decrease_on_skill_growth,
            "max_seconds_between_snapshots": max_seconds_between_snapshots,
        },
        "previous": (
            {
                "skill_count": prev_count,
                "reachability_cost": prev_cost,
                "generated_at": prev_generated_at,
                "tick": prev_tick,
            }
            if previous_state
            else None
        ),
        "next": {
            "skill_count": curr_count,
            "reachability_cost": curr_cost,
            "generated_at": now_utc.isoformat(),
            "tick": curr_tick,
        },
        "constraints": {
            "non_decreasing_skill_count_unless_oversight": (
                True if human_oversight else count_constraint_raw
            ),
            "steadily_decreasing_reachability_cost_unless_oversight": (
                True if human_oversight else cost_constraint_raw
            ),
            "locally_dense_time_unless_oversight": (
                True if human_oversight else time_constraint_raw
            ),
        },
        "timing": {
            "metrics_changed": metrics_changed,
            "delta_seconds": delta_seconds,
        },
        "oversight": {
            "enabled": human_oversight,
            "note": oversight_note,
        },
        "valid": evaluation_ok_or_waived,
    }
    intent_core["witness"] = _intent_witness(intent_core)
    return intent_core


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Enforce ASI skill invariants")
    parser.add_argument("--skills-dir", type=Path, default=DEFAULT_SKILLS_DIR)
    parser.add_argument("--config", type=Path, default=DEFAULT_CONFIG_PATH)
    parser.add_argument("--state", type=Path, default=DEFAULT_STATE_PATH)
    parser.add_argument(
        "--update-state",
        action="store_true",
        help="Write current metrics to the state file.",
    )
    parser.add_argument(
        "--human-oversight",
        action="store_true",
        help="Waive invariant violations with explicit human oversight note.",
    )
    parser.add_argument(
        "--oversight-note",
        type=str,
        default=None,
        help="Human oversight rationale (required if oversight is used).",
    )
    parser.add_argument(
        "--include-untracked",
        action="store_true",
        help="Include untracked local skill directories (default is tracked-only when git is available).",
    )
    parser.add_argument(
        "--loadable-manifest",
        type=Path,
        default=None,
        help=(
            "Path to the JSON manifest of loadable skills emitted by "
            "scripts/skillmd_lint.bb --manifest=PATH. When provided, only "
            "directories that load under the codex-rs SKILL.md rules are counted "
            "as skills (single oracle for membership). Fail-open if missing."
        ),
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit machine-readable JSON summary.",
    )
    parser.add_argument(
        "--emit-intent",
        type=Path,
        default=None,
        help="Emit Anoma/Juvix transition intent JSON to the provided path.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()

    if not args.skills_dir.exists():
        print(f"ERROR: skills directory does not exist: {args.skills_dir}", file=sys.stderr)
        return 2
    if not args.config.exists():
        print(f"ERROR: config file does not exist: {args.config}", file=sys.stderr)
        return 2

    config = _load_json(args.config)
    hubs = list(config.get("hubs", []))
    policy = config.get("policy", {})
    strict_cost_decrease = bool(policy.get("strict_cost_decrease_on_skill_growth", True))
    max_seconds_between_snapshots = policy.get("max_seconds_between_snapshots")
    if max_seconds_between_snapshots is not None:
        max_seconds_between_snapshots = int(max_seconds_between_snapshots)

    loadable_names = _load_loadable_manifest(args.loadable_manifest)
    skills = discover_skills(
        args.skills_dir,
        include_untracked=args.include_untracked,
        loadable_names=loadable_names,
    )
    graph = build_graph(skills, config)
    metrics = compute_metrics(skills, graph, hubs)

    previous_state = _load_json(args.state) if args.state.exists() else None
    previous_metrics = previous_state.get("metrics", {}) if previous_state else {}
    metrics_changed = bool(previous_state is not None and previous_metrics != metrics)
    now_utc = datetime.now(timezone.utc)

    env_oversight = _truthy(os.environ.get("ASI_HUMAN_OVERSIGHT"))
    human_oversight = args.human_oversight or env_oversight
    oversight_note = args.oversight_note or os.environ.get("ASI_HUMAN_OVERSIGHT_NOTE")

    evaluation = evaluate_invariants(
        current=metrics,
        previous=previous_state,
        metrics_changed=metrics_changed,
        strict_cost_decrease_on_skill_growth=strict_cost_decrease,
        max_seconds_between_snapshots=max_seconds_between_snapshots,
        current_generated_at=now_utc,
        previous_generated_at=previous_state.get("generated_at") if previous_state else None,
        human_oversight=human_oversight,
        oversight_note=oversight_note,
    )
    current_digest = config_digest(config)
    previous_digest = previous_state.get("config_digest") if previous_state else None
    if previous_digest and previous_digest != current_digest:
        evaluation.warnings.append(
            "Config digest changed since baseline; compare metrics with caution."
        )

    if args.json:
        summary = {
            "ok": evaluation.ok or human_oversight,
            "waived": bool(human_oversight and evaluation.violations),
            "config_digest": current_digest,
            "previous_config_digest": previous_digest,
            "metrics": metrics,
            "violations": evaluation.violations,
            "warnings": evaluation.warnings,
        }
        print(json.dumps(summary, indent=2, sort_keys=True))
    else:
        print("=== ASI Skill Invariant Check ===")
        print(f"Skill dirs:          {metrics['skill_dirs']}")
        print(f"Reachable from hubs: {metrics['reachable']} / {metrics['skill_dirs']}")
        print(f"Reachability cost:   {metrics['reachability_cost']}")
        print(f"Coverage:            {metrics['coverage']:.4f}")
        if previous_state is not None:
            prev = previous_state.get("metrics", {})
            print(f"Previous count/cost: {prev.get('skill_dirs', '?')} / {prev.get('reachability_cost', '?')}")
        else:
            print("Previous count/cost: <none>")
        if evaluation.warnings:
            for warning in evaluation.warnings:
                print(f"WARN: {warning}")
        if evaluation.violations:
            for violation in evaluation.violations:
                print(f"VIOLATION: {violation}")

    waived = bool(human_oversight and evaluation.violations)
    hard_fail = bool(evaluation.violations and not waived)

    if args.emit_intent is not None:
        intent = build_transition_intent(
            previous_state=previous_state,
            current_metrics=metrics,
            strict_cost_decrease_on_skill_growth=strict_cost_decrease,
            max_seconds_between_snapshots=max_seconds_between_snapshots,
            metrics_changed=metrics_changed,
            now_utc=now_utc,
            human_oversight=human_oversight,
            oversight_note=oversight_note,
            evaluation_ok_or_waived=(evaluation.ok or waived),
        )
        _dump_json(args.emit_intent, intent)
        if not args.json:
            print(f"Intent emitted: {args.emit_intent}")

    if args.update_state:
        state_payload = {
            "version": 1,
            "generated_at": datetime.now(timezone.utc).isoformat(),
            "config_digest": current_digest,
            "metrics": metrics,
            "policy": {
                "strict_cost_decrease_on_skill_growth": strict_cost_decrease,
                "max_seconds_between_snapshots": max_seconds_between_snapshots,
            },
            "oversight": {
                "enabled": human_oversight,
                "note": oversight_note,
            },
        }
        _dump_json(args.state, state_payload)
        if not args.json:
            print(f"State updated: {args.state}")

    return 1 if hard_fail else 0


if __name__ == "__main__":
    sys.exit(main())
