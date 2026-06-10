#!/usr/bin/env python3
"""
Enforce bidirectionality of the skill reference graph.

Every intentional link A -> B must have a corresponding B -> A. We compute the
symmetric closure of the guarded reference graph (single-char names and the
REF_STOPWORDS already filtered by enforce_skill_invariants.extract_references)
and materialize, for each skill, its full undirected neighbor set into a managed
block in CONCOMITANT_SKILLS.md (which the invariant harness reads as references).

Because both A and B end up listing each other, the reference graph becomes
symmetric by construction -> reciprocity == 1.0. Idempotent: re-running on an
already-symmetric corpus rewrites the same managed blocks.

Hand-authored content outside the BEGIN/END markers is preserved.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import enforce_skill_invariants as inv  # noqa: E402

BEGIN = "<!-- BEGIN GENERATED bidirectional-neighbors (scripts/symmetrize_neighbors.py) -->"
END = "<!-- END GENERATED bidirectional-neighbors -->"


def render_block(name: str, neighbors: list[str]) -> str:
    lines = [
        BEGIN,
        "",
        "## Bidirectional Neighbors",
        "",
        "Auto-generated symmetric closure of the reference graph: every skill that "
        "links to this one is listed here so the link is reciprocated. Do not edit "
        "inside the markers; regenerate with `python3 scripts/symmetrize_neighbors.py`.",
        "",
    ]
    lines += [f"- `{n}`" for n in neighbors]
    lines += ["", END]
    return "\n".join(lines)


def upsert_block(path: Path, block: str) -> str:
    """Insert/replace the managed block, preserving other content. Returns action."""
    if path.exists():
        text = path.read_text(encoding="utf-8", errors="ignore")
        if BEGIN in text and END in text:
            pre = text[: text.index(BEGIN)]
            post = text[text.index(END) + len(END):]
            new = f"{pre.rstrip()}\n\n{block}\n{post.lstrip()}".rstrip() + "\n"
            action = "updated"
        else:
            new = text.rstrip() + "\n\n" + block + "\n"
            action = "appended"
    else:
        new = block + "\n"
        action = "created"
    path.write_text(new, encoding="utf-8")
    return action


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--skills-dir", type=Path, default=Path("skills"))
    ap.add_argument("--loadable-manifest", type=Path, default=None)
    ap.add_argument("--apply", action="store_true", help="Write CONCOMITANT_SKILLS.md files.")
    args = ap.parse_args()

    empty_cfg = {"hubs": [], "seed_edges": {}, "pattern_edges": {}}
    load = inv._load_loadable_manifest(args.loadable_manifest)
    skills = inv.discover_skills(args.skills_dir, loadable_names=load)
    g = inv.build_graph(skills, empty_cfg)  # guarded directed reference graph

    # Symmetric closure (undirected neighbor sets).
    un: dict[str, set[str]] = {n: set() for n in g}
    for s, ds in g.items():
        for t in ds:
            un[s].add(t)
            un[t].add(s)

    missing_back = sum(1 for s, ds in g.items() for t in ds if s not in g.get(t, set()))
    with_neighbors = {n: sorted(v) for n, v in un.items() if v}

    actions = {"created": 0, "updated": 0, "appended": 0}
    failed: list[str] = []
    if args.apply:
        for name, neighbors in with_neighbors.items():
            meta = skills.get(name)
            if meta is None:
                continue
            path = meta["path"] / "CONCOMITANT_SKILLS.md"
            try:
                actions[upsert_block(path, render_block(name, neighbors))] += 1
            except OSError as err:
                failed.append(f"{name} ({err.strerror})")

    print(f"skills: {len(g)}  directed edges: {sum(len(v) for v in g.values())}")
    print(f"asymmetric (missing back-edge) directed edges before: {missing_back}")
    print(f"skills with >=1 neighbor: {len(with_neighbors)}")
    print(f"managed concomitant files {'written' if args.apply else 'would write'}: "
          f"{sum(actions.values())} ({actions})")
    if failed:
        print(f"WARN: {len(failed)} skills not writable, back-refs skipped: {failed}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
