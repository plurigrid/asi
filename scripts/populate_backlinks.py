#!/usr/bin/env python3
"""
Populate backlinks: for each skill, the set of skills whose own SKILL.md prose
references it (genuine inbound citations, computed PROSE-ONLY so it is not just a
restatement of the symmetric-closure neighbor block).

Writes a managed "## Backlinks" block into CONCOMITANT_SKILLS.md, alongside (and
preserving) the bidirectional-neighbors block. Idempotent; hand-authored content
and the neighbors block are left intact.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import enforce_skill_invariants as inv  # noqa: E402

BEGIN = "<!-- BEGIN GENERATED backlinks (scripts/populate_backlinks.py) -->"
END = "<!-- END GENERATED backlinks -->"


def prose_out_edges(skills: dict, known: set[str]) -> dict[str, set[str]]:
    """Directed edges from each skill's SKILL.md prose only (guarded)."""
    out: dict[str, set[str]] = {n: set() for n in skills}
    for name, meta in skills.items():
        if inv._is_noise_ref(name):
            continue
        md = meta["path"] / "SKILL.md"
        if not md.exists():
            continue
        try:
            text = md.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        refs = inv.extract_references(text, known)
        refs.discard(name)
        out[name] |= refs
    return out


def render_block(backlinks: list[str]) -> str:
    lines = [
        BEGIN,
        "",
        "## Backlinks",
        "",
        "Skills whose SKILL.md prose references this one (inbound citations, "
        "auto-generated). Do not edit inside the markers; regenerate with "
        "`python3 scripts/populate_backlinks.py`.",
        "",
    ]
    if backlinks:
        lines += [f"- `{n}`" for n in backlinks]
    else:
        lines += ["_No inbound prose citations yet._"]
    lines += ["", END]
    return "\n".join(lines)


def upsert(path: Path, block: str) -> str:
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
    ap.add_argument("--apply", action="store_true")
    args = ap.parse_args()

    load = inv._load_loadable_manifest(args.loadable_manifest)
    skills = inv.discover_skills(args.skills_dir, loadable_names=load)
    known = set(skills.keys())
    out = prose_out_edges(skills, known)

    backlinks: dict[str, list[str]] = {n: [] for n in skills}
    for src, dsts in out.items():
        for d in dsts:
            backlinks.setdefault(d, []).append(src)
    backlinks = {n: sorted(v) for n, v in backlinks.items()}

    total_in = sum(len(v) for v in backlinks.values())
    with_bl = {n: v for n, v in backlinks.items() if v}

    actions = {"created": 0, "updated": 0, "appended": 0}
    failed: list[str] = []
    if args.apply:
        for name, meta in skills.items():
            path = meta["path"] / "CONCOMITANT_SKILLS.md"
            try:
                actions[upsert(path, render_block(backlinks.get(name, [])))] += 1
            except OSError as err:
                failed.append(f"{name} ({err.strerror})")

    print(f"skills: {len(skills)}  prose inbound citations: {total_in}")
    print(f"skills with >=1 backlink: {len(with_bl)}")
    print(f"blocks {'written' if args.apply else 'would write'}: {sum(actions.values())} ({actions})")
    if failed:
        print(f"WARN: {len(failed)} not writable, skipped: {failed}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
