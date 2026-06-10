#!/usr/bin/env python3
"""
Unified "## Related" section for every skill.

Replaces the separate bidirectional-neighbors and backlinks blocks with ONE
symmetric Related block. Each entry names a related skill and describes the
NATURE of the relation from both sides:

  - relation direction, computed from prose citations:
      mutual / builds-on (outbound) / invoked-by (inbound) / shared-neighborhood
  - cluster context, where the pair co-belongs to a hub cluster whose domain is
    characterized from exa + our own use (see CLUSTER_DOMAINS)
  - the other skill's own one-line purpose (our own use), so the reader learns
    what the related thing is

The relation is symmetric by construction (the related SET is the undirected
closure of the guarded prose graph), and the per-edge wording is complementary
on each side: A's page says "builds on B", B's page says "invoked by A".

Prose graph = SKILL.md + hand-authored NEIGHBOR_SKILLS.md, excluding the
generated CONCOMITANT blocks (so the related set is stable / idempotent).
"""
from __future__ import annotations

import argparse
import fnmatch
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import enforce_skill_invariants as inv  # noqa: E402

BEGIN = "<!-- BEGIN GENERATED related (scripts/relate_skills.py) -->"
END = "<!-- END GENERATED related -->"
# Legacy managed blocks this generator supersedes.
LEGACY = [
    ("<!-- BEGIN GENERATED bidirectional-neighbors (scripts/symmetrize_neighbors.py) -->",
     "<!-- END GENERATED bidirectional-neighbors -->"),
    ("<!-- BEGIN GENERATED backlinks (scripts/populate_backlinks.py) -->",
     "<!-- END GENERATED backlinks -->"),
]

# Cluster domains: characterization gleaned from exa (web-grounded) fused with
# our own corpus usage. Keyed by hub skill name.
CLUSTER_DOMAINS = {
    "acsets": "attributed C-sets — category-theoretic relational data (AlgebraicJulia)",
    "interaction-nets": "Lafont interaction-net graph rewriting / optimal lambda-reduction",
    "goblins": "Spritely distributed object-capability programming (CapTP / OCapN)",
    "open-games": "compositional game theory via parametrised optics (play/coplay)",
    "para-mensch-commons": "categorical cybernetics — parametrised optics & bidirectional learners",
    "topos-unified": "topos theory, sheaves & categorical logic",
    "narya-proofs": "proof assistants & formal verification (Narya / Lean / Juvix)",
    "dynamic-sufficiency": "intent & sufficiency propagation (SPI)",
    "security": "security auditing, fuzzing & pentest",
    "repl-commons": "interactive REPLs & Lisp tooling",
    "python-scientific-commons": "scientific Python — bio/cheminformatics",
    "alife-commons": "artificial life, autopoiesis & chemical organization",
    "flox": "reproducible environments & deployment",
    "emacs": "Emacs / elisp tooling",
    "babashka": "Clojure / babashka scripting",
    "zig-programming": "Zig systems programming",
    "gay-mcp": "GF(3) deterministic color generation",
    "agent-o-rama": "multi-agent orchestration",
    "skill-dispatch": "skill routing & dispatch",
    "triadic-skill-orchestrator": "triadic GF(3) skill loading",
    "world-hopping": "world:// navigation",
    "acp-commons": "agent & capability protocols (CapTP / OCapN)",
}

FM_DESC_RE = re.compile(r"^description:\s*(.+?)\s*$", re.MULTILINE)


def neutralize(s: str) -> str:
    """Remove all reference-extraction triggers (backtick / slash / arrow /
    hyphenated-token) from free text, so the human-readable relation wording and
    descriptions never introduce graph edges. Only the explicitly backticked
    related name in each entry carries an edge -> the graph stays exactly the
    symmetric related set."""
    s = s.replace("`", "").replace("->", " ").replace("→", " ").replace("/", " ")
    s = re.sub(r"(?<=\w)-(?=\w)", " ", s)
    return re.sub(r"\s+", " ", s).strip()


def first_clause(desc: str, n: int = 90) -> str:
    desc = desc.strip().strip('"').strip("'")
    desc = re.split(r"(?<=[.;])\s", desc, maxsplit=1)[0]
    desc = re.sub(r"\s+", " ", desc)
    return desc[: n - 1] + "…" if len(desc) > n else desc


def load_descriptions(skills: dict) -> dict[str, str]:
    out: dict[str, str] = {}
    for name, meta in skills.items():
        md = meta["path"] / "SKILL.md"
        if not md.exists():
            continue
        try:
            head = md.read_text(encoding="utf-8", errors="ignore")[:2000]
        except OSError:
            continue
        m = FM_DESC_RE.search(head)
        out[name] = first_clause(m.group(1)) if m else ""
    return out


def prose_out_edges(skills: dict, known: set[str]) -> dict[str, set[str]]:
    """Directed edges from SKILL.md + hand-authored NEIGHBOR_SKILLS.md only."""
    out: dict[str, set[str]] = {n: set() for n in skills}
    for name, meta in skills.items():
        if inv._is_noise_ref(name):
            continue
        text = ""
        for fn in ("SKILL.md", "NEIGHBOR_SKILLS.md"):
            p = meta["path"] / fn
            if p.exists():
                try:
                    text += "\n" + p.read_text(encoding="utf-8", errors="ignore")
                except OSError:
                    pass
        refs = inv.extract_references(text, known)
        refs.discard(name)
        out[name] |= refs
    return out


def cluster_map(config: dict, known: set[str]) -> dict[str, set[str]]:
    """skill -> set of hub clusters it belongs to (pattern_edges + seed_edges)."""
    membership: dict[str, set[str]] = {n: set() for n in known}
    for hub, patterns in config.get("pattern_edges", {}).items():
        for pat in patterns:
            for cand in known:
                if cand != hub and fnmatch.fnmatch(cand, pat):
                    membership[cand].add(hub)
    for hub, dests in config.get("seed_edges", {}).items():
        for d in dests:
            if d in membership:
                membership[d].add(hub)
    for hub in config.get("hubs", []):
        if hub in membership:
            membership[hub].add(hub)
    return membership


def relation(a: str, b: str, out: dict[str, set[str]],
             clusters: dict[str, set[str]]) -> str:
    shared = clusters.get(a, set()) & clusters.get(b, set())
    if shared:
        hub = sorted(shared, key=lambda h: (h not in CLUSTER_DOMAINS, h))[0]
        dom = CLUSTER_DOMAINS.get(hub, hub)
        return f"sibling in the {dom} cluster"
    a2b = b in out.get(a, set())
    b2a = a in out.get(b, set())
    if a2b and b2a:
        return "mutually referenced"
    if a2b:
        return "builds on"
    if b2a:
        return "invoked by"
    return "related via shared neighborhood"


def render_block(name: str, entries: list[tuple[str, str, str]]) -> str:
    lines = [
        BEGIN,
        "",
        "## Related",
        "",
        "Skills related to this one, with the nature of each relation "
        "(direction from prose citations; cluster domains characterized from exa "
        "and our own use). Symmetric — each related skill lists this one too. "
        "Do not edit inside the markers; regenerate with "
        "`python3 scripts/relate_skills.py`.",
        "",
    ]
    for other, rel, desc in entries:
        rel = neutralize(rel)
        desc = neutralize(desc)
        tail = f" — {desc}" if desc else ""
        lines.append(f"- `{other}` — {rel}{tail}")
    lines += ["", END]
    return "\n".join(lines)


def strip_block(text: str, begin: str, end: str) -> str:
    while begin in text and end in text and text.index(begin) < text.index(end):
        pre = text[: text.index(begin)]
        post = text[text.index(end) + len(end):]
        text = pre.rstrip() + "\n\n" + post.lstrip()
    return text


def upsert(path: Path, block: str) -> str:
    if path.exists():
        text = path.read_text(encoding="utf-8", errors="ignore")
        for b, e in LEGACY:
            text = strip_block(text, b, e)
        text = strip_block(text, BEGIN, END)
        new = (text.rstrip() + "\n\n" + block + "\n") if text.strip() else block + "\n"
        action = "updated"
    else:
        new = block + "\n"
        action = "created"
    path.write_text(new, encoding="utf-8")
    return action


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--skills-dir", type=Path, default=Path("skills"))
    ap.add_argument("--config", type=Path, default=Path("invariants/skill_invariants_config.json"))
    ap.add_argument("--loadable-manifest", type=Path, default=None)
    ap.add_argument("--apply", action="store_true")
    args = ap.parse_args()

    config = inv._load_json(args.config)
    load = inv._load_loadable_manifest(args.loadable_manifest)
    skills = inv.discover_skills(args.skills_dir, loadable_names=load)
    known = set(skills.keys())
    desc = load_descriptions(skills)
    out = prose_out_edges(skills, known)
    clusters = cluster_map(config, known)

    # Undirected closure of the prose graph = the related set.
    related: dict[str, set[str]] = {n: set() for n in skills}
    for s, ds in out.items():
        for d in ds:
            related[s].add(d)
            related[d].add(s)

    total = sum(len(v) for v in related.values())
    actions = {"created": 0, "updated": 0}
    failed: list[str] = []
    if args.apply:
        for name, meta in skills.items():
            entries = [(b, relation(name, b, out, clusters), desc.get(b, ""))
                       for b in sorted(related[name])]
            path = meta["path"] / "CONCOMITANT_SKILLS.md"
            try:
                actions[upsert(path, render_block(name, entries))] += 1
            except OSError as err:
                failed.append(f"{name} ({err.strerror})")

    rel_types = {}
    for s in skills:
        for b in related[s]:
            rel_types[relation(s, b, out, clusters)] = rel_types.get(relation(s, b, out, clusters), 0) + 1
    print(f"skills: {len(skills)}  related edges (directed, symmetric): {total}")
    print(f"relation-type histogram: {dict(sorted(rel_types.items(), key=lambda kv: -kv[1]))}")
    print(f"blocks {'written' if args.apply else 'would write'}: {sum(actions.values())} ({actions})")
    if failed:
        print(f"WARN: {len(failed)} not writable, skipped")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
