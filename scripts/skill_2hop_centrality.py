#!/usr/bin/env python3
"""
2-hop interconnection of the skill graph.

Reuses enforce_skill_invariants.build_graph (the SAME graph CI scores) and counts,
for each skill, the number of DISTINCT other skills reachable within <=2 hops under
three lenses:

  out  : directed out-edges  -> how many skills this one can reach in 2 hops
  in   : directed in-edges   -> how many skills can reach this one in 2 hops
  undirected : edges as bidirectional -> genuine 2-hop neighborhood size

"Most interconnected" defaults to the undirected lens (broadcast hubs inflate the
directed-out number via pattern_edges; undirected measures mutual embedding).
"""
from __future__ import annotations

import argparse
import sys
from collections import deque
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import enforce_skill_invariants as inv  # noqa: E402


def two_hop_count(adj: dict[str, set[str]], src: str) -> int:
    seen = {src}
    frontier = deque([(src, 0)])
    while frontier:
        node, d = frontier.popleft()
        if d == 2:
            continue
        for nxt in adj.get(node, ()):  # noqa: SIM118
            if nxt not in seen:
                seen.add(nxt)
                frontier.append((nxt, d + 1))
    return len(seen) - 1  # exclude src itself


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--skills-dir", type=Path, default=Path("skills"))
    ap.add_argument("--config", type=Path, default=Path("invariants/skill_invariants_config.json"))
    ap.add_argument("--loadable-manifest", type=Path, default=None)
    ap.add_argument("--top", type=int, default=25)
    args = ap.parse_args()

    config = inv._load_json(args.config)
    loadable = inv._load_loadable_manifest(args.loadable_manifest)
    skills = inv.discover_skills(args.skills_dir, loadable_names=loadable)
    graph = inv.build_graph(skills, config)  # directed: source -> referenced

    # Build the three adjacency views.
    out_adj = graph
    in_adj: dict[str, set[str]] = {n: set() for n in graph}
    for s, dests in graph.items():
        for d in dests:
            in_adj.setdefault(d, set()).add(s)
    un_adj: dict[str, set[str]] = {n: set() for n in graph}
    for s, dests in graph.items():
        for d in dests:
            un_adj[s].add(d)
            un_adj.setdefault(d, set()).add(s)

    nodes = list(graph.keys())
    out2 = {n: two_hop_count(out_adj, n) for n in nodes}
    in2 = {n: two_hop_count(in_adj, n) for n in nodes}
    un2 = {n: two_hop_count(un_adj, n) for n in nodes}

    total = len(nodes)
    hubs = set(config.get("hubs", []))

    def top(metric: dict[str, int], k: int) -> list[tuple[str, int]]:
        return sorted(metric.items(), key=lambda kv: (-kv[1], kv[0]))[:k]

    print(f"graph: {total} nodes, {sum(len(v) for v in graph.values())} directed edges")
    print(f"hubs:  {len(hubs & set(nodes))} present\n")

    for label, metric in (("undirected", un2), ("out (reach)", out2), ("in (reached-by)", in2)):
        print(f"=== top {args.top} by 2-hop {label} ===")
        for name, c in top(metric, args.top):
            tag = " [hub]" if name in hubs else ""
            print(f"  {c:5d}  {name}{tag}")
        print()

    # Most interconnected excluding configured hubs (hubs win by construction).
    non_hub = {n: c for n, c in un2.items() if n not in hubs}
    print(f"=== top {args.top} by 2-hop undirected, EXCLUDING hubs ===")
    for name, c in top(non_hub, args.top):
        print(f"  {c:5d}  {name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
