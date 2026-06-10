#!/usr/bin/env python3
"""
Graph-level + content-level metrics for the ASI skill corpus.

GRAPH (organic-reference graph; hub seed/pattern edges excluded so we measure
real interconnection, not glob broadcast):
  - density, reciprocity
  - degree distribution (in/out/undirected): mean/median/max/Gini
  - weakly- and strongly-connected components (Tarjan)  <- SCC = cycles
  - graph CYCLOMATIC number (circuit rank) M = E - N + P   <- "graph as code"
  - average local clustering coefficient
  - k-core: max core number + distribution
  - PageRank (power iteration), top nodes

CONTENT (each SKILL.md treated as code):
  - McCabe cyclomatic complexity of embedded fenced code blocks
    M = 1 + #branch-tokens (if/elif/for/while/case/when/catch/except/&&/||/?/match/and/or)
  - markdown structural complexity (headings, max depth, list items, max nest,
    code fences, links, tables)
  - composite complexity score
Outputs JSON to stdout (--json) or human tables.
"""
from __future__ import annotations

import argparse
import json
import re
import statistics as st
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import enforce_skill_invariants as inv  # noqa: E402

BRANCH_RE = re.compile(
    r"\b(if|elif|else|for|while|case|when|catch|except|switch|match|and|or)\b"
    r"|&&|\|\||(?<![=!<>])\?(?!\?)|=>"
)
FENCE_RE = re.compile(r"^```(\w*)\s*$")
HEADING_RE = re.compile(r"^(#{1,6})\s")
LIST_RE = re.compile(r"^(\s*)[-*+]\s|^(\s*)\d+\.\s")
LINK_RE = re.compile(r"\[[^\]]+\]\([^)]+\)")
TABLE_RE = re.compile(r"^\s*\|.+\|\s*$")


def gini(xs: list[int]) -> float:
    if not xs:
        return 0.0
    s = sorted(xs)
    n = len(s)
    cum = sum((i + 1) * v for i, v in enumerate(s))
    tot = sum(s)
    if tot == 0:
        return 0.0
    return (2 * cum) / (n * tot) - (n + 1) / n


def tarjan_scc(adj: dict[str, set[str]]) -> list[list[str]]:
    index = {}
    low = {}
    onstack = set()
    stack: list[str] = []
    sccs: list[list[str]] = []
    counter = [0]

    def strong(v: str) -> None:
        # iterative Tarjan to avoid recursion limits on 1.5k nodes
        work = [(v, iter(adj.get(v, ())))]
        index[v] = low[v] = counter[0]
        counter[0] += 1
        stack.append(v)
        onstack.add(v)
        while work:
            node, it = work[-1]
            pushed = False
            for w in it:
                if w not in index:
                    index[w] = low[w] = counter[0]
                    counter[0] += 1
                    stack.append(w)
                    onstack.add(w)
                    work.append((w, iter(adj.get(w, ()))))
                    pushed = True
                    break
                elif w in onstack:
                    low[node] = min(low[node], index[w])
            if pushed:
                continue
            if low[node] == index[node]:
                comp = []
                while True:
                    x = stack.pop()
                    onstack.discard(x)
                    comp.append(x)
                    if x == node:
                        break
                sccs.append(comp)
            work.pop()
            if work:
                parent = work[-1][0]
                low[parent] = min(low[parent], low[node])

    for v in adj:
        if v not in index:
            strong(v)
    return sccs


def weakly_connected(un: dict[str, set[str]]) -> list[int]:
    seen = set()
    sizes = []
    for s in un:
        if s in seen:
            continue
        stack = [s]
        seen.add(s)
        sz = 0
        while stack:
            n = stack.pop()
            sz += 1
            for m in un[n]:
                if m not in seen:
                    seen.add(m)
                    stack.append(m)
        sizes.append(sz)
    return sorted(sizes, reverse=True)


def clustering(un: dict[str, set[str]], sample: int | None = None) -> float:
    nodes = list(un)
    coeffs = []
    for v in nodes:
        nb = un[v]
        k = len(nb)
        if k < 2:
            continue
        links = 0
        nbl = list(nb)
        for i in range(len(nbl)):
            for j in range(i + 1, len(nbl)):
                if nbl[j] in un[nbl[i]]:
                    links += 1
        coeffs.append(2 * links / (k * (k - 1)))
    return sum(coeffs) / len(coeffs) if coeffs else 0.0


def k_core(un: dict[str, set[str]]) -> dict[str, int]:
    deg = {n: len(un[n]) for n in un}
    core = dict(deg)
    order = sorted(un, key=lambda n: deg[n])
    processed = set()
    nbr = {n: set(un[n]) for n in un}
    import heapq
    heap = [(deg[n], n) for n in un]
    heapq.heapify(heap)
    cur = 0
    while heap:
        d, n = heapq.heappop(heap)
        if n in processed:
            continue
        if d < core[n]:
            continue
        cur = max(cur, d)
        core[n] = cur
        processed.add(n)
        for m in nbr[n]:
            if m not in processed and core[m] > cur:
                core[m] -= 1
                heapq.heappush(heap, (core[m], m))
    return core


def pagerank(out_adj: dict[str, set[str]], d: float = 0.85, iters: int = 60) -> dict[str, float]:
    nodes = list(out_adj)
    n = len(nodes)
    pr = {x: 1.0 / n for x in nodes}
    out_deg = {x: len(out_adj[x]) for x in nodes}
    in_edges: dict[str, list[str]] = {x: [] for x in nodes}
    for s, ds in out_adj.items():
        for t in ds:
            in_edges.setdefault(t, []).append(s)
    for _ in range(iters):
        dangling = sum(pr[x] for x in nodes if out_deg[x] == 0)
        nxt = {}
        for x in nodes:
            s = sum(pr[src] / out_deg[src] for src in in_edges.get(x, []) if out_deg[src])
            nxt[x] = (1 - d) / n + d * (s + dangling / n)
        pr = nxt
    return pr


def content_complexity(skill_md: Path) -> dict:
    try:
        text = skill_md.read_text(encoding="utf-8", errors="ignore")
    except OSError:
        return {}
    lines = text.splitlines()
    in_fence = False
    fence_lang = ""
    code_lines: list[str] = []
    fences = 0
    headings = 0
    max_head = 0
    list_items = 0
    max_nest = 0
    tables = 0
    for ln in lines:
        fm = FENCE_RE.match(ln.strip())
        if fm:
            if not in_fence:
                in_fence = True
                fence_lang = fm.group(1)
                fences += 1
            else:
                in_fence = False
            continue
        if in_fence:
            code_lines.append(ln)
            continue
        hm = HEADING_RE.match(ln)
        if hm:
            headings += 1
            max_head = max(max_head, len(hm.group(1)))
        lm = LIST_RE.match(ln)
        if lm:
            list_items += 1
            indent = len((lm.group(1) or lm.group(2)) or "")
            max_nest = max(max_nest, indent // 2 + 1)
        if TABLE_RE.match(ln):
            tables += 1
    code = "\n".join(code_lines)
    mccabe = 1 + len(BRANCH_RE.findall(code))
    links = len(LINK_RE.findall(text))
    composite = mccabe + headings + (list_items // 2) + tables * 2 + fences
    return {
        "mccabe": mccabe,
        "code_lines": len(code_lines),
        "fences": fences,
        "headings": headings,
        "max_head_depth": max_head,
        "list_items": list_items,
        "max_list_nest": max_nest,
        "tables": tables,
        "links": links,
        "doc_lines": len(lines),
        "composite": composite,
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--skills-dir", type=Path, default=Path("skills"))
    ap.add_argument("--loadable-manifest", type=Path, default=None)
    ap.add_argument("--top", type=int, default=20)
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--content-out", type=Path, default=None,
                    help="Write per-skill content metrics as JSON for downstream joins.")
    args = ap.parse_args()

    empty_cfg = {"hubs": [], "seed_edges": {}, "pattern_edges": {}}
    load = inv._load_loadable_manifest(args.loadable_manifest)
    skills = inv.discover_skills(args.skills_dir, loadable_names=load)
    g = inv.build_graph(skills, empty_cfg)

    un: dict[str, set[str]] = {n: set() for n in g}
    for s, ds in g.items():
        for t in ds:
            un[s].add(t)
            un[t].add(s)
    N = len(g)
    E = sum(len(v) for v in g.values())
    mutual = sum(1 for s, ds in g.items() for t in ds if s in g.get(t, ()))
    out_deg = [len(v) for v in g.values()]
    in_cnt: dict[str, int] = {n: 0 for n in g}
    for s, ds in g.items():
        for t in ds:
            in_cnt[t] += 1
    in_deg = list(in_cnt.values())
    un_deg = [len(v) for v in un.values()]

    sccs = tarjan_scc(g)
    nontrivial = [c for c in sccs if len(c) > 1]
    wcc = weakly_connected(un)
    cyclomatic = E - N + len(wcc)  # circuit rank of the dependency graph
    core = k_core(un)
    pr = pagerank(g)

    graph_metrics = {
        "nodes": N,
        "directed_edges": E,
        "density": round(E / (N * (N - 1)), 6) if N > 1 else 0.0,
        "reciprocity": round(mutual / E, 4) if E else 0.0,
        "graph_cyclomatic_number_E_minus_N_plus_P": cyclomatic,
        "weakly_connected_components": len(wcc),
        "largest_wcc": wcc[0] if wcc else 0,
        "strongly_connected_components": len(sccs),
        "nontrivial_sccs": len(nontrivial),
        "largest_scc": max((len(c) for c in sccs), default=0),
        "avg_clustering_coefficient": round(clustering(un), 4),
        "max_k_core": max(core.values()) if core else 0,
        "degree": {
            "out": {"mean": round(st.mean(out_deg), 2), "median": st.median(out_deg),
                    "max": max(out_deg), "gini": round(gini(out_deg), 4)},
            "in": {"mean": round(st.mean(in_deg), 2), "median": st.median(in_deg),
                   "max": max(in_deg), "gini": round(gini(in_deg), 4)},
            "undirected": {"mean": round(st.mean(un_deg), 2), "median": st.median(un_deg),
                           "max": max(un_deg), "gini": round(gini(un_deg), 4)},
        },
    }

    content = {name: content_complexity(meta["path"] / "SKILL.md")
               for name, meta in skills.items() if meta["has_skill_md"]}
    if args.content_out:
        args.content_out.write_text(json.dumps(content, sort_keys=True))

    def topk(d, key, k):
        return sorted(d.items(), key=lambda kv: -key(kv[1]))[:k]

    top_core = sorted(core.items(), key=lambda kv: -kv[1])[:args.top]
    top_pr = sorted(pr.items(), key=lambda kv: -kv[1])[:args.top]
    top_mccabe = topk(content, lambda v: v.get("mccabe", 0), args.top)
    top_composite = topk(content, lambda v: v.get("composite", 0), args.top)

    if args.json:
        print(json.dumps({
            "graph": graph_metrics,
            "top_k_core": top_core,
            "top_pagerank": [(n, round(p, 6)) for n, p in top_pr],
            "top_mccabe": [(n, v["mccabe"]) for n, v in top_mccabe],
            "top_composite": [(n, v["composite"]) for n, v in top_composite],
        }, indent=2))
        return 0

    print("=== GRAPH METRICS (organic reference graph) ===")
    print(json.dumps(graph_metrics, indent=2))
    print(f"\n=== top {args.top} k-core (densest mutual cores) ===")
    for n, c in top_core:
        print(f"  core={c:3d}  {n}")
    print(f"\n=== top {args.top} PageRank ===")
    for n, p in top_pr:
        print(f"  {p:.5f}  {n}")
    print(f"\n=== top {args.top} content McCabe (code in SKILL.md) ===")
    for n, v in top_mccabe:
        print(f"  M={v['mccabe']:4d}  code_lines={v['code_lines']:4d}  {n}")
    print(f"\n=== top {args.top} content composite complexity ===")
    for n, v in top_composite:
        print(f"  {v['composite']:4d}  {n}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
