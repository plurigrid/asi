#!/usr/bin/env python3
"""
Noise-vs-genuine audit of inbound references for every skill.

The discriminator (established across /sdf, /acsets, /org): the harness extractor
splits backticked snippets on '.', so a token immediately preceded by '.' is a
TLD/file-extension fragment (arxiv.org -> org, foo.jl -> jl), NOT an intentional
reference. We replicate extract_references faithfully but record, per extracted
token, whether it was dot-preceded. Per target skill:

  inbound        = total token extractions naming it
  dot_artifact   = those preceded by '.'  (TLD/extension noise)
  genuine        = inbound - dot_artifact  (real prose references)
  noise_frac     = dot_artifact / inbound
  verdict        = NOISE (>0.5) / MIXED (0.2-0.5) / GENUINE (<0.2)

Outputs the fullest table for the top-interlinked skills and every skill they
reference, sorted by inbound degree.
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import enforce_skill_invariants as inv  # noqa: E402


def extract_with_dot(text: str, known: set[str]):
    """Yield (token, dot_preceded) for each extracted reference, faithful to
    enforce_skill_invariants.extract_references plus a dot-predecessor flag."""
    lc = text.lower()
    out = []
    for m in inv.BACKTICK_RE.finditer(lc):
        snip = m.group(1)
        for wm in inv.WORD_RE.finditer(snip):
            tok = wm.group(0)
            if tok in known and not inv._is_noise_ref(tok):
                dotp = wm.start() > 0 and snip[wm.start() - 1] == "."
                out.append((tok, dotp))
    for m in inv.SLASH_RE.finditer(lc):
        tok = m.group(1)
        if tok in known and not inv._is_noise_ref(tok):
            out.append((tok, False))
    for m in inv.ARROW_RE.finditer(lc):
        tok = m.group(1)
        if tok in known and not inv._is_noise_ref(tok):
            out.append((tok, False))
    for m in inv.HYPHENATED_RE.finditer(lc):
        tok = m.group(1)
        if tok in known and not inv._is_noise_ref(tok):
            dotp = m.start() > 0 and lc[m.start() - 1] == "."
            out.append((tok, dotp))
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--skills-dir", type=Path, default=Path("skills"))
    ap.add_argument("--loadable-manifest", type=Path, default=None)
    ap.add_argument("--top", type=int, default=20)
    args = ap.parse_args()

    load = inv._load_loadable_manifest(args.loadable_manifest)
    skills = inv.discover_skills(args.skills_dir, loadable_names=load)
    known = set(skills.keys())

    # Per-target tallies, and outbound (who references whom) from prose.
    inbound: dict[str, int] = {n: 0 for n in known}
    dot: dict[str, int] = {n: 0 for n in known}
    out_refs: dict[str, set[str]] = {n: set() for n in known}
    for src, meta in skills.items():
        if inv._is_noise_ref(src):
            continue
        md = meta["path"] / "SKILL.md"
        if not md.exists():
            continue
        try:
            text = md.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        for tok, dotp in extract_with_dot(text, known):
            if tok == src:
                continue
            inbound[tok] += 1
            if dotp:
                dot[tok] += 1
            out_refs[src].add(tok)

    def verdict(n: str) -> tuple[str, float]:
        ib = inbound[n]
        if ib == 0:
            return ("ISOLATED", 0.0)
        nf = dot[n] / ib
        v = "NOISE" if nf > 0.5 else ("MIXED" if nf >= 0.2 else "GENUINE")
        return (v, nf)

    # Top interlinked = highest inbound degree.
    top = sorted(known, key=lambda n: -inbound[n])[: args.top]
    # Union with everything the top skills reference.
    referenced = set().union(*(out_refs[t] for t in top)) if top else set()
    universe = sorted(set(top) | referenced, key=lambda n: -inbound[n])

    print(f"# corpus: {len(known)} skills")
    tot_ib = sum(inbound.values())
    tot_dot = sum(dot.values())
    print(f"# total inbound extractions: {tot_ib}  dot-artifact: {tot_dot} "
          f"({100*tot_dot/tot_ib:.1f}%)")
    vc = {}
    for n in known:
        vc[verdict(n)[0]] = vc.get(verdict(n)[0], 0) + 1
    print(f"# corpus verdicts: {vc}\n")

    print(f"## TOP {args.top} INTERLINKED — noise/genuine")
    print(f"{'skill':<34} {'in':>5} {'dot':>5} {'gen':>5} {'noise%':>7}  verdict  ref→")
    for n in top:
        v, nf = verdict(n)
        gen = inbound[n] - dot[n]
        print(f"{n:<34} {inbound[n]:>5} {dot[n]:>5} {gen:>5} {100*nf:>6.0f}%  {v:<8} {len(out_refs[n])}")

    print(f"\n## FULL TABLE — top {args.top} ∪ all they reference "
          f"({len(universe)} skills), by inbound degree")
    print(f"{'skill':<34} {'in':>5} {'dot':>5} {'gen':>5} {'noise%':>7}  verdict")
    for n in universe:
        v, nf = verdict(n)
        gen = inbound[n] - dot[n]
        print(f"{n:<34} {inbound[n]:>5} {dot[n]:>5} {gen:>5} {100*nf:>6.0f}%  {v}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
