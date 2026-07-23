#!/usr/bin/env python3
"""Classify same-name fork deltas against a true upstream.

This prevents treating a stale-fork sync gap as original contributor work.
Example:
  scripts/fork_delta_conservation.py \
    --repo mathlib4 \
    --upstream leanprover-community:master \
    --left monaduck1069:master \
    --right plurigrid:master
"""
from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from typing import Any


@dataclass(frozen=True)
class Ref:
    owner: str
    ref: str

    @classmethod
    def parse(cls, text: str) -> "Ref":
        if ":" not in text:
            raise argparse.ArgumentTypeError(f"expected OWNER:REF, got {text!r}")
        owner, ref = text.split(":", 1)
        if not owner or not ref:
            raise argparse.ArgumentTypeError(f"expected OWNER:REF, got {text!r}")
        return cls(owner, ref)

    def qualified(self) -> str:
        return f"{self.owner}:{self.ref}"


def _compare_path(owner: str, repo: str, base: str, head: str) -> str:
    # GitHub's compare endpoint accepts OWNER:BRANCH in the head segment.
    # Quote branch slashes but keep colon and the triple-dot separator readable.
    spec = urllib.parse.quote(f"{base}...{head}", safe=":.")
    return f"repos/{owner}/{repo}/compare/{spec}"


def gh_api(path: str) -> dict[str, Any]:
    out = subprocess.check_output(["gh", "api", path], text=True)
    return json.loads(out)


def http_api(path: str) -> dict[str, Any]:
    url = f"https://api.github.com/{path}"
    req = urllib.request.Request(url, headers={"User-Agent": "asi-fork-delta-conservation"})
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if token:
        req.add_header("Authorization", f"Bearer {token}")
    with urllib.request.urlopen(req, timeout=30) as response:
        return json.loads(response.read().decode("utf-8"))


def github_compare(owner: str, repo: str, base: str, head: str, *, prefer_gh: bool = True) -> dict[str, Any]:
    path = _compare_path(owner, repo, base, head)
    if prefer_gh and shutil.which("gh"):
        try:
            return gh_api(path)
        except (subprocess.CalledProcessError, FileNotFoundError, json.JSONDecodeError):
            # Fall through to direct HTTPS for unauthenticated or token-based use.
            pass
    try:
        return http_api(path)
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", errors="replace")
        raise RuntimeError(f"GitHub compare failed for {path}: HTTP {exc.code}: {detail}") from exc


def summarize_compare(data: dict[str, Any]) -> dict[str, Any]:
    return {
        "status": data.get("status"),
        "ahead_by": int(data.get("ahead_by", 0)),
        "behind_by": int(data.get("behind_by", 0)),
        "total_commits": int(data.get("total_commits", 0)),
        "merge_base_commit": (data.get("merge_base_commit") or {}).get("sha"),
    }


def classify_delta(left: dict[str, int], right: dict[str, int], pairwise: dict[str, int]) -> str:
    """Classify the observed left/right fork delta.

    Inputs are summaries of upstream...left, upstream...right, and right...left.
    If both forks are ancestors of upstream, any pairwise ahead/behind mass is
    upstream history already conserved in the upstream DAG, not original fork work.
    """
    left_ahead = int(left.get("ahead_by", 0))
    left_behind = int(left.get("behind_by", 0))
    right_ahead = int(right.get("ahead_by", 0))
    right_behind = int(right.get("behind_by", 0))
    pair_ahead = int(pairwise.get("ahead_by", 0))
    pair_behind = int(pairwise.get("behind_by", 0))

    if left_ahead == 0 and right_ahead == 0:
        if left_behind == right_behind and pair_ahead == 0 and pair_behind == 0:
            return "same-upstream-snapshot"
        return "upstream-sync-gap"

    if (left_ahead > 0 and left_behind > 0) or (right_ahead > 0 and right_behind > 0):
        return "mixed-upstream-and-original"

    if left_ahead > 0 or right_ahead > 0:
        return "original-work-present"

    return "unknown"


def recommendation(classification: str) -> str:
    if classification == "upstream-sync-gap":
        return "Do not treat the pairwise delta as contributor work; sync the stale fork or record it as upstream history already conserved elsewhere."
    if classification == "same-upstream-snapshot":
        return "No fork delta to conserve; both refs point at the same upstream snapshot."
    if classification == "original-work-present":
        return "Inspect fork-ahead commits, compute patch IDs, and run repo-specific tests before porting or PRing."
    if classification == "mixed-upstream-and-original":
        return "Separate upstream catch-up from fork-original commits before attributing or merging work."
    return "Insufficient evidence; inspect merge bases and commits manually."


def build_report(repo: str, upstream: Ref, left: Ref, right: Ref, *, prefer_gh: bool = True) -> dict[str, Any]:
    left_vs_up = summarize_compare(
        github_compare(upstream.owner, repo, upstream.ref, left.qualified(), prefer_gh=prefer_gh)
    )
    right_vs_up = summarize_compare(
        github_compare(upstream.owner, repo, upstream.ref, right.qualified(), prefer_gh=prefer_gh)
    )
    pairwise = summarize_compare(
        github_compare(right.owner, repo, right.ref, left.qualified(), prefer_gh=prefer_gh)
    )
    cls = classify_delta(left_vs_up, right_vs_up, pairwise)
    return {
        "repo": repo,
        "upstream": {"owner": upstream.owner, "ref": upstream.ref},
        "left": {"owner": left.owner, "ref": left.ref, "vs_upstream": left_vs_up},
        "right": {"owner": right.owner, "ref": right.ref, "vs_upstream": right_vs_up},
        "pairwise_right_to_left": pairwise,
        "classification": cls,
        "recommendation": recommendation(cls),
        "conservation_law": "fork delta is original only after subtracting upstream DAG mass",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, help="repository name shared by the fork network, e.g. mathlib4")
    parser.add_argument("--upstream", required=True, type=Ref.parse, help="true upstream OWNER:REF")
    parser.add_argument("--left", required=True, type=Ref.parse, help="left fork OWNER:REF, e.g. monaduck1069:master")
    parser.add_argument("--right", required=True, type=Ref.parse, help="right fork OWNER:REF, e.g. plurigrid:master")
    parser.add_argument("--no-gh", action="store_true", help="skip gh CLI and use direct GitHub HTTPS")
    args = parser.parse_args(argv)

    report = build_report(args.repo, args.upstream, args.left, args.right, prefer_gh=not args.no_gh)
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
