#!/usr/bin/env python3
"""
GH CLI Activity → ACSet JSON Export
ERGODIC (0) Agent | Seed: 0x42D | Trit: 0 (balance/coordination)

Transforms GitHub activity into colored ACSet format with gay-mcp deterministic colors.
"""

import json
import subprocess
import hashlib
from dataclasses import dataclass, field
from typing import Any

SEED = 0x42D

def splitmix64(seed: int) -> tuple[int, int]:
    """SplitMix64 deterministic RNG for gay-mcp colors."""
    seed = (seed + 0x9E3779B97F4A7C15) & 0xFFFFFFFFFFFFFFFF
    z = seed
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & 0xFFFFFFFFFFFFFFFF
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & 0xFFFFFFFFFFFFFFFF
    return seed, (z ^ (z >> 31)) & 0xFFFFFFFFFFFFFFFF

def seed_to_color(seed: int) -> str:
    """Generate deterministic hex color from seed."""
    _, val = splitmix64(seed)
    r = (val >> 16) & 0xFF
    g = (val >> 8) & 0xFF
    b = val & 0xFF
    return f"#{r:02x}{g:02x}{b:02x}"

def to_trit(val: int) -> int:
    """Map value to GF(3) trit: -1, 0, +1."""
    return (val % 3) - 1

def gf3_sum(trits: list[int]) -> int:
    """GF(3) sum must conserve to 0 for balance."""
    return sum(trits) % 3

@dataclass
class ACSetSchema:
    """ACSet schema for GitHub activity."""
    objects: list[str] = field(default_factory=lambda: ["Issue", "PR", "Commit", "User", "Repo"])
    morphisms: dict[str, tuple[str, str]] = field(default_factory=lambda: {
        "authored_by": ("Issue", "User"),
        "pr_authored_by": ("PR", "User"),
        "commit_authored_by": ("Commit", "User"),
        "on_repo": ("Issue", "Repo"),
        "pr_on_repo": ("PR", "Repo"),
        "commit_on_repo": ("Commit", "Repo"),
        "references": ("PR", "Issue"),
        "reviews": ("User", "PR"),
    })

@dataclass
class ColoredACSet:
    """Colored ACSet with gay-mcp deterministic coloring."""
    schema: ACSetSchema
    tables: dict[str, list[dict[str, Any]]]
    colors: dict[str, str]
    trits: dict[str, int]
    seed: int
    
    def to_json(self) -> dict:
        return {
            "schema": {
                "objects": self.schema.objects,
                "morphisms": {k: list(v) for k, v in self.schema.morphisms.items()}
            },
            "tables": self.tables,
            "colors": self.colors,
            "trits": self.trits,
            "gf3_sum": gf3_sum(list(self.trits.values())),
            "seed": hex(self.seed),
            "agent": "ERGODIC(0)"
        }

def run_gh_api(endpoint: str) -> list[dict]:
    """Run gh api command and return JSON."""
    try:
        result = subprocess.run(
            ["gh", "api", endpoint, "--paginate"],
            capture_output=True, text=True, timeout=30
        )
        if result.returncode == 0 and result.stdout.strip():
            data = json.loads(result.stdout)
            return data if isinstance(data, list) else [data]
    except (subprocess.TimeoutExpired, json.JSONDecodeError, FileNotFoundError):
        pass
    return []

def fetch_github_activity(user: str = "bmorphism", limit: int = 20) -> dict[str, list]:
    """Fetch recent GitHub activity via gh CLI."""
    activity = {"issues": [], "prs": [], "commits": [], "users": set(), "repos": set()}
    
    # Fetch recent issues
    issues = run_gh_api(f"/users/{user}/issues?state=all&per_page={limit}&sort=updated")
    for issue in issues[:limit]:
        activity["issues"].append({
            "id": issue.get("id"),
            "number": issue.get("number"),
            "title": issue.get("title", "")[:100],
            "state": issue.get("state"),
            "user": issue.get("user", {}).get("login"),
            "repo": issue.get("repository_url", "").split("/")[-1] if issue.get("repository_url") else None
        })
        if issue.get("user", {}).get("login"):
            activity["users"].add(issue["user"]["login"])
        if issue.get("repository_url"):
            activity["repos"].add(issue["repository_url"].split("/")[-1])
    
    # Fetch recent PRs
    prs = run_gh_api(f"/search/issues?q=author:{user}+type:pr&per_page={limit}")
    for pr in prs.get("items", [])[:limit] if isinstance(prs, dict) else prs[:limit]:
        activity["prs"].append({
            "id": pr.get("id"),
            "number": pr.get("number"),
            "title": pr.get("title", "")[:100],
            "state": pr.get("state"),
            "user": pr.get("user", {}).get("login"),
            "repo": pr.get("repository_url", "").split("/")[-1] if pr.get("repository_url") else None
        })
        if pr.get("user", {}).get("login"):
            activity["users"].add(pr["user"]["login"])
    
    # Fetch recent events for commits
    events = run_gh_api(f"/users/{user}/events?per_page={limit}")
    for event in events[:limit]:
        if event.get("type") == "PushEvent":
            for commit in event.get("payload", {}).get("commits", [])[:3]:
                activity["commits"].append({
                    "sha": commit.get("sha", "")[:7],
                    "message": commit.get("message", "")[:80],
                    "user": event.get("actor", {}).get("login"),
                    "repo": event.get("repo", {}).get("name", "").split("/")[-1]
                })
                if event.get("repo", {}).get("name"):
                    activity["repos"].add(event["repo"]["name"].split("/")[-1])
    
    activity["users"] = list(activity["users"])
    activity["repos"] = list(activity["repos"])
    return activity

def build_colored_acset(activity: dict, seed: int = SEED) -> ColoredACSet:
    """Build ColoredACSet from GitHub activity."""
    schema = ACSetSchema()
    tables = {obj: [] for obj in schema.objects}
    colors = {}
    trits = {}
    
    current_seed = seed
    
    # Populate User table
    for i, user in enumerate(activity.get("users", [])):
        uid = f"user_{i}"
        current_seed, _ = splitmix64(current_seed)
        colors[uid] = seed_to_color(current_seed)
        trits[uid] = to_trit(i)
        tables["User"].append({"id": uid, "login": user, "color": colors[uid], "trit": trits[uid]})
    
    # Populate Repo table
    for i, repo in enumerate(activity.get("repos", [])):
        rid = f"repo_{i}"
        current_seed, _ = splitmix64(current_seed)
        colors[rid] = seed_to_color(current_seed)
        trits[rid] = to_trit(i)
        tables["Repo"].append({"id": rid, "name": repo, "color": colors[rid], "trit": trits[rid]})
    
    # User/Repo lookup
    user_idx = {u: f"user_{i}" for i, u in enumerate(activity.get("users", []))}
    repo_idx = {r: f"repo_{i}" for i, r in enumerate(activity.get("repos", []))}
    
    # Populate Issue table with morphisms
    for i, issue in enumerate(activity.get("issues", [])):
        iid = f"issue_{i}"
        current_seed, _ = splitmix64(current_seed)
        colors[iid] = seed_to_color(current_seed)
        trits[iid] = to_trit(i)
        tables["Issue"].append({
            "id": iid,
            "number": issue.get("number"),
            "title": issue.get("title"),
            "state": issue.get("state"),
            "color": colors[iid],
            "trit": trits[iid],
            "authored_by": user_idx.get(issue.get("user")),
            "on_repo": repo_idx.get(issue.get("repo"))
        })
    
    # Populate PR table
    for i, pr in enumerate(activity.get("prs", [])):
        pid = f"pr_{i}"
        current_seed, _ = splitmix64(current_seed)
        colors[pid] = seed_to_color(current_seed)
        trits[pid] = to_trit(i)
        tables["PR"].append({
            "id": pid,
            "number": pr.get("number"),
            "title": pr.get("title"),
            "state": pr.get("state"),
            "color": colors[pid],
            "trit": trits[pid],
            "pr_authored_by": user_idx.get(pr.get("user")),
            "pr_on_repo": repo_idx.get(pr.get("repo"))
        })
    
    # Populate Commit table
    for i, commit in enumerate(activity.get("commits", [])):
        cid = f"commit_{i}"
        current_seed, _ = splitmix64(current_seed)
        colors[cid] = seed_to_color(current_seed)
        trits[cid] = to_trit(i)
        tables["Commit"].append({
            "id": cid,
            "sha": commit.get("sha"),
            "message": commit.get("message"),
            "color": colors[cid],
            "trit": trits[cid],
            "commit_authored_by": user_idx.get(commit.get("user")),
            "commit_on_repo": repo_idx.get(commit.get("repo"))
        })
    
    return ColoredACSet(schema=schema, tables=tables, colors=colors, trits=trits, seed=seed)

def export_acset(output_path: str = None, user: str = "bmorphism") -> dict:
    """Main export function."""
    activity = fetch_github_activity(user=user)
    acset = build_colored_acset(activity)
    result = acset.to_json()
    
    if output_path:
        with open(output_path, 'w') as f:
            json.dump(result, f, indent=2)
    
    return result

if __name__ == "__main__":
    import sys
    output = sys.argv[1] if len(sys.argv) > 1 else "/Users/bob/ies/plurigrid-asi-skillz/gh_acset_export.json"
    result = export_acset(output)
    print(f"Exported ACSet: {len(result['tables']['Issue'])} issues, {len(result['tables']['PR'])} PRs, {len(result['tables']['Commit'])} commits")
    print(f"GF(3) sum: {result['gf3_sum']} (0 = balanced)")
