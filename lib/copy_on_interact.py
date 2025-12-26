#!/usr/bin/env python3
"""
Copy-on-Interact: Bidirectional sync between local state and GitHub repos.

Python implementation for integration with gh CLI and MCP servers.
"""
# /// script
# requires-python = ">=3.11"
# dependencies = ["rich", "httpx"]
# ///

from dataclasses import dataclass, field
from enum import Enum
from typing import Optional, Any
import re
import json
import subprocess
import time

class Trit(Enum):
    MINUS = -1
    ERGODIC = 0
    PLUS = 1

class InteractionType(Enum):
    FORK = "fork"
    PR = "pr"
    ISSUE = "issue"
    MENTION = "mention"
    STAR = "star"
    REVIEW = "review"
    THREAD_REF = "thread_ref"

INTERACTION_SEMANTICS = {
    InteractionType.FORK:    {"trit": Trit.MINUS, "hue": 270.0},
    InteractionType.PR:      {"trit": Trit.PLUS,  "hue": 60.0},
    InteractionType.ISSUE:   {"trit": Trit.ERGODIC, "hue": 180.0},
    InteractionType.MENTION: {"trit": Trit.ERGODIC, "hue": 200.0},
    InteractionType.STAR:    {"trit": Trit.PLUS,  "hue": 45.0},
    InteractionType.REVIEW:  {"trit": Trit.MINUS, "hue": 290.0},
    InteractionType.THREAD_REF: {"trit": Trit.ERGODIC, "hue": 180.0},
}

@dataclass
class OkLCH:
    L: float  # Lightness 0-1
    C: float  # Chroma 0-0.4
    h: float  # Hue 0-360
    
    def to_css(self) -> str:
        return f"oklch({self.L:.2f} {self.C:.2f} {self.h:.0f})"
    
    def to_dict(self) -> dict:
        return {"L": self.L, "C": self.C, "h": self.h}

@dataclass
class RemoteRef:
    url: str
    owner: str
    repo: str
    ref_type: str  # issue, pr, commit, repo
    number: Optional[int] = None
    fetched: bool = False
    last_sync: float = 0.0
    data: dict = field(default_factory=dict)

@dataclass
class Interaction:
    id: int
    url: str
    type: InteractionType
    trit: Trit
    color: OkLCH
    timestamp: float
    source_thread: Optional[str] = None
    target_thread: Optional[str] = None

class SplitMix64:
    def __init__(self, seed: int):
        self.state = seed & 0xFFFFFFFFFFFFFFFF
    
    def next(self) -> int:
        self.state = (self.state + 0x9E3779B97F4A7C15) & 0xFFFFFFFFFFFFFFFF
        z = self.state
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & 0xFFFFFFFFFFFFFFFF
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & 0xFFFFFFFFFFFFFFFF
        return z ^ (z >> 31)
    
    def color_at(self, index: int) -> OkLCH:
        temp = SplitMix64(self.state)
        for _ in range(index):
            temp.next()
        val = temp.next()
        
        hue = val % 360
        L = 0.50 + ((val >> 8) % 100) / 500.0
        C = 0.12 + ((val >> 16) % 100) / 500.0
        return OkLCH(L=L, C=C, h=float(hue))

class CopyOnInteractState:
    def __init__(self, seed: int = 0x42D):
        self.seed = seed
        self.rng = SplitMix64(seed)
        self.remote_refs: dict[str, RemoteRef] = {}
        self.interaction_log: list[Interaction] = []
        self.threads: dict[str, dict] = {}
        self.invocation_count = 0
    
    def on_interact(self, ref_url: str, interaction_type: InteractionType) -> Optional[Interaction]:
        """Triggered on any cross-boundary access."""
        parsed = self._parse_github_url(ref_url)
        if not parsed:
            return None
        
        # Check cache
        if ref_url in self.remote_refs:
            cached = self.remote_refs[ref_url]
            if cached.fetched and (time.time() - cached.last_sync) < 300:
                return self._materialize_cached(cached, interaction_type)
        
        # Fetch remote
        remote = self._fetch_github_ref(parsed)
        if remote:
            remote.fetched = True
            remote.last_sync = time.time()
            self.remote_refs[ref_url] = remote
        
        return self._log_interaction(ref_url, interaction_type)
    
    def _parse_github_url(self, url: str) -> Optional[dict]:
        patterns = [
            (r"github\.com/([^/]+)/([^/]+)/issues/(\d+)", "issue"),
            (r"github\.com/([^/]+)/([^/]+)/pull/(\d+)", "pr"),
            (r"github\.com/([^/]+)/([^/]+)/commit/([a-f0-9]+)", "commit"),
            (r"github\.com/([^/]+)/([^/]+)/?$", "repo"),
        ]
        
        for pattern, ref_type in patterns:
            m = re.search(pattern, url)
            if m:
                groups = m.groups()
                return {
                    "owner": groups[0],
                    "repo": groups[1],
                    "number": int(groups[2]) if len(groups) > 2 and groups[2].isdigit() else None,
                    "ref_type": ref_type,
                }
        return None
    
    def _fetch_github_ref(self, parsed: dict) -> Optional[RemoteRef]:
        """Fetch via gh CLI."""
        owner, repo = parsed["owner"], parsed["repo"]
        ref_type = parsed["ref_type"]
        number = parsed.get("number")
        
        if ref_type in ("issue", "pr") and number:
            endpoint = f"repos/{owner}/{repo}/issues/{number}"
        else:
            endpoint = f"repos/{owner}/{repo}"
        
        try:
            result = subprocess.run(
                ["gh", "api", endpoint],
                capture_output=True,
                text=True,
                timeout=10
            )
            if result.returncode == 0:
                data = json.loads(result.stdout)
                return RemoteRef(
                    url=f"https://github.com/{owner}/{repo}",
                    owner=owner,
                    repo=repo,
                    ref_type=ref_type,
                    number=number,
                    data=data
                )
        except Exception:
            pass
        
        return RemoteRef(
            url=f"https://github.com/{owner}/{repo}",
            owner=owner,
            repo=repo,
            ref_type=ref_type,
            number=number,
        )
    
    def _log_interaction(self, url: str, itype: InteractionType) -> Interaction:
        self.invocation_count += 1
        
        sem = INTERACTION_SEMANTICS.get(itype, {"trit": Trit.ERGODIC, "hue": 180.0})
        base_color = self.rng.color_at(self.invocation_count)
        
        # Override hue based on interaction type semantics
        color = OkLCH(L=base_color.L, C=base_color.C, h=sem["hue"])
        
        interaction = Interaction(
            id=self.invocation_count,
            url=url,
            type=itype,
            trit=sem["trit"],
            color=color,
            timestamp=time.time(),
        )
        
        self.interaction_log.append(interaction)
        return interaction
    
    def _materialize_cached(self, remote: RemoteRef, itype: InteractionType) -> Interaction:
        return self._log_interaction(remote.url, itype)
    
    def create_bidirectional_link(self, thread_a: str, thread_b: str) -> tuple[Interaction, Interaction]:
        """When thread A references thread B, create bidirectional links."""
        forward = self._log_interaction(
            f"thread:{thread_a}→{thread_b}",
            InteractionType.THREAD_REF
        )
        forward.source_thread = thread_a
        forward.target_thread = thread_b
        
        # Inverse link (for bidirectionality)
        backward = self._log_interaction(
            f"thread:{thread_b}←{thread_a}",
            InteractionType.THREAD_REF
        )
        backward.source_thread = thread_b
        backward.target_thread = thread_a
        
        return forward, backward
    
    def verify_gf3_conservation(self) -> bool:
        """Verify sum of trits ≡ 0 (mod 3)."""
        total = sum(i.trit.value for i in self.interaction_log)
        return total % 3 == 0
    
    def find_cobordisms(self) -> list[dict]:
        """Find shared boundaries between different repo communities."""
        repos = list({r.repo for r in self.remote_refs.values()})
        cobordisms = []
        
        for i, repo_a in enumerate(repos):
            for repo_b in repos[i+1:]:
                shared = [
                    interaction for interaction in self.interaction_log
                    if repo_a in interaction.url or repo_b in interaction.url
                ]
                if shared:
                    cobordisms.append({
                        "repos": (repo_a, repo_b),
                        "shared_count": len(shared),
                        "net_trit": sum(s.trit.value for s in shared) % 3 - 1,
                    })
        
        return sorted(cobordisms, key=lambda x: x["shared_count"], reverse=True)
    
    def summary(self) -> dict:
        by_type = {}
        for i in self.interaction_log:
            key = i.type.value
            by_type[key] = by_type.get(key, 0) + 1
        
        return {
            "total_interactions": len(self.interaction_log),
            "by_type": by_type,
            "gf3_sum": sum(i.trit.value for i in self.interaction_log),
            "gf3_conserved": self.verify_gf3_conservation(),
            "remote_refs_count": len(self.remote_refs),
            "cobordisms": len(self.find_cobordisms()),
            "seed": hex(self.seed),
        }
    
    def export_acset_json(self) -> dict:
        """Export as ACSet-compatible JSON."""
        return {
            "schema": {
                "objects": ["Thread", "RemoteRef", "Interaction"],
                "morphisms": {
                    "source": ["Interaction", "Thread"],
                    "target": ["Interaction", "Thread"],
                    "involves": ["Interaction", "RemoteRef"],
                },
            },
            "tables": {
                "Interaction": [
                    {
                        "id": i.id,
                        "url": i.url,
                        "type": i.type.value,
                        "trit": i.trit.value,
                        "color": i.color.to_css(),
                        "timestamp": i.timestamp,
                    }
                    for i in self.interaction_log
                ],
                "RemoteRef": [
                    {
                        "url": r.url,
                        "owner": r.owner,
                        "repo": r.repo,
                        "ref_type": r.ref_type,
                        "fetched": r.fetched,
                    }
                    for r in self.remote_refs.values()
                ],
            },
            "gf3_sum": sum(i.trit.value for i in self.interaction_log),
            "seed": hex(self.seed),
        }


def demo():
    """Demonstrate copy-on-interact with GitHub repos."""
    from rich.console import Console
    from rich.table import Table
    
    console = Console()
    state = CopyOnInteractState(seed=0x42D)
    
    # Simulate interactions with plurigrid ecosystem
    repos = [
        ("https://github.com/AlgebraicJulia/Catlab.jl", InteractionType.FORK),
        ("https://github.com/ToposInstitute/poly", InteractionType.STAR),
        ("https://github.com/bmorphism/Gay.jl", InteractionType.PR),
        ("https://github.com/AlgebraicJulia/ACSets.jl/issues/42", InteractionType.ISSUE),
        ("https://github.com/discopy/discopy/pull/123", InteractionType.REVIEW),
    ]
    
    console.print("[bold cyan]Copy-on-Interact Demo[/]")
    console.print(f"Seed: {hex(state.seed)}")
    
    table = Table(title="Interactions")
    table.add_column("ID", style="dim")
    table.add_column("Type", style="bold")
    table.add_column("Trit")
    table.add_column("Color")
    table.add_column("URL")
    
    for url, itype in repos:
        interaction = state.on_interact(url, itype)
        if interaction:
            trit_symbol = {-1: "⊖", 0: "○", 1: "⊕"}[interaction.trit.value]
            table.add_row(
                str(interaction.id),
                itype.value,
                trit_symbol,
                interaction.color.to_css(),
                url[:50] + "..." if len(url) > 50 else url,
            )
    
    console.print(table)
    
    # Create thread bidirectional links
    console.print("\n[bold cyan]Thread Links[/]")
    fwd, bwd = state.create_bidirectional_link("T-001", "T-002")
    console.print(f"  {fwd.url}")
    console.print(f"  {bwd.url}")
    
    # Summary
    console.print("\n[bold cyan]Summary[/]")
    summary = state.summary()
    console.print(f"  Total: {summary['total_interactions']}")
    console.print(f"  GF(3) sum: {summary['gf3_sum']}")
    console.print(f"  Conserved: {summary['gf3_conserved']}")
    
    # Export
    console.print("\n[bold cyan]ACSet Export[/]")
    export = state.export_acset_json()
    console.print(json.dumps(export, indent=2, default=str)[:500] + "...")


if __name__ == "__main__":
    demo()
