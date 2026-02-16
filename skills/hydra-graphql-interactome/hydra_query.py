#!/usr/bin/env python3
"""
Hydra-GraphQL Interactome Query Engine

Multi-head GraphQL queries for security DAO network discovery
with degree-personalized author expansion and Move/Aptos bridging.
"""
# /// script
# requires-python = ">=3.11"
# dependencies = ["httpx", "rich"]
# ///

import os
import json
import hashlib
from dataclasses import dataclass
from typing import Optional
from rich.console import Console
from rich.table import Table
import httpx

console = Console()

GITHUB_GRAPHQL = "https://api.github.com/graphql"
APTOS_API = "https://api.mainnet.aptoslabs.com/v1"


@dataclass
class HydraHead:
    """Single head of the Hydra query."""
    name: str
    query: str
    trit: int  # GF(3): -1, 0, +1
    variables: dict


def gf3_trit(degree: int) -> int:
    """Compute GF(3) trit from degree."""
    return (degree % 3) - 1


def color_from_seed(seed: int, index: int) -> str:
    """Deterministic color from seed (Gay.jl compatible)."""
    combined = seed ^ (index * 0x9E3779B9)
    hue = (combined % 360)
    return f"hsl({hue}, 70%, 55%)"


class HydraQueryEngine:
    """Multi-head GraphQL query engine for interactome discovery."""
    
    def __init__(self, github_token: Optional[str] = None):
        self.github_token = github_token or os.environ.get("GITHUB_TOKEN")
        self.seed = int(hashlib.sha256(b"security-dao-interactome").hexdigest()[:8], 16)
    
    def _github_headers(self) -> dict:
        return {
            "Authorization": f"Bearer {self.github_token}",
            "Content-Type": "application/json"
        }
    
    async def execute_head(self, head: HydraHead) -> dict:
        """Execute a single Hydra head query."""
        async with httpx.AsyncClient() as client:
            response = await client.post(
                GITHUB_GRAPHQL,
                headers=self._github_headers(),
                json={"query": head.query, "variables": head.variables}
            )
            return response.json()
    
    def security_dao_head(self, org: str, degree: int = 1) -> HydraHead:
        """Create security DAO organization query head."""
        query = """
        query SecurityDAOOrg($org: String!, $limit: Int!) {
          organization(login: $org) {
            name
            description
            repositories(first: $limit, orderBy: {field: STARGAZERS, direction: DESC}) {
              nodes {
                name
                description
                stargazerCount
                primaryLanguage { name }
                repositoryTopics(first: 5) {
                  nodes { topic { name } }
                }
              }
            }
          }
        }
        """
        return HydraHead(
            name=f"security-dao-{org}",
            query=query,
            trit=gf3_trit(degree),
            variables={"org": org, "limit": 10 * degree}
        )
    
    def author_network_head(self, author: str, degree: int = 1) -> HydraHead:
        """Create author network expansion head."""
        query = """
        query AuthorNetwork($author: String!, $followLimit: Int!) {
          user(login: $author) {
            login
            bio
            company
            following(first: $followLimit) {
              nodes {
                login
                repositories(first: 5) {
                  nodes { name primaryLanguage { name } }
                }
              }
            }
            repositories(first: 20, orderBy: {field: PUSHED_AT, direction: DESC}) {
              nodes {
                name
                stargazerCount
                primaryLanguage { name }
              }
            }
          }
        }
        """
        return HydraHead(
            name=f"author-{author}-d{degree}",
            query=query,
            trit=gf3_trit(degree),
            variables={"author": author, "followLimit": 10 * degree}
        )
    
    def move_security_head(self, degree: int = 1) -> HydraHead:
        """Create Move language security search head."""
        query = """
        query MoveSecuritySearch($searchQuery: String!, $limit: Int!) {
          search(query: $searchQuery, type: REPOSITORY, first: $limit) {
            repositoryCount
            nodes {
              ... on Repository {
                nameWithOwner
                description
                stargazerCount
                primaryLanguage { name }
                repositoryTopics(first: 5) {
                  nodes { topic { name } }
                }
              }
            }
          }
        }
        """
        return HydraHead(
            name=f"move-security-d{degree}",
            query=query,
            trit=-1,  # Security = MINUS
            variables={
                "searchQuery": "language:Move security OR audit OR vulnerability",
                "limit": 15 * degree
            }
        )
    
    def aptos_bridge_head(self, module: str = "0x1::coin") -> HydraHead:
        """Create Aptos module query head (non-GraphQL, REST API)."""
        return HydraHead(
            name=f"aptos-bridge-{module}",
            query=f"{APTOS_API}/accounts/0x1/modules",
            trit=0,  # Bridge = ERGODIC
            variables={"module": module}
        )
    
    async def execute_hydra(self, heads: list[HydraHead]) -> dict:
        """Execute all Hydra heads and verify GF(3) conservation."""
        # Verify GF(3) conservation
        trit_sum = sum(h.trit for h in heads)
        if trit_sum % 3 != 0:
            console.print(f"[yellow]Warning: GF(3) not conserved, sum={trit_sum}[/yellow]")
        
        results = {}
        for i, head in enumerate(heads):
            color = color_from_seed(self.seed, i)
            console.print(f"[bold]Executing head: {head.name}[/bold] trit={head.trit} {color}")
            
            if head.name.startswith("aptos-bridge"):
                # REST API call for Aptos
                async with httpx.AsyncClient() as client:
                    resp = await client.get(head.query)
                    results[head.name] = resp.json()
            else:
                results[head.name] = await self.execute_head(head)
        
        return results
    
    def display_interactome(self, results: dict):
        """Display interactome results as rich table."""
        table = Table(title="Hydra-GraphQL Interactome Results")
        table.add_column("Head", style="cyan")
        table.add_column("Trit", style="magenta")
        table.add_column("Results", style="green")
        
        for name, data in results.items():
            count = len(data.get("data", {}).get("search", {}).get("nodes", [])) or \
                    len(data.get("data", {}).get("organization", {}).get("repositories", {}).get("nodes", [])) or \
                    len(data.get("data", {}).get("user", {}).get("repositories", {}).get("nodes", [])) or \
                    len(data) if isinstance(data, list) else 1
            table.add_row(name, str(gf3_trit(hash(name) % 3)), str(count))
        
        console.print(table)


# Personalization functions
def personalize_by_degree(results: dict, author: str, target_degree: int) -> dict:
    """Filter results to show connections at specific degree from author."""
    personalized = {}
    for name, data in results.items():
        degree = int(name.split("-d")[-1]) if "-d" in name else 0
        if degree <= target_degree:
            personalized[name] = data
    return personalized


def compute_author_centrality(results: dict) -> dict[str, float]:
    """Compute centrality scores for authors in interactome."""
    author_counts = {}
    for name, data in results.items():
        if "user" in str(data):
            user_data = data.get("data", {}).get("user", {})
            author = user_data.get("login", "unknown")
            following = user_data.get("following", {}).get("nodes", [])
            author_counts[author] = len(following)
    
    total = sum(author_counts.values()) or 1
    return {a: c / total for a, c in author_counts.items()}


# CLI entry point
if __name__ == "__main__":
    import asyncio
    import sys
    
    async def main():
        engine = HydraQueryEngine()
        
        if len(sys.argv) < 2:
            console.print("[bold]Usage:[/bold] hydra_query.py <command> [args]")
            console.print("  security-dao <org> [degree]")
            console.print("  author <login> [degree]")
            console.print("  move-security [degree]")
            console.print("  full-hydra <org> <author>")
            return
        
        cmd = sys.argv[1]
        
        if cmd == "security-dao":
            org = sys.argv[2] if len(sys.argv) > 2 else "aptos-labs"
            degree = int(sys.argv[3]) if len(sys.argv) > 3 else 1
            heads = [engine.security_dao_head(org, degree)]
        
        elif cmd == "author":
            author = sys.argv[2] if len(sys.argv) > 2 else "bmorphism"
            degree = int(sys.argv[3]) if len(sys.argv) > 3 else 1
            heads = [engine.author_network_head(author, degree)]
        
        elif cmd == "move-security":
            degree = int(sys.argv[2]) if len(sys.argv) > 2 else 1
            heads = [engine.move_security_head(degree)]
        
        elif cmd == "full-hydra":
            org = sys.argv[2] if len(sys.argv) > 2 else "aptos-labs"
            author = sys.argv[3] if len(sys.argv) > 3 else "bmorphism"
            # GF(3) balanced: -1 + 0 + 1 = 0
            heads = [
                engine.move_security_head(1),           # trit = -1 (MINUS)
                engine.security_dao_head(org, 1),       # trit = 0 (ERGODIC)
                engine.author_network_head(author, 2),  # trit = +1 (PLUS)
            ]
        
        else:
            console.print(f"[red]Unknown command: {cmd}[/red]")
            return
        
        results = await engine.execute_hydra(heads)
        engine.display_interactome(results)
    
    asyncio.run(main())
