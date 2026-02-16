#!/usr/bin/env python3
"""
gh-skill-explorer discovery pattern implementation.

Encodes the exploration workflow discovered in session T-019b5207-300a-704b-b75e-8bdf2557254c:
1. Load related skill for context
2. Parallel Exa searches for SKILL.md patterns
3. Widen search radius (tools → frameworks → ecosystems)
4. Map to GitHub topics

Usage:
    uv run discover.py "disk space management"
    uv run discover.py "reverse engineering"
    uv run discover.py "category theory"
"""
# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///

import json
from dataclasses import dataclass
from typing import Optional

@dataclass
class SearchQuery:
    """Exa search query template."""
    name: str
    query_template: str
    num_results: int = 10
    
    def render(self, topic: str) -> str:
        return self.query_template.format(topic=topic)


# Phase 2: Parallel search queries
PARALLEL_SEARCHES = [
    SearchQuery(
        name="skills",
        query_template='site:github.com SKILL.md "{topic}" Claude AI agent',
        num_results=12
    ),
    SearchQuery(
        name="agents_md",
        query_template='site:github.com "SKILL.md" OR "AGENTS.md" {topic}',
        num_results=10
    ),
    SearchQuery(
        name="tools",
        query_template='site:github.com {topic} rust go CLI tool',
        num_results=12
    ),
    SearchQuery(
        name="mcp_servers",
        query_template='site:github.com MCP server {topic} Claude LLM agent',
        num_results=10
    ),
]

# Phase 3: Widening queries (domain-specific)
WIDENING_PATTERNS = {
    "disk space": [
        "site:github.com macos disk space analyzer cleanup utility ncdu duf dust",
        "site:github.com storage management rust go CLI tool filesystem analysis",
        "site:github.com duplicate file finder deduplication macOS cross-platform",
    ],
    "reverse engineering": [
        "site:github.com radare2 ghidra IDA plugin LLM AI assistant",
        "site:github.com MCP server binary analysis malware reversing decompiler",
        "site:github.com awesome reverse engineering binary exploitation CTF tools",
    ],
    "category theory": [
        "site:github.com/topics category-theory applied-category-theory operads sheaves",
        "site:github.com/topics bisimulation coalgebra open-games game-semantics",
        "site:github.com/topics string-diagrams monoidal-categories tensor-networks",
    ],
    "type theory": [
        "site:github.com/topics homotopy-type-theory dependent-types proof-assistant",
        "site:github.com/topics cubical infinity-categories",
    ],
    "artificial life": [
        "site:github.com/topics artificial-life alife cellular-automata emergence",
        "site:github.com/topics complex-systems self-organization",
    ],
    "lisp": [
        "site:github.com/topics clojure scheme lisp repl emacs nrepl babashka",
    ],
}

# Phase 4: GitHub topic mappings (discovered 2025-12-24)
TOPIC_MAPPINGS = {
    "category_theory": {
        "topics": [
            "applied-category-theory",
            "topos",
            "sheaves",
            "polynomial-functors",
        ],
        "anchor_repos": [
            ("ToposInstitute/poly", 113),
            ("b-mehta/topos", 52),
            ("AlgebraicJulia/Catlab.jl", 1000),
        ]
    },
    "game_semantics": {
        "topics": [
            "game-semantics",
            "bisimulation",
            "coalgebra",
        ],
        "anchor_repos": [
            ("Lapin0t/ogs", None),
            ("CertiKOS/rbgs", None),
            ("coq-contribs/coalgebras", None),
        ]
    },
    "hott": {
        "topics": [
            "homotopy-type-theory",
            "cubical-type-theory",
            "infinity-categories",
            "dependent-types",
        ],
        "anchor_repos": [
            ("HoTT/Coq-HoTT", 1300),
            ("HoTT/book", 2100),
            ("rzk-lang/rzk", 223),
            ("mortberg/cubicaltt", 581),
            ("the1lab/1lab", 366),
        ]
    },
    "string_diagrams": {
        "topics": [
            "string-diagrams",
            "monoidal-categories",
            "zx-calculus",
            "tensor-networks",
        ],
        "anchor_repos": [
            ("discopy/discopy", 392),
            ("akissinger/chyp", 113),
            ("zxcalc/book", 78),
            ("AlgebraicJulia/CategoricalTensorNetworks.jl", None),
        ]
    },
    "artificial_life": {
        "topics": [
            "artificial-life",
            "cellular-automata",
            "emergence",
            "complex-systems",
        ],
        "anchor_repos": [
            ("hunar4321/particle-life", None),
            ("dwoiwode/awesome-neural-cellular-automata", None),
        ]
    },
    "clojure_lisp": {
        "topics": [
            "clojure",
            "babashka",
            "nrepl",
            "cider",
        ],
        "anchor_repos": [
            ("clojure-emacs/cider", 3600),
            ("babashka/babashka", None),
            ("bhauman/clojure-mcp", 634),
            ("nrepl/nrepl", None),
        ]
    },
    "reverse_engineering": {
        "topics": [
            "radare2",
            "binary-exploitation",
            "reverse-engineering",
        ],
        "anchor_repos": [
            ("radareorg/radare2", None),
            ("angr/angr", 7900),
            ("pwndbg/pwndbg", None),
            ("hugsy/gef", 7400),
            ("LaurieWired/GhidraMCP", None),
            ("mrexodia/ida-pro-mcp", None),
        ]
    },
    "skills_ecosystem": {
        "topics": [],
        "anchor_repos": [
            ("ComposioHQ/awesome-claude-skills", 5595),
            ("anthropics/skills", None),
            ("travisvn/awesome-claude-skills", None),
            ("yusufkaraaslan/Skill_Seekers", None),
        ]
    },
    "filesystem_tools": {
        "topics": [],
        "anchor_repos": [
            ("muesli/duf", 13300),
            ("bootandy/dust", None),
            ("Byron/dua-cli", None),
            ("dundee/gdu", None),
            ("solidiquis/erdtree", None),
            ("cyanheads/filesystem-mcp-server", None),
        ]
    },
}


def generate_mcp_calls(topic: str) -> dict:
    """Generate MCP tool calls for the discovery pattern."""
    
    # Phase 2: Parallel searches
    phase2_calls = []
    for sq in PARALLEL_SEARCHES:
        phase2_calls.append({
            "tool": "mcp__exa__web_search_exa",
            "params": {
                "query": sq.render(topic),
                "numResults": sq.num_results
            }
        })
    
    # Phase 3: Widening (find matching domain)
    phase3_calls = []
    topic_lower = topic.lower()
    for domain, queries in WIDENING_PATTERNS.items():
        if domain in topic_lower or any(word in topic_lower for word in domain.split()):
            for q in queries:
                phase3_calls.append({
                    "tool": "mcp__exa__web_search_exa",
                    "params": {
                        "query": q,
                        "numResults": 10
                    }
                })
            break
    
    # Phase 4: Topic mappings
    phase4_topics = []
    for category, data in TOPIC_MAPPINGS.items():
        if any(word in topic_lower for word in category.replace("_", " ").split()):
            phase4_topics.append({
                "category": category,
                "github_topics": data["topics"],
                "anchor_repos": data["anchor_repos"]
            })
    
    return {
        "topic": topic,
        "phase2_parallel_searches": phase2_calls,
        "phase3_widening_searches": phase3_calls,
        "phase4_topic_mappings": phase4_topics,
    }


def score_skill_similarity(content: str) -> float:
    """Score 0.0-1.0 similarity to plurigrid/asi pattern."""
    markers = {
        "trit:": 0.15,
        "GF(3)": 0.15,
        "SplitMix": 0.15,
        "parallel": 0.10,
        "ERGODIC": 0.10,
        "PLUS": 0.10,
        "MINUS": 0.10,
        "deterministic": 0.05,
        "seed": 0.05,
        "conservation": 0.05
    }
    
    score = 0.0
    content_lower = content.lower()
    for marker, weight in markers.items():
        if marker.lower() in content_lower:
            score += weight
    
    return min(1.0, score)


def main():
    import sys
    
    if len(sys.argv) < 2:
        print("Usage: discover.py <topic>")
        print()
        print("Examples:")
        print('  discover.py "disk space management"')
        print('  discover.py "reverse engineering"')
        print('  discover.py "category theory"')
        sys.exit(1)
    
    topic = " ".join(sys.argv[1:])
    result = generate_mcp_calls(topic)
    
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
