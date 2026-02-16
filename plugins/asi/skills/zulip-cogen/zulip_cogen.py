#!/usr/bin/env python3
"""
Zulip Cogen - Code generator from Category Theory Zulip knowledge base.

Trit: +1 (PLUS - Generator)
GF(3) Triad: chain-of-states(-1) ⊗ proof-of-frog(0) ⊗ zulip-cogen(+1) = 0
"""

import os
import re
import json
import duckdb
from pathlib import Path
from typing import Optional, List, Dict, Any
from dataclasses import dataclass
from enum import Enum

# SPI constants
GAY_SEED = 0x6761795f636f6c6f
GOLDEN = 0x9e3779b97f4a7c15
MIX1 = 0xbf58476d1ce4e5b9
MIX2 = 0x94d049bb133111eb
MASK64 = 0xffffffffffffffff


class GenMode(Enum):
    PROOF = "proof"
    DIAGRAM = "diagram"
    IMPL = "impl"
    SCHEMA = "schema"
    SKILL = "skill"


class Verdict(Enum):
    PROCEED = "proceed"
    WARN = "warn"
    ABORT = "abort"


@dataclass
class Coverage:
    """Dynamic sufficiency coverage for generation."""
    score: float  # 0.0 - 1.0
    message_count: int
    math_count: int
    code_count: int
    causal_state: str
    
    def is_sufficient(self, mode: str) -> bool:
        """Check if coverage is sufficient for generation mode."""
        thresholds = {
            'proof': (0.7, 3),   # 70% score, 3+ math
            'diagram': (0.5, 2), # 50% score, 2+ messages
            'impl': (0.6, 5),    # 60% score, 5+ code
            'schema': (0.6, 3),  # 60% score, 3+ messages
            'skill': (0.4, 10),  # 40% score, 10+ messages
        }
        min_score, min_count = thresholds.get(mode, (0.5, 2))
        return self.score >= min_score and self.message_count >= min_count


@dataclass
class Message:
    id: int
    sender: str
    content: str
    color: str
    stream: str


def splitmix64(x: int) -> int:
    z = (x + GOLDEN) & MASK64
    z = ((z ^ (z >> 30)) * MIX1) & MASK64
    z = ((z ^ (z >> 27)) * MIX2) & MASK64
    return (z ^ (z >> 31)) & MASK64


def fnv1a(s: str) -> int:
    h = 0xcbf29ce484222325
    for b in s.encode('utf-8'):
        h = ((h ^ b) * 0x100000001b3) & MASK64
    return h


def seed_to_color(seed: int) -> str:
    h = splitmix64(seed)
    return f"#{(h>>16)&0xFF:02x}{(h>>8)&0xFF:02x}{h&0xFF:02x}"


class ZulipCogen:
    """
    Code generator from CT Zulip knowledge base.
    
    Transforms discussions into executable artifacts:
    - Lean4 proofs
    - Mermaid diagrams
    - Julia/Python implementations
    - ACSet schemas
    - SKILL.md files
    """
    
    def __init__(self, db_path: str = "~/ies/hatchery.duckdb"):
        self.db_path = Path(db_path).expanduser()
        self.gay_seed = GAY_SEED
    
    def connect(self) -> duckdb.DuckDBPyConnection:
        return duckdb.connect(str(self.db_path), read_only=True)
    
    def compute_coverage(self, query: str, messages: List[Message], mode: str) -> Coverage:
        """Compute dynamic sufficiency coverage for generation."""
        if not messages:
            return Coverage(0.0, 0, 0, 0, "EMPTY")
        
        # Count math and code content
        math_count = sum(1 for m in messages if '$' in m.content or '\\' in m.content)
        code_count = sum(1 for m in messages if '```' in m.content or '`' in m.content)
        
        # Determine causal state
        if mode == 'proof' and math_count >= 3:
            causal_state = "PROOF_READY"
            base_score = 0.8
        elif mode == 'diagram' and len(messages) >= 2:
            causal_state = "DIAGRAM_READY"
            base_score = 0.7
        elif mode == 'impl' and code_count >= 2:
            causal_state = "IMPL_READY"
            base_score = 0.75
        elif mode == 'schema' and len(messages) >= 3:
            causal_state = "SCHEMA_READY"
            base_score = 0.7
        elif mode == 'skill' and len(messages) >= 10:
            causal_state = "SKILL_READY"
            base_score = 0.6
        else:
            causal_state = "INSUFFICIENT"
            base_score = 0.3
        
        # Adjust score based on content richness
        score = min(1.0, base_score + (len(messages) / 100) + (math_count / 20) + (code_count / 20))
        
        return Coverage(
            score=score,
            message_count=len(messages),
            math_count=math_count,
            code_count=code_count,
            causal_state=causal_state
        )
    
    def pre_generation_gate(self, query: str, mode: str, pond: Optional[str] = None) -> tuple:
        """
        Dynamic sufficiency gate - verify sufficient context before generation.
        
        Returns: (Verdict, Coverage, messages)
        """
        messages = self.retrieve(query, pond, limit=30)
        coverage = self.compute_coverage(query, messages, mode)
        
        if coverage.is_sufficient(mode):
            return (Verdict.PROCEED, coverage, messages)
        elif coverage.score >= 0.3:
            return (Verdict.WARN, coverage, messages)
        else:
            return (Verdict.ABORT, coverage, messages)
    
    def retrieve(
        self,
        query: str,
        pond: Optional[str] = None,
        limit: int = 20
    ) -> List[Message]:
        """Retrieve relevant messages from archive."""
        with self.connect() as conn:
            sql = """
                SELECT m.id, m.sender, m.content, m.color, s.name
                FROM ct_zulip_messages m
                JOIN ct_zulip_streams s ON m.stream_id = s.id
                WHERE m.content LIKE ?
            """
            params = [f"%{query}%"]
            
            if pond:
                sql += " AND s.name LIKE ?"
                params.append(f"%{pond}%")
            
            sql += " ORDER BY m.timestamp DESC LIMIT ?"
            params.append(limit)
            
            rows = conn.execute(sql, params).fetchall()
            return [
                Message(id=r[0], sender=r[1], content=r[2], 
                       color=r[3], stream=r[4])
                for r in rows
            ]
    
    def extract_math(self, content: str) -> List[str]:
        """Extract LaTeX math from message content."""
        # Match $...$ and $$...$$
        inline = re.findall(r'\$([^\$]+)\$', content)
        display = re.findall(r'\$\$([^\$]+)\$\$', content)
        return inline + display
    
    def extract_code(self, content: str) -> List[Dict[str, str]]:
        """Extract code blocks from message content."""
        pattern = r'```(\w*)\n(.*?)```'
        matches = re.findall(pattern, content, re.DOTALL)
        return [{'lang': m[0] or 'text', 'code': m[1].strip()} 
                for m in matches]
    
    def generate_proof(self, query: str, pond: Optional[str] = None) -> str:
        """Generate Lean4 proof from discussions."""
        messages = self.retrieve(query, pond, limit=10)
        
        if not messages:
            return f"-- No discussions found for: {query}"
        
        # Extract math content
        math_content = []
        for msg in messages:
            math_content.extend(self.extract_math(msg.content))
        
        # Build proof skeleton
        color = seed_to_color(fnv1a(query) ^ self.gay_seed)
        
        proof = f"""-- Generated from CT Zulip: {query}
-- Color: {color}
-- Sources: {len(messages)} messages

import Mathlib

/-- 
Theorem derived from Zulip discussions about: {query}

Contributors: {', '.join(set(m.sender for m in messages[:5]))}
-/
theorem {self._to_identifier(query)} : sorry := by
  -- Proof structure extracted from discussions
  sorry
"""
        
        if math_content:
            proof += f"""
/- Mathematical content found:
{chr(10).join(f'  • {m}' for m in math_content[:5])}
-/
"""
        return proof
    
    def generate_diagram(
        self, 
        query: str, 
        pond: Optional[str] = None,
        format: str = "mermaid"
    ) -> str:
        """Generate diagram from discussions."""
        messages = self.retrieve(query, pond, limit=15)
        
        if not messages:
            return f"graph LR\n    A[No results for: {query}]"
        
        color = seed_to_color(fnv1a(query) ^ self.gay_seed)
        
        # Extract potential nodes from content
        nodes = set()
        edges = []
        
        keywords = ['functor', 'category', 'morphism', 'object', 
                   'adjoint', 'limit', 'colimit', 'natural transformation']
        
        for msg in messages:
            content_lower = msg.content.lower()
            found = [k for k in keywords if k in content_lower]
            nodes.update(found)
        
        if format == "mermaid":
            diagram = f"""graph TD
    %% Generated from CT Zulip: {query}
    %% Color: {color}
"""
            node_list = list(nodes)[:6]
            for i, node in enumerate(node_list):
                node_id = node.replace(' ', '_').upper()
                diagram += f'    {node_id}["{node.title()}"]\n'
            
            # Add some edges
            for i in range(len(node_list) - 1):
                src = node_list[i].replace(' ', '_').upper()
                dst = node_list[i+1].replace(' ', '_').upper()
                diagram += f'    {src} --> {dst}\n'
            
            diagram += f'    style {node_list[0].replace(" ", "_").upper()} fill:{color}\n'
            return diagram
        
        else:  # tikzcd
            return f"""% Generated from CT Zulip: {query}
\\begin{{tikzcd}}
    A \\arrow[r] \\arrow[d] & B \\arrow[d] \\\\
    C \\arrow[r] & D
\\end{{tikzcd}}
"""
    
    def generate_impl(
        self,
        query: str,
        pond: Optional[str] = None,
        lang: str = "julia"
    ) -> str:
        """Generate implementation from discussions."""
        messages = self.retrieve(query, pond, limit=10)
        
        color = seed_to_color(fnv1a(query) ^ self.gay_seed)
        func_name = self._to_identifier(query)
        
        # Extract any code blocks
        code_blocks = []
        for msg in messages:
            code_blocks.extend(self.extract_code(msg.content))
        
        if lang == "julia":
            impl = f'''"""
    {func_name}

Generated from CT Zulip discussions about: {query}
Color: {color}
Sources: {len(messages)} messages
"""
function {func_name}(args...)
    # Implementation derived from Zulip discussions
    # Contributors: {', '.join(set(m.sender for m in messages[:3]))}
    
    error("Not yet implemented")
end
'''
        elif lang == "python":
            impl = f'''"""
{func_name}

Generated from CT Zulip discussions about: {query}
Color: {color}
Sources: {len(messages)} messages
"""

def {func_name}(*args, **kwargs):
    """
    Implementation derived from Zulip discussions.
    Contributors: {', '.join(set(m.sender for m in messages[:3]))}
    """
    raise NotImplementedError()
'''
        else:
            impl = f"// Generated for: {query}\n// Lang: {lang}\n"
        
        if code_blocks:
            impl += f"\n# Referenced code from discussions:\n"
            for block in code_blocks[:2]:
                impl += f"# [{block['lang']}]\n# {block['code'][:100]}...\n"
        
        return impl
    
    def generate_schema(self, query: str, pond: Optional[str] = None) -> str:
        """Generate ACSet schema from discussions."""
        messages = self.retrieve(query, pond, limit=10)
        
        color = seed_to_color(fnv1a(query) ^ self.gay_seed)
        schema_name = self._to_identifier(query, pascal=True) + "Schema"
        
        return f'''# Generated from CT Zulip: {query}
# Color: {color}
# Sources: {len(messages)} messages

using ACSets

@present {schema_name}(FreeSchema) begin
    # Objects extracted from discussions
    Ob::Ob
    Mor::Ob
    
    # Morphisms
    src::Hom(Mor, Ob)
    tgt::Hom(Mor, Ob)
    
    # Composition (if applicable)
    # compose::Hom(Mor × Mor, Mor)
end

const {schema_name.replace("Schema", "")} = ACSetType({schema_name})

# Contributors: {', '.join(set(m.sender for m in messages[:5]))}
'''
    
    def generate_skill(self, pond: str) -> str:
        """Generate SKILL.md from a pond."""
        with self.connect() as conn:
            # Get pond stats
            stats = conn.execute("""
                SELECT s.name, s.color, COUNT(m.id) as cnt,
                       MIN(m.timestamp) as first_msg,
                       MAX(m.timestamp) as last_msg
                FROM ct_zulip_streams s
                LEFT JOIN ct_zulip_messages m ON s.id = m.stream_id
                WHERE s.name LIKE ?
                GROUP BY s.id, s.name, s.color
            """, [f"%{pond}%"]).fetchone()
            
            if not stats:
                return f"# {pond}\n\nNo pond found."
            
            name, color, count, first, last = stats
            
            # Get top contributors
            contributors = conn.execute("""
                SELECT sender, COUNT(*) as cnt
                FROM ct_zulip_messages m
                JOIN ct_zulip_streams s ON m.stream_id = s.id
                WHERE s.name LIKE ?
                GROUP BY sender
                ORDER BY cnt DESC
                LIMIT 5
            """, [f"%{pond}%"]).fetchall()
            
            skill_name = self._to_identifier(name.split(':')[-1] if ':' in name else name)
            
            return f'''# {name.replace(':', ' ').title()} Skill

**Trit**: 0 (ERGODIC - Coordinator)
**Color**: {color}

## Overview

Generated from CT Zulip pond: `{name}`

- **Messages**: {count:,}
- **First**: {first}
- **Last**: {last}

## Top Contributors

| Contributor | Messages |
|-------------|----------|
{chr(10).join(f"| {c[0]} | {c[1]} |" for c in contributors)}

## Topics

Extracted from pond discussions.

## References

- [CT Zulip: {name}](https://cats-for-ai.zulipchat.com/)

## Gay.jl

```python
color = "{color}"  # Deterministic from pond ID
```
'''
    
    def _to_identifier(self, s: str, pascal: bool = False) -> str:
        """Convert string to valid identifier."""
        # Remove non-alphanumeric
        clean = re.sub(r'[^a-zA-Z0-9\s]', '', s)
        words = clean.lower().split()
        
        if pascal:
            return ''.join(w.title() for w in words)
        else:
            return '_'.join(words)
    
    def generate(
        self,
        mode: str,
        query: str,
        pond: Optional[str] = None,
        skip_gate: bool = False,
        **kwargs
    ) -> str:
        """
        Main generation entry point with dynamic sufficiency gating.
        
        Gate checks coverage before generation:
        - PROCEED: Sufficient context, generate
        - WARN: Low coverage, generate with warning
        - ABORT: Insufficient context, refuse
        """
        # Dynamic sufficiency gate
        if not skip_gate:
            verdict, coverage, _ = self.pre_generation_gate(query, mode, pond)
            
            header = f"""# Dynamic Sufficiency Report
# Query: {query}
# Mode: {mode}
# Verdict: {verdict.value.upper()}
# Coverage: {coverage.score:.0%} ({coverage.message_count} msgs, {coverage.math_count} math, {coverage.code_count} code)
# Causal State: {coverage.causal_state}

"""
            if verdict == Verdict.ABORT:
                return header + f"# ❌ GENERATION ABORTED: Insufficient context\n# Load more skills or broaden query"
            elif verdict == Verdict.WARN:
                header += f"# ⚠️  WARNING: Low coverage, results may be incomplete\n\n"
        else:
            header = ""
        
        # Generate based on mode
        if mode == "proof":
            return header + self.generate_proof(query, pond)
        elif mode == "diagram":
            return header + self.generate_diagram(query, pond, kwargs.get('format', 'mermaid'))
        elif mode == "impl":
            return header + self.generate_impl(query, pond, kwargs.get('lang', 'julia'))
        elif mode == "schema":
            return header + self.generate_schema(query, pond)
        elif mode == "skill":
            return header + self.generate_skill(query)
        else:
            return f"Unknown mode: {mode}"


def tui_mode(cogen: ZulipCogen):
    """Interactive TUI for zulip-cogen."""
    print("🐸⚡ Zulip Cogen TUI")
    print(f"   Archive: {cogen.db_path}")
    print("   Commands: proof|diagram|impl|schema|skill <query> [--pond <name>]")
    print("   Special: ponds, coverage <query>, quit")
    print()
    
    while True:
        try:
            cmd = input("⚡> ").strip()
        except (EOFError, KeyboardInterrupt):
            print("\n🦎 Goodbye!")
            break
        
        if not cmd:
            continue
        
        parts = cmd.split()
        action = parts[0].lower()
        
        if action in ('quit', 'q', 'exit'):
            print("🦎 Goodbye!")
            break
        
        elif action == 'ponds':
            with cogen.connect() as conn:
                rows = conn.execute("""
                    SELECT s.name, s.color, COUNT(m.id) as cnt
                    FROM ct_zulip_streams s
                    LEFT JOIN ct_zulip_messages m ON s.id = m.stream_id
                    GROUP BY s.id, s.name, s.color
                    ORDER BY cnt DESC LIMIT 15
                """).fetchall()
                print(f"{'Pond':<40} {'Color':<10} {'Msgs':>8}")
                print("-" * 60)
                for name, color, cnt in rows:
                    print(f"{name[:40]:<40} {color:<10} {cnt:>8}")
        
        elif action == 'coverage':
            if len(parts) < 2:
                print("Usage: coverage <query> [--pond <name>]")
                continue
            query = ' '.join(p for p in parts[1:] if not p.startswith('--'))
            pond = None
            if '--pond' in parts:
                idx = parts.index('--pond')
                pond = parts[idx + 1] if idx + 1 < len(parts) else None
            
            verdict, coverage, msgs = cogen.pre_generation_gate(query, 'proof', pond)
            print(f"Query: {query}")
            print(f"Verdict: {verdict.value.upper()}")
            print(f"Coverage: {coverage.score:.0%}")
            print(f"Messages: {coverage.message_count}")
            print(f"Math: {coverage.math_count}, Code: {coverage.code_count}")
            print(f"Causal State: {coverage.causal_state}")
        
        elif action in ('proof', 'diagram', 'impl', 'schema', 'skill'):
            if len(parts) < 2:
                print(f"Usage: {action} <query> [--pond <name>]")
                continue
            
            # Parse query and pond
            query_parts = []
            pond = None
            i = 1
            while i < len(parts):
                if parts[i] == '--pond' and i + 1 < len(parts):
                    pond = parts[i + 1]
                    i += 2
                else:
                    query_parts.append(parts[i])
                    i += 1
            query = ' '.join(query_parts)
            
            # Generate with sufficiency gate
            result = cogen.generate(mode=action, query=query, pond=pond)
            print(result)
        
        elif action == 'help':
            print("Commands:")
            print("  proof <query>   - Generate Lean4 theorem")
            print("  diagram <query> - Generate Mermaid diagram")
            print("  impl <query>    - Generate Julia/Python code")
            print("  schema <query>  - Generate ACSet schema")
            print("  skill <pond>    - Generate SKILL.md from pond")
            print("  coverage <query>- Check dynamic sufficiency")
            print("  ponds           - List available ponds")
            print("  quit            - Exit")
        
        else:
            print(f"Unknown command: {action}. Type 'help' for commands.")


def main():
    import argparse
    
    parser = argparse.ArgumentParser(description="Zulip Cogen ⚡🐸")
    parser.add_argument('mode', nargs='?', default='tui',
                        choices=['proof', 'diagram', 'impl', 'schema', 'skill', 'tui', 'coverage'],
                        help='Generation mode (default: tui)')
    parser.add_argument('query', nargs='?', help='Search query or pond name')
    parser.add_argument('--pond', '-p', help='Filter by pond name')
    parser.add_argument('--lang', '-l', default='julia', help='Output language')
    parser.add_argument('--format', '-f', default='mermaid', help='Diagram format')
    parser.add_argument('--db', default='~/ies/hatchery.duckdb', help='DuckDB path')
    parser.add_argument('--output', '-o', help='Output file')
    parser.add_argument('--skip-gate', action='store_true', help='Skip sufficiency gate')
    
    args = parser.parse_args()
    
    cogen = ZulipCogen(args.db)
    
    if args.mode == 'tui':
        tui_mode(cogen)
        return
    
    if not args.query:
        parser.error(f"Mode '{args.mode}' requires a query argument")
    
    if args.mode == 'coverage':
        verdict, coverage, _ = cogen.pre_generation_gate(args.query, 'proof', args.pond)
        print(f"Query: {args.query}")
        print(f"Verdict: {verdict.value.upper()}")
        print(f"Coverage: {coverage.score:.0%} ({coverage.message_count} msgs)")
        print(f"Causal State: {coverage.causal_state}")
        return
    
    result = cogen.generate(
        mode=args.mode,
        query=args.query,
        pond=args.pond,
        lang=args.lang,
        format=args.format,
        skip_gate=args.skip_gate
    )
    
    if args.output:
        Path(args.output).write_text(result)
        print(f"✓ Written to {args.output}")
    else:
        print(result)


if __name__ == "__main__":
    main()
