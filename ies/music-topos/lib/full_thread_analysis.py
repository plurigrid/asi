#!/usr/bin/env python3
"""
Full Thread Relational Analysis - Live Data from 30 Threads
Applies HyJAX relational patterns to actual Amp thread history
"""

import json
import time
import re
import math
from dataclasses import dataclass, field
from typing import Dict, List, Any, Tuple
from collections import defaultdict

# ============================================================================
# THREAD DATA (30 recent threads)
# ============================================================================

THREADS = [
    {"id": "T-019b4417-c005-743b-8a4c-1b87bcfc806f", "title": "Maximally polarizing implied worlds along subagent directions", "messageCount": 77},
    {"id": "T-019b4424-7b9e-7515-bb83-5514e2aefba8", "title": "Exploring relational thinking with HyJAX skills", "messageCount": 47},
    {"id": "T-019b4405-2a14-7207-af89-748a784371d5", "title": "Load localsend script", "messageCount": 306},
    {"id": "T-019b4412-7cbf-705c-81e8-1b84fb6d49c3", "title": "Use alife skill with Exa MCP for refined queries", "messageCount": 59},
    {"id": "T-019b43f1-cae1-7043-9196-c6839793df4c", "title": "List of active workspace threads", "messageCount": 112},
    {"id": "T-019b43f9-f76d-771f-b361-59e94bc175e6", "title": "Load all the most bizarre skills", "messageCount": 108},
    {"id": "T-019b43f5-0762-73c9-8c9b-4f36e494e5c3", "title": "LocalSend exchange via subagent skill groupings", "messageCount": 33},
    {"id": "T-019b43f1-969c-729d-b7a6-0eda331ceba2", "title": "Fix MCP issue in AMP immediately", "messageCount": 18},
    {"id": "T-019b43c2-dafd-7457-a442-82e29798a0fb", "title": "Refactor justfile to be cleaner", "messageCount": 29},
    {"id": "T-019b43de-907c-7008-a545-57e8ff698498", "title": "Random walk spectral gap refinement process", "messageCount": 104},
    {"id": "T-019b43e6-3692-7390-af9a-e2da68fed856", "title": "Skills for cohesive sonification platform", "messageCount": 32},
    {"id": "T-019b43d0-5985-7669-adbe-22cbac795113", "title": "Continuing Signal database analysis with adjacency and sparse structures", "messageCount": 52},
    {"id": "T-019b43b8-a9e6-7109-8142-74c4e95f725a", "title": "DuckDB time travel queries for November 2025", "messageCount": 151},
    {"id": "T-019b43a6-11f7-77a8-a9cd-ea618e457b70", "title": "Load acset skill", "messageCount": 88},
    {"id": "T-019b43a1-9412-726e-bf0b-f18536b93f2a", "title": "Extend acset with discohy threads neighbor awareness", "messageCount": 52},
    {"id": "T-019b438f-c843-7779-8812-bc0d6fe8b803", "title": "Continue synergistic skill triads and subagent coloring", "messageCount": 177},
    {"id": "T-019b4388-8d1f-710e-9bce-8cdc3d8ea000", "title": "Continue verifying justfile recipes and fixes", "messageCount": 95},
    {"id": "T-019b438d-c2ce-72ee-8ecc-c34dec2272c5", "title": "Fix hatchling wheel build configuration", "messageCount": 12},
    {"id": "T-019b4364-7514-7758-a42c-fd160b7d2317", "title": "Instrumental resources for topos geometric morphisms", "messageCount": 145},
    {"id": "T-019b4334-885f-7395-9905-1bf90b48983f", "title": "Unworld system GF(3) conservation and agent propagation", "messageCount": 116},
    {"id": "T-019b42fd-3020-74f4-808b-331ec29b75c2", "title": "Borkdude skill integration and goblin capability propagation", "messageCount": 141},
    {"id": "T-019b42f5-695f-7328-90e7-ca2b0b580303", "title": "Explore AI skills ruler and sexp-wrapped cherry", "messageCount": 30},
    {"id": "T-019b42dd-588b-755f-b0dd-4b319ad6d7aa", "title": "Maximum parallelism with SPI and SplitMixTernary", "messageCount": 116},
    {"id": "T-019b42eb-b180-707a-bd3b-ff5eb2d7f657", "title": "Update codex locally to latest released", "messageCount": 113},
    {"id": "T-019b42cd-e554-75b2-949d-8723ba328c72", "title": "Integrate clj-kondo plurigrid/asi 3-coloring with skills", "messageCount": 58},
    {"id": "T-019b42b1-e9cd-75c3-84c8-8c4de7c109fd", "title": "Integrating transients, Babashka, and MCP for Codex", "messageCount": 143},
    {"id": "T-019b428e-cf8e-72bd-8485-a59ca9e9e477", "title": "Integrate Synadia broadcasts with WORLD system", "messageCount": 102},
    {"id": "T-019b4274-b674-754e-a853-86367a34c154", "title": "Lazy directory trees with local cache in Hydra", "messageCount": 160},
    {"id": "T-019b4274-a43a-7389-9ad6-7e25a34d1acf", "title": "Forked(2): Fork and continue", "messageCount": 138},
    {"id": "T-019b4274-9366-70f7-85fa-8a0a7012e021", "title": "Forked: Fork and continue", "messageCount": 137},
]

# Concept patterns to extract from titles
CONCEPT_PATTERNS = {
    'skill': r'\bskill\b',
    'MCP': r'\bmcp\b',
    'subagent': r'\bsubagent\b',
    'thread': r'\bthread\b',
    'DuckDB': r'\bduckdb\b',
    'ACSet': r'\bacset\b',
    'GF3': r'\bgf\(?3\)?|ternary|3-color',
    'parallelism': r'\bparallel\b|\bspi\b',
    'Babashka': r'\bbabashka\b|\bbb\b',
    'Clojure': r'\bclj\b|\bclojure\b|\bcider\b',
    'topos': r'\btopos\b|\bgeometric\b|\bmorphism\b',
    'WORLD': r'\bworld\b|\bunworld\b',
    'Synadia': r'\bsynadia\b|\bnats\b',
    'LocalSend': r'\blocalsend\b',
    'justfile': r'\bjustfile\b|\brecipe\b',
    'Hydra': r'\bhydra\b|\blazy\b',
    'sonification': r'\bsonifi\b|\bmusic\b',
    'spectral': r'\bspectral\b|\brandom\s+walk\b',
    'entropy': r'\bentropy\b',
    'relational': r'\brelational\b',
    'HyJAX': r'\bhyjax\b',
    'alife': r'\balife\b',
    'fork': r'\bfork\b',
    'codex': r'\bcodex\b',
    'Signal': r'\bsignal\b',
    'discohy': r'\bdiscohy\b',
    'borkdude': r'\bborkdude\b',
    'kondo': r'\bkondo\b',
    'plurigrid': r'\bplurigrid\b',
    'goblin': r'\bgoblin\b',
    'propagation': r'\bpropagat\b',
    'coloring': r'\bcolor\b',
    'triad': r'\btriad\b',
    'synergistic': r'\bsynergi\b',
}


def extract_concepts(text: str) -> List[str]:
    """Extract concepts from text"""
    found = []
    text_lower = text.lower()
    for concept, pattern in CONCEPT_PATTERNS.items():
        if re.search(pattern, text_lower):
            found.append(concept)
    return found


def compute_entropy(values: List[float]) -> float:
    """Shannon entropy"""
    if not values:
        return 0.0
    total = sum(values)
    if total == 0:
        return 0.0
    probs = [v / total for v in values if v > 0]
    return -sum(p * math.log2(p) for p in probs if p > 0)


# ============================================================================
# ACSET + ANALYSIS
# ============================================================================

@dataclass  
class ThreadACSet:
    threads: Dict[str, Dict] = field(default_factory=dict)
    concepts: Dict[str, Dict] = field(default_factory=dict)
    thread_concepts: Dict[str, List[str]] = field(default_factory=dict)
    concept_relations: Dict[str, Dict] = field(default_factory=dict)
    
    def add_thread(self, tid: str, title: str, msg_count: int):
        self.threads[tid] = {'id': tid, 'title': title, 'messages': msg_count}
        
    def add_concept(self, name: str):
        if name not in self.concepts:
            self.concepts[name] = {'name': name, 'frequency': 0, 'threads': []}
        self.concepts[name]['frequency'] += 1
        
    def link_thread_concept(self, tid: str, concept: str):
        if tid not in self.thread_concepts:
            self.thread_concepts[tid] = []
        self.thread_concepts[tid].append(concept)
        self.concepts[concept]['threads'].append(tid)
        
    def add_relation(self, c1: str, c2: str, rtype: str = 'co-occurs'):
        key = f"{c1}→{c2}"
        if key not in self.concept_relations:
            self.concept_relations[key] = {'from': c1, 'to': c2, 'type': rtype, 'weight': 0}
        self.concept_relations[key]['weight'] += 1


class ColoredSExpr:
    def __init__(self, color: str, children: List):
        self.color = color
        self.children = children
    
    def __repr__(self):
        child_strs = [repr(c) if isinstance(c, ColoredSExpr) else str(c) for c in self.children]
        return f"({self.color} {' '.join(child_strs[:3])}{'...' if len(child_strs) > 3 else ''})"
    
    def to_list(self):
        return [self.color, [c.to_list() if isinstance(c, ColoredSExpr) else c for c in self.children]]


def build_acset(threads: List[Dict]) -> ThreadACSet:
    """Build ACSet from thread data"""
    acset = ThreadACSet()
    
    for t in threads:
        tid = t['id']
        title = t['title']
        msg_count = t['messageCount']
        
        acset.add_thread(tid, title, msg_count)
        
        # Extract concepts from title
        concepts = extract_concepts(title)
        for c in concepts:
            acset.add_concept(c)
            acset.link_thread_concept(tid, c)
        
        # Add co-occurrence relations
        for i, c1 in enumerate(concepts):
            for c2 in concepts[i+1:]:
                acset.add_relation(c1, c2)
                acset.add_relation(c2, c1)  # symmetric
    
    return acset


def acset_to_sexpr(acset: ThreadACSet) -> ColoredSExpr:
    """Convert to Colored S-expression"""
    sorted_concepts = sorted(acset.concepts.items(), key=lambda x: -x[1]['frequency'])[:15]
    sorted_relations = sorted(acset.concept_relations.items(), key=lambda x: -x[1]['weight'])[:20]
    
    return ColoredSExpr("acset-gold", [
        ColoredSExpr("threads-red", [
            ColoredSExpr("thread", [t['id'][:20], t['messages']])
            for t in list(acset.threads.values())[:10]
        ]),
        ColoredSExpr("concepts-green", [
            ColoredSExpr("concept", [name, data['frequency']])
            for name, data in sorted_concepts
        ]),
        ColoredSExpr("relations-purple", [
            ColoredSExpr("edge", [r['from'], r['weight'], r['to']])
            for _, r in sorted_relations
        ])
    ])


def analyze_and_report(acset: ThreadACSet):
    """Full analysis with report"""
    print("\n" + "="*70)
    print("  FULL THREAD RELATIONAL ANALYSIS - 30 THREADS")
    print("  HyJAX Patterns | ACSet Schema | Colored S-expressions")
    print("="*70)
    
    # Summary
    total_msgs = sum(t['messages'] for t in acset.threads.values())
    print(f"\n[1] ACSET SUMMARY")
    print(f"    Threads:    {len(acset.threads)}")
    print(f"    Messages:   {total_msgs}")
    print(f"    Concepts:   {len(acset.concepts)}")
    print(f"    Relations:  {len(acset.concept_relations)}")
    
    # Top concepts
    print(f"\n[2] TOP CONCEPTS (by frequency)")
    sorted_concepts = sorted(acset.concepts.items(), key=lambda x: -x[1]['frequency'])
    for i, (name, data) in enumerate(sorted_concepts[:15]):
        bar = "█" * data['frequency']
        print(f"    {i+1:2}. {name:15} {data['frequency']:3} {bar}")
    
    # Concept entropy
    freqs = [c['frequency'] for c in acset.concepts.values()]
    entropy = compute_entropy(freqs)
    print(f"\n[3] CONCEPT ENTROPY")
    print(f"    H(concepts) = {entropy:.4f} bits")
    print(f"    Max entropy = {math.log2(len(acset.concepts)):.4f} bits")
    print(f"    Efficiency  = {entropy / math.log2(len(acset.concepts)) * 100:.1f}%")
    
    # Hub concepts (most connected)
    print(f"\n[4] HUB CONCEPTS (most co-occurrences)")
    hub_scores = defaultdict(int)
    for rel in acset.concept_relations.values():
        hub_scores[rel['from']] += rel['weight']
    sorted_hubs = sorted(hub_scores.items(), key=lambda x: -x[1])[:10]
    for name, score in sorted_hubs:
        print(f"    {name:15} connections: {score}")
    
    # Strongest relations
    print(f"\n[5] STRONGEST RELATIONS")
    sorted_rels = sorted(acset.concept_relations.items(), key=lambda x: -x[1]['weight'])[:10]
    for _, rel in sorted_rels:
        print(f"    {rel['from']:12} ←({rel['weight']})→ {rel['to']}")
    
    # Thread clusters by concept
    print(f"\n[6] THREAD CLUSTERS")
    for concept in ['skill', 'MCP', 'GF3', 'parallelism', 'WORLD']:
        if concept in acset.concepts:
            thread_ids = acset.concepts[concept]['threads']
            print(f"    {concept}: {len(thread_ids)} threads")
    
    # Colored S-expression
    print(f"\n[7] COLORED S-EXPRESSION")
    sexpr = acset_to_sexpr(acset)
    print(f"    {sexpr}")
    
    # Message distribution
    print(f"\n[8] MESSAGE DISTRIBUTION")
    msg_counts = sorted([t['messages'] for t in acset.threads.values()], reverse=True)
    print(f"    Max:    {msg_counts[0]}")
    print(f"    Median: {msg_counts[len(msg_counts)//2]}")
    print(f"    Min:    {msg_counts[-1]}")
    print(f"    Total:  {sum(msg_counts)}")
    
    return {
        'threads': len(acset.threads),
        'total_messages': total_msgs,
        'concepts': len(acset.concepts),
        'relations': len(acset.concept_relations),
        'entropy': entropy,
        'top_concepts': sorted_concepts[:15],
        'hub_concepts': sorted_hubs,
        'strongest_relations': [(r['from'], r['weight'], r['to']) for _, r in sorted_rels],
        'colored_sexpr': sexpr.to_list()
    }


def generate_sql(acset: ThreadACSet) -> str:
    """Generate DuckDB SQL"""
    lines = [
        "-- Thread Relational ACSet Export",
        f"-- Generated: {time.strftime('%Y-%m-%d %H:%M:%S')}",
        f"-- Threads: {len(acset.threads)}, Concepts: {len(acset.concepts)}",
        "",
        "-- Create tables",
        "CREATE TABLE IF NOT EXISTS thread_concepts (thread_id VARCHAR, concept VARCHAR, PRIMARY KEY(thread_id, concept));",
        "CREATE TABLE IF NOT EXISTS concept_relations (concept_from VARCHAR, concept_to VARCHAR, weight INT);",
        ""
    ]
    
    # Thread-concept links
    for tid, concepts in acset.thread_concepts.items():
        for c in concepts:
            lines.append(f"INSERT INTO thread_concepts VALUES ('{tid}', '{c}');")
    
    lines.append("")
    
    # Concept relations
    for rel in acset.concept_relations.values():
        lines.append(f"INSERT INTO concept_relations VALUES ('{rel['from']}', '{rel['to']}', {rel['weight']});")
    
    return "\n".join(lines)


def generate_mermaid(acset: ThreadACSet) -> str:
    """Generate Mermaid diagram of concept network"""
    lines = ["graph LR"]
    
    # Add nodes for top concepts
    sorted_concepts = sorted(acset.concepts.items(), key=lambda x: -x[1]['frequency'])[:12]
    for name, data in sorted_concepts:
        safe_name = name.replace("-", "_")
        lines.append(f"    {safe_name}[{name}: {data['frequency']}]")
    
    # Add edges for strongest relations
    sorted_rels = sorted(acset.concept_relations.items(), key=lambda x: -x[1]['weight'])[:15]
    seen = set()
    for _, rel in sorted_rels:
        key = tuple(sorted([rel['from'], rel['to']]))
        if key not in seen:
            seen.add(key)
            f = rel['from'].replace("-", "_")
            t = rel['to'].replace("-", "_")
            lines.append(f"    {f} -->|{rel['weight']}| {t}")
    
    return "\n".join(lines)


# ============================================================================
# MAIN
# ============================================================================

def main():
    print("\n" + "="*70)
    print("  HYJAX THREAD RELATIONAL ANALYZER - FULL RUN")
    print("="*70)
    
    # Build ACSet
    print("\n[Building ACSet from 30 threads...]")
    acset = build_acset(THREADS)
    
    # Analyze
    result = analyze_and_report(acset)
    
    # Generate outputs
    print("\n[9] GENERATING OUTPUTS")
    
    # SQL
    sql = generate_sql(acset)
    with open('/Users/bob/ies/music-topos/lib/thread_full_export.sql', 'w') as f:
        f.write(sql)
    print(f"    Saved: thread_full_export.sql")
    
    # JSON
    with open('/Users/bob/ies/music-topos/lib/thread_full_analysis.json', 'w') as f:
        json.dump(result, f, indent=2, default=str)
    print(f"    Saved: thread_full_analysis.json")
    
    # Mermaid
    mermaid = generate_mermaid(acset)
    with open('/Users/bob/ies/music-topos/lib/thread_concept_network.mmd', 'w') as f:
        f.write(mermaid)
    print(f"    Saved: thread_concept_network.mmd")
    
    print("\n" + "="*70)
    print("  ANALYSIS COMPLETE")
    print("="*70 + "\n")
    
    # Print mermaid for visualization
    print("CONCEPT NETWORK (Mermaid):")
    print(mermaid)
    
    return acset, result


if __name__ == "__main__":
    main()
