#!/usr/bin/env python3
"""
Analyze Amp Threads with Relational Thinking (HyJAX patterns in Python)

Applies ThreadACSet schema to real thread data for relational analysis.
Outputs Colored S-expressions and DuckDB-compatible SQL.
"""

import json
import time
import re
from dataclasses import dataclass, field
from typing import Dict, List, Any, Tuple
from collections import defaultdict

# ============================================================================
# 1. THREAD ACSET SCHEMA (Category-Theoretic)
# ============================================================================

@dataclass
class ThreadACSet:
    """Algebraic database for thread relational structure"""
    
    # Objects (tables)
    threads: Dict[str, Dict] = field(default_factory=dict)
    messages: Dict[str, Dict] = field(default_factory=dict)
    files: Dict[str, Dict] = field(default_factory=dict)
    concepts: Dict[str, Dict] = field(default_factory=dict)
    
    # Morphisms (foreign keys / relations)
    thread_msg: Dict[str, str] = field(default_factory=dict)
    mentions: Dict[str, List[str]] = field(default_factory=dict)
    discusses: Dict[str, List[str]] = field(default_factory=dict)
    related: Dict[str, Dict] = field(default_factory=dict)
    
    # Attributes
    content: Dict[str, str] = field(default_factory=dict)
    timestamps: Dict[str, float] = field(default_factory=dict)
    info_gain: Dict[str, float] = field(default_factory=dict)
    
    def add_thread(self, thread_id: str, title: str, message_count: int = 0):
        self.threads[thread_id] = {
            'id': thread_id,
            'title': title,
            'message_count': message_count,
            'created': time.time()
        }
    
    def add_message(self, msg_id: str, thread_id: str, content: str, timestamp: float):
        self.messages[msg_id] = {'id': msg_id, 'thread': thread_id}
        self.thread_msg[msg_id] = thread_id
        self.content[msg_id] = content
        self.timestamps[msg_id] = timestamp
    
    def add_concept(self, concept_name: str):
        if concept_name not in self.concepts:
            self.concepts[concept_name] = {'name': concept_name, 'frequency': 0}
        self.concepts[concept_name]['frequency'] += 1
    
    def add_concept_relation(self, concept1: str, concept2: str, relation_type: str = 'co-occurs'):
        key = f"{concept1}→{concept2}"
        self.related[key] = {
            'from': concept1,
            'to': concept2,
            'type': relation_type
        }
    
    def add_file_mention(self, msg_id: str, file_path: str):
        if file_path not in self.files:
            self.files[file_path] = {'path': file_path}
        if msg_id not in self.mentions:
            self.mentions[msg_id] = []
        self.mentions[msg_id].append(file_path)


# ============================================================================
# 2. COLORED S-EXPRESSIONS
# ============================================================================

class ColoredSExpr:
    """S-expression with semantic color annotations"""
    
    def __init__(self, color: str, children: List):
        self.color = color
        self.children = children
    
    def __repr__(self):
        child_strs = []
        for c in self.children:
            if isinstance(c, ColoredSExpr):
                child_strs.append(repr(c))
            else:
                child_strs.append(str(c))
        return f"({self.color} {' '.join(child_strs)})"
    
    def to_list(self) -> List:
        return [self.color, [
            c.to_list() if isinstance(c, ColoredSExpr) else c
            for c in self.children
        ]]


def acset_to_colored_sexpr(acset: ThreadACSet) -> ColoredSExpr:
    """Convert ThreadACSet to Colored S-expression tree"""
    return ColoredSExpr(
        "acset-root-gold",
        [
            ColoredSExpr(
                "threads-red",
                [ColoredSExpr("thread-scarlet", [tid, t['title'][:40]])
                 for tid, t in acset.threads.items()]
            ),
            ColoredSExpr(
                "concepts-green",
                [ColoredSExpr("concept-emerald", [name, data['frequency']])
                 for name, data in sorted(acset.concepts.items(), 
                                         key=lambda x: -x[1]['frequency'])[:10]]
            ),
            ColoredSExpr(
                "files-blue",
                [ColoredSExpr("file-azure", [path[:50]])
                 for path in list(acset.files.keys())[:5]]
            ),
            ColoredSExpr(
                "relations-purple",
                [ColoredSExpr("relation-violet", [r['from'], r['type'], r['to']])
                 for r in list(acset.related.values())[:10]]
            )
        ]
    )


# ============================================================================
# 3. ENTROPY CALCULATION
# ============================================================================

import math

def compute_entropy(values: List[float]) -> float:
    """Compute Shannon entropy from value distribution"""
    if not values:
        return 0.0
    total = sum(values)
    if total == 0:
        return 0.0
    probs = [v / total for v in values if v > 0]
    return -sum(p * math.log2(p) for p in probs if p > 0)


def entropy_maximized_order(items: List[Dict], key_fn) -> List[Dict]:
    """Order items to maximize information gain at each step"""
    if not items:
        return []
    
    remaining = list(items)
    result = []
    seen_keys = set()
    
    while remaining:
        # Find item with most novel information
        best_idx = 0
        best_novelty = -1
        
        for i, item in enumerate(remaining):
            key = key_fn(item)
            novelty = 0 if key in seen_keys else 1
            # Add length-based novelty
            if 'content' in item:
                novelty += len(item.get('content', '')) / 1000
            if novelty > best_novelty:
                best_novelty = novelty
                best_idx = i
        
        best = remaining.pop(best_idx)
        result.append(best)
        seen_keys.add(key_fn(best))
    
    return result


# ============================================================================
# 4. CONCEPT EXTRACTION
# ============================================================================

# Key concepts to look for in thread analysis
CONCEPT_PATTERNS = {
    'HyJAX': r'\bhyjax\b|\bhy.*jax\b',
    'ACSet': r'\bacset\b|\bc-set\b|\balgebraic\s+database\b',
    'entropy': r'\bentropy\b|\binformation\s+gain\b',
    'ColoredShape': r'\bcolored\s*shape\b|\bcolored\s*tensor\b',
    'bidirectional': r'\bbidirectional\b|\bread.*write\b',
    'morphism': r'\bmorphism\b|\bhomomorphism\b',
    'pullback': r'\bpullback\b|\bpushout\b|\bcolimit\b',
    'operad': r'\boperad\b|\bdefoperad\b',
    'monadic': r'\bmonad\b|\bmonadic\b|\bdefmonadic\b',
    'ZX-calculus': r'\bzx\b|\bpyzx\b|\bquizx\b',
    'JAX': r'\bjax\b|\bjit\b|\bautodiff\b',
    'DuckDB': r'\bduckdb\b|\bducklake\b',
    'Gay.jl': r'\bgay\.jl\b|\bgf\(3\)\b|\bternary\b',
    'thread': r'\bthread\b|\bamp\s+thread\b',
    'relational': r'\brelational\b|\brelation\b',
    'category': r'\bcategory\b|\bfunctor\b|\btopos\b',
}


def extract_concepts(text: str) -> List[str]:
    """Extract concepts from text using patterns"""
    found = []
    text_lower = text.lower()
    for concept, pattern in CONCEPT_PATTERNS.items():
        if re.search(pattern, text_lower):
            found.append(concept)
    return found


def extract_file_mentions(text: str) -> List[str]:
    """Extract file paths from text"""
    # Match common file patterns
    patterns = [
        r'[\w/.-]+\.(?:hy|py|jl|sql|md|json|toml|yaml)',
        r'/Users/\S+',
        r'music-topos/\S+',
    ]
    files = []
    for pattern in patterns:
        files.extend(re.findall(pattern, text))
    return list(set(files))


# ============================================================================
# 5. THREAD ANALYZER
# ============================================================================

class ThreadRelationalAnalyzer:
    """Apply relational thinking to Amp threads"""
    
    def __init__(self):
        self.acset = ThreadACSet()
        self.analysis_history = []
    
    def ingest_thread(self, thread_data: Dict):
        """Ingest a thread from find_thread results"""
        thread_id = thread_data.get('id', f"T-{time.time()}")
        title = thread_data.get('title', 'Untitled')
        message_count = thread_data.get('messageCount', 0)
        matched_text = thread_data.get('matchedSearchText', '')
        
        # Add thread
        self.acset.add_thread(thread_id, title, message_count)
        
        # Create synthetic message from matched text
        if matched_text:
            msg_id = f"{thread_id}-matched"
            self.acset.add_message(msg_id, thread_id, matched_text, time.time())
            
            # Extract concepts
            concepts = extract_concepts(matched_text)
            for concept in concepts:
                self.acset.add_concept(concept)
                if msg_id not in self.acset.discusses:
                    self.acset.discusses[msg_id] = []
                self.acset.discusses[msg_id].append(concept)
            
            # Extract file mentions
            files = extract_file_mentions(matched_text)
            for file_path in files:
                self.acset.add_file_mention(msg_id, file_path)
            
            # Add concept relations (co-occurrence)
            for i, c1 in enumerate(concepts):
                for c2 in concepts[i+1:]:
                    self.acset.add_concept_relation(c1, c2, 'co-occurs')
        
        return thread_id
    
    def analyze(self) -> Dict:
        """Run full relational analysis"""
        print("\n" + "="*60)
        print("  THREAD RELATIONAL ANALYSIS (HyJAX Patterns)")
        print("="*60 + "\n")
        
        # 1. Summary
        print(f"[1] ACSet Summary:")
        print(f"    Threads:   {len(self.acset.threads)}")
        print(f"    Messages:  {len(self.acset.messages)}")
        print(f"    Concepts:  {len(self.acset.concepts)}")
        print(f"    Files:     {len(self.acset.files)}")
        print(f"    Relations: {len(self.acset.related)}")
        
        # 2. Concept frequency
        print(f"\n[2] Top Concepts:")
        sorted_concepts = sorted(
            self.acset.concepts.items(),
            key=lambda x: -x[1]['frequency']
        )[:10]
        for name, data in sorted_concepts:
            print(f"    {name}: {data['frequency']}")
        
        # 3. Entropy
        print(f"\n[3] Concept Entropy:")
        freqs = [c['frequency'] for c in self.acset.concepts.values()]
        entropy = compute_entropy(freqs)
        print(f"    H(concepts) = {entropy:.4f} bits")
        
        # 4. Colored S-expression
        print(f"\n[4] Colored S-Expression:")
        sexpr = acset_to_colored_sexpr(self.acset)
        print(f"    {sexpr}")
        
        # 5. Concept network
        print(f"\n[5] Concept Network (top relations):")
        for key, rel in list(self.acset.related.items())[:5]:
            print(f"    {rel['from']} --{rel['type']}--> {rel['to']}")
        
        result = {
            'timestamp': time.time(),
            'summary': {
                'threads': len(self.acset.threads),
                'messages': len(self.acset.messages),
                'concepts': len(self.acset.concepts),
                'files': len(self.acset.files),
                'relations': len(self.acset.related)
            },
            'concept_entropy': entropy,
            'top_concepts': sorted_concepts,
            'colored_sexpr': sexpr.to_list()
        }
        
        self.analysis_history.append(result)
        return result
    
    def to_sql(self) -> str:
        """Generate SQL INSERT statements for DuckDB"""
        lines = ["-- Thread ACSet SQL Export", f"-- Generated: {time.strftime('%Y-%m-%d %H:%M:%S')}", ""]
        
        # Objects
        for tid, thread in self.acset.threads.items():
            lines.append(f"INSERT INTO thread_acset_objects VALUES ('{tid}', 'Thread', '{json.dumps(thread)}', CURRENT_TIMESTAMP);")
        
        for cname, cdata in self.acset.concepts.items():
            lines.append(f"INSERT INTO thread_acset_objects VALUES ('concept:{cname}', 'Concept', '{json.dumps(cdata)}', CURRENT_TIMESTAMP);")
        
        # Morphisms
        for key, rel in self.acset.related.items():
            data = json.dumps({'type': rel['type']})
            lines.append(f"INSERT INTO thread_acset_morphisms VALUES ('{key}', 'related', 'concept:{rel['from']}', 'concept:{rel['to']}', '{data}', CURRENT_TIMESTAMP);")
        
        return "\n".join(lines)


# ============================================================================
# 6. SAMPLE THREAD DATA (from find_thread results)
# ============================================================================

SAMPLE_THREADS = [
    {
        "id": "T-019b4424-7b9e-7515-bb83-5514e2aefba8",
        "title": "Exploring relational thinking with HyJAX skills",
        "messageCount": 36,
        "matchedSearchText": "HyJAX skill exploration, relational thinking, ACSets, ColoredShape tensors, entropy interleaving, music-topos/lib/hy_skill_loader.hy, bidirectional learning"
    },
    {
        "id": "T-019b4412-7cbf-705c-81e8-1b84fb6d49c3",
        "title": "Use alife skill with Exa MCP for refined queries",
        "messageCount": 59,
        "matchedSearchText": "alife skill, ACSet integration, SchLenia as C-Set schema, entropy-driven diffusion, worlding_skill_omniglot_hyjax.hy"
    },
    {
        "id": "T-019b43f1-cae1-7043-9196-c6839793df4c",
        "title": "List of active workspace threads",
        "messageCount": 112,
        "matchedSearchText": "acsets-relational-thinking skill, DuckDB queries, thread operad, ACSet history view, GF(3) conservation"
    },
    {
        "id": "T-019b381e-cb1c-728e-973f-b8d2106767ed",
        "title": "DiscoPy interaction entropy harmonizer across 17 subagents",
        "messageCount": 175,
        "matchedSearchText": "hyjax JAX bindings for Hy, discohy DiscoPy integration, entropy maximizing, interaction entropy self-verification, categorical structure"
    },
    {
        "id": "T-019b43de-907c-7008-a545-57e8ff698498",
        "title": "Random walk spectral gap refinement process",
        "messageCount": 104,
        "matchedSearchText": "topos/topoi, functor/endofunctor, monad/comonad/operad, pullback/pushout/colimit, ACSet reference, open games"
    }
]


# ============================================================================
# 7. MAIN
# ============================================================================

def main():
    print("\n" + "="*60)
    print("  HYJAX THREAD RELATIONAL ANALYZER")
    print("  Applying relational thinking to Amp threads")
    print("="*60)
    
    # Create analyzer
    analyzer = ThreadRelationalAnalyzer()
    
    # Ingest threads
    print("\n[Ingesting threads...]")
    for thread_data in SAMPLE_THREADS:
        tid = analyzer.ingest_thread(thread_data)
        print(f"  + {tid}: {thread_data['title'][:40]}...")
    
    # Run analysis
    result = analyzer.analyze()
    
    # Generate SQL
    print("\n[6] SQL Export (sample):")
    sql = analyzer.to_sql()
    for line in sql.split('\n')[:10]:
        print(f"    {line}")
    print("    ...")
    
    # Save outputs
    print("\n[7] Saving outputs...")
    with open('/Users/bob/ies/music-topos/lib/thread_analysis_output.json', 'w') as f:
        json.dump(result, f, indent=2, default=str)
    print("    Saved: thread_analysis_output.json")
    
    with open('/Users/bob/ies/music-topos/lib/thread_acset_export.sql', 'w') as f:
        f.write(sql)
    print("    Saved: thread_acset_export.sql")
    
    print("\n" + "="*60)
    print("  ANALYSIS COMPLETE")
    print("="*60 + "\n")
    
    return analyzer


if __name__ == "__main__":
    main()
