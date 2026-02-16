#!/usr/bin/env python3
"""
L-Space Causality Graph - P2 Implementation
Extract causality structure from code/text using tree-sitter

Usage:
    python causality_graph.py file.py --lang python
    python causality_graph.py file.txt --lang text
    
Output: JSON with dependency graph + GF(3) analysis
"""

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from typing import Optional

@dataclass
class CausalNode:
    id: str
    label: str
    node_type: str  # function, variable, statement, concept
    line: Optional[int] = None
    trit: int = 0  # -1=sink, 0=pass-through, +1=source

@dataclass
class CausalEdge:
    source: str
    target: str
    edge_type: str  # calls, assigns, imports, causes

@dataclass
class CausalityGraph:
    nodes: list[CausalNode] = field(default_factory=list)
    edges: list[CausalEdge] = field(default_factory=list)
    
    def add_node(self, node: CausalNode):
        if node.id not in [n.id for n in self.nodes]:
            self.nodes.append(node)
    
    def add_edge(self, edge: CausalEdge):
        self.edges.append(edge)
    
    def compute_trits(self):
        """Assign trits based on in/out degree"""
        in_degree = {n.id: 0 for n in self.nodes}
        out_degree = {n.id: 0 for n in self.nodes}
        
        for e in self.edges:
            out_degree[e.source] = out_degree.get(e.source, 0) + 1
            in_degree[e.target] = in_degree.get(e.target, 0) + 1
        
        for n in self.nodes:
            ins = in_degree.get(n.id, 0)
            outs = out_degree.get(n.id, 0)
            if outs > ins:
                n.trit = 1   # Source (+1)
            elif ins > outs:
                n.trit = -1  # Sink (-1)
            else:
                n.trit = 0   # Pass-through (0)
    
    def gf3_check(self) -> dict:
        """Verify GF(3) conservation"""
        self.compute_trits()
        trits = [n.trit for n in self.nodes]
        return {
            "distribution": {
                "source": trits.count(1),
                "passthrough": trits.count(0),
                "sink": trits.count(-1)
            },
            "sum": sum(trits),
            "balanced": sum(trits) % 3 == 0
        }
    
    def to_dict(self) -> dict:
        return {
            "nodes": [{"id": n.id, "label": n.label, "type": n.node_type, 
                       "line": n.line, "trit": n.trit} for n in self.nodes],
            "edges": [{"source": e.source, "target": e.target, 
                       "type": e.edge_type} for e in self.edges],
            "gf3": self.gf3_check()
        }

# --- Tree-sitter Python Parser ---
def parse_python_treesitter(code: str) -> CausalityGraph:
    """Extract causality from Python using tree-sitter"""
    try:
        import tree_sitter_python as tspython
        from tree_sitter import Language, Parser
    except ImportError:
        print("pip install tree-sitter tree-sitter-python", file=sys.stderr)
        return parse_python_regex(code)
    
    PY_LANGUAGE = Language(tspython.language())
    parser = Parser(PY_LANGUAGE)
    tree = parser.parse(bytes(code, "utf8"))
    
    graph = CausalityGraph()
    
    def walk(node, depth=0):
        if node.type == "function_definition":
            name_node = node.child_by_field_name("name")
            if name_node:
                name = code[name_node.start_byte:name_node.end_byte]
                graph.add_node(CausalNode(
                    id=f"func:{name}",
                    label=name,
                    node_type="function",
                    line=node.start_point[0] + 1
                ))
        
        elif node.type == "call":
            func_node = node.child_by_field_name("function")
            if func_node:
                name = code[func_node.start_byte:func_node.end_byte]
                # Find enclosing function
                parent = node.parent
                while parent and parent.type != "function_definition":
                    parent = parent.parent
                if parent:
                    parent_name = parent.child_by_field_name("name")
                    if parent_name:
                        caller = code[parent_name.start_byte:parent_name.end_byte]
                        graph.add_node(CausalNode(
                            id=f"func:{name}",
                            label=name,
                            node_type="function"
                        ))
                        graph.add_edge(CausalEdge(
                            source=f"func:{caller}",
                            target=f"func:{name}",
                            edge_type="calls"
                        ))
        
        elif node.type == "import_statement" or node.type == "import_from_statement":
            for child in node.children:
                if child.type in ("dotted_name", "aliased_import"):
                    name = code[child.start_byte:child.end_byte].split()[0]
                    graph.add_node(CausalNode(
                        id=f"import:{name}",
                        label=name,
                        node_type="import",
                        line=node.start_point[0] + 1
                    ))
        
        for child in node.children:
            walk(child, depth + 1)
    
    walk(tree.root_node)
    return graph

# --- Regex Fallback ---
def parse_python_regex(code: str) -> CausalityGraph:
    """Fallback: extract Python structure with regex"""
    graph = CausalityGraph()
    
    # Functions
    for match in re.finditer(r'^def\s+(\w+)', code, re.MULTILINE):
        graph.add_node(CausalNode(
            id=f"func:{match.group(1)}",
            label=match.group(1),
            node_type="function",
            line=code[:match.start()].count('\n') + 1
        ))
    
    # Calls within functions
    func_pattern = r'def\s+(\w+)[^:]*:(.*?)(?=\ndef\s|\Z)'
    for match in re.finditer(func_pattern, code, re.DOTALL):
        caller = match.group(1)
        body = match.group(2)
        for call in re.finditer(r'\b(\w+)\s*\(', body):
            callee = call.group(1)
            if callee not in ('if', 'for', 'while', 'print', 'return'):
                graph.add_node(CausalNode(
                    id=f"func:{callee}",
                    label=callee,
                    node_type="function"
                ))
                graph.add_edge(CausalEdge(
                    source=f"func:{caller}",
                    target=f"func:{callee}",
                    edge_type="calls"
                ))
    
    # Imports
    for match in re.finditer(r'^(?:from\s+(\w+)|import\s+(\w+))', code, re.MULTILINE):
        name = match.group(1) or match.group(2)
        graph.add_node(CausalNode(
            id=f"import:{name}",
            label=name,
            node_type="import"
        ))
    
    return graph

# --- Text Causality ---
def parse_text_causality(text: str) -> CausalityGraph:
    """Extract causal relationships from natural language"""
    graph = CausalityGraph()
    
    # Causal patterns
    patterns = [
        (r'(\w+)\s+(?:causes?|leads?\s+to|results?\s+in)\s+(\w+)', 'causes'),
        (r'(\w+)\s+(?:because|since|as)\s+(\w+)', 'because'),
        (r'if\s+(\w+).*?then\s+(\w+)', 'implies'),
        (r'(\w+)\s+(?:therefore|thus|hence|so)\s+(\w+)', 'therefore'),
        (r'(\w+)\s+depends\s+on\s+(\w+)', 'depends'),
    ]
    
    for pattern, edge_type in patterns:
        for match in re.finditer(pattern, text, re.IGNORECASE):
            source, target = match.group(1), match.group(2)
            graph.add_node(CausalNode(id=source.lower(), label=source, node_type="concept"))
            graph.add_node(CausalNode(id=target.lower(), label=target, node_type="concept"))
            graph.add_edge(CausalEdge(source=source.lower(), target=target.lower(), edge_type=edge_type))
    
    return graph

# --- Main ---
def main():
    parser = argparse.ArgumentParser(description="L-Space Causality Graph")
    parser.add_argument("file", help="File to analyze")
    parser.add_argument("-l", "--lang", default="auto", 
                        choices=["python", "text", "auto"])
    parser.add_argument("--dot", action="store_true", help="Output Graphviz DOT")
    
    args = parser.parse_args()
    
    with open(args.file) as f:
        content = f.read()
    
    # Auto-detect language
    if args.lang == "auto":
        if args.file.endswith(".py"):
            args.lang = "python"
        else:
            args.lang = "text"
    
    if args.lang == "python":
        graph = parse_python_treesitter(content)
    else:
        graph = parse_text_causality(content)
    
    graph.compute_trits()
    
    if args.dot:
        print("digraph causality {")
        print("  rankdir=LR;")
        for n in graph.nodes:
            color = {1: "green", 0: "gray", -1: "red"}[n.trit]
            print(f'  "{n.id}" [label="{n.label}" color={color}];')
        for e in graph.edges:
            print(f'  "{e.source}" -> "{e.target}" [label="{e.edge_type}"];')
        print("}")
    else:
        print(json.dumps(graph.to_dict(), indent=2))

if __name__ == "__main__":
    main()
