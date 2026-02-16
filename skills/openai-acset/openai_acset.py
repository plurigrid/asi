#!/usr/bin/env python3
"""
OpenAI ChatGPT Export → Compositional ACSet
Anticipates schema via traversal parsing.
"""
import json
from dataclasses import dataclass, field
from typing import Optional, Any
from pathlib import Path

# Full OpenAI Export Schema
SCHEMA_OPENAI = {
    "objects": [
        "Conversation", "Node", "Message", 
        "Author", "Content", "Attachment", 
        "Citation", "SearchQuery"
    ],
    "morphisms": {
        "conv_of": ("Node", "Conversation"),
        "message_of": ("Node", "Message"),
        "parent_of": ("Node", "Node"),
        "author_of": ("Message", "Author"),
        "content_of": ("Message", "Content"),
        "attachment_of": ("Attachment", "Message"),
        "citation_of": ("Citation", "Message"),
        "query_of": ("SearchQuery", "Message"),
    },
    "attributes": {
        "Conversation": ["title", "conv_id", "create_time", "update_time", "current_node", "gizmo_id"],
        "Node": ["node_id"],
        "Message": ["msg_id", "status", "end_turn", "weight", "recipient", "model_slug", "request_id"],
        "Author": ["role", "name"],
        "Content": ["content_type", "parts", "text"],
        "Attachment": ["file_id", "file_name", "file_type"],
        "Citation": ["url", "title", "snippet"],
        "SearchQuery": ["query"],
    }
}


@dataclass
class OpenAIACSet:
    """Compositional ACSet for OpenAI exports."""
    schema: dict = field(default_factory=lambda: SCHEMA_OPENAI)
    parts: dict = field(default_factory=dict)
    subparts: dict = field(default_factory=dict)
    
    def __post_init__(self):
        for ob in self.schema["objects"]:
            self.parts[ob] = []
        for morph in self.schema["morphisms"]:
            self.subparts[morph] = []
        for ob, attrs in self.schema["attributes"].items():
            for attr in attrs:
                self.subparts[f"{ob}_{attr}"] = []
    
    def add_part(self, ob: str, **attrs) -> int:
        idx = len(self.parts[ob])
        self.parts[ob].append(idx)
        for attr in self.schema["attributes"].get(ob, []):
            val = attrs.get(attr)
            self.subparts[f"{ob}_{attr}"].append(val)
        return idx
    
    def set_subpart(self, morph: str, src: int, tgt: int):
        while len(self.subparts[morph]) <= src:
            self.subparts[morph].append(None)
        self.subparts[morph][src] = tgt
    
    def nparts(self, ob: str) -> int:
        return len(self.parts[ob])
    
    def incident(self, tgt: int, morph: str) -> list:
        """Find all sources that map to target via morphism."""
        return [i for i, t in enumerate(self.subparts[morph]) if t == tgt]
    
    def summary(self) -> str:
        lines = [
            "╔═══════════════════════════════════════════════════════════════╗",
            "║              OpenAI ChatGPT Export ACSet                      ║",
            "╠═══════════════════════════════════════════════════════════════╣",
        ]
        for ob in self.schema["objects"]:
            n = self.nparts(ob)
            if n > 0:
                lines.append(f"║  {ob:15} : {n:6} parts                          ║")
        lines.append("╚═══════════════════════════════════════════════════════════════╝")
        return "\n".join(lines)


def build_openai_acset(conversations_file: str, filter_pattern: str = None) -> OpenAIACSet:
    """Build full ACSet from ChatGPT export."""
    acset = OpenAIACSet()
    
    with open(conversations_file) as f:
        convos = json.load(f)
    
    if filter_pattern:
        convos = [c for c in convos if filter_pattern.lower() in json.dumps(c).lower()]
    
    print(f"Processing {len(convos)} conversations...")
    
    # Cache for deduplication
    author_cache = {}
    
    for conv in convos:
        # Add Conversation
        conv_idx = acset.add_part("Conversation",
            title=conv.get("title", ""),
            conv_id=conv.get("conversation_id", conv.get("id", "")),
            create_time=conv.get("create_time"),
            update_time=conv.get("update_time"),
            current_node=conv.get("current_node"),
            gizmo_id=conv.get("gizmo_id"))
        
        mapping = conv.get("mapping", {})
        node_id_to_idx = {}
        
        # First pass: create all Nodes
        for node_id, node_data in mapping.items():
            node_idx = acset.add_part("Node", node_id=node_id)
            node_id_to_idx[node_id] = node_idx
            acset.set_subpart("conv_of", node_idx, conv_idx)
        
        # Second pass: set parent relationships and create Messages
        for node_id, node_data in mapping.items():
            node_idx = node_id_to_idx[node_id]
            
            # Parent relationship
            parent_id = node_data.get("parent")
            if parent_id and parent_id in node_id_to_idx:
                acset.set_subpart("parent_of", node_idx, node_id_to_idx[parent_id])
            
            # Message (if exists)
            msg_data = node_data.get("message")
            if msg_data:
                # Author
                author_data = msg_data.get("author", {})
                role = author_data.get("role", "unknown")
                name = author_data.get("name")
                author_key = (role, name)
                
                if author_key not in author_cache:
                    author_idx = acset.add_part("Author", role=role, name=name)
                    author_cache[author_key] = author_idx
                author_idx = author_cache[author_key]
                
                # Content
                content_data = msg_data.get("content", {})
                content_type = content_data.get("content_type", "text")
                parts = json.dumps(content_data.get("parts", []))[:2000]
                text = content_data.get("text", "")[:2000]
                
                content_idx = acset.add_part("Content",
                    content_type=content_type,
                    parts=parts,
                    text=text)
                
                # Message
                metadata = msg_data.get("metadata", {})
                msg_idx = acset.add_part("Message",
                    msg_id=msg_data.get("id", ""),
                    status=msg_data.get("status"),
                    end_turn=msg_data.get("end_turn"),
                    weight=msg_data.get("weight"),
                    recipient=msg_data.get("recipient"),
                    model_slug=metadata.get("model_slug"),
                    request_id=metadata.get("request_id"))
                
                # Set morphisms
                acset.set_subpart("message_of", node_idx, msg_idx)
                acset.set_subpart("author_of", msg_idx, author_idx)
                acset.set_subpart("content_of", msg_idx, content_idx)
                
                # Citations
                for cit in metadata.get("citations", []):
                    cit_idx = acset.add_part("Citation",
                        url=cit.get("url", ""),
                        title=cit.get("title", ""),
                        snippet=cit.get("snippet", ""))
                    acset.set_subpart("citation_of", cit_idx, msg_idx)
                
                # Search queries
                for query in metadata.get("search_queries", []):
                    q_idx = acset.add_part("SearchQuery", query=query)
                    acset.set_subpart("query_of", q_idx, msg_idx)
                
                # Attachments
                for att in metadata.get("attachments", []):
                    att_idx = acset.add_part("Attachment",
                        file_id=att.get("id", ""),
                        file_name=att.get("name", ""),
                        file_type=att.get("mimeType", ""))
                    acset.set_subpart("attachment_of", att_idx, msg_idx)
    
    return acset


def filter_by_package(acset: OpenAIACSet, package: str) -> list:
    """Find conversations mentioning a package."""
    matches = []
    pattern = package.lower()
    
    for conv_idx in acset.parts["Conversation"]:
        # Get all nodes in this conversation
        nodes = acset.incident(conv_idx, "conv_of")
        
        for node_idx in nodes:
            msg_idx = acset.subparts["message_of"][node_idx] if node_idx < len(acset.subparts["message_of"]) else None
            if msg_idx is not None:
                content_idx = acset.subparts["content_of"][msg_idx] if msg_idx < len(acset.subparts["content_of"]) else None
                if content_idx is not None:
                    parts = acset.subparts["Content_parts"][content_idx] or ""
                    text = acset.subparts["Content_text"][content_idx] or ""
                    if pattern in parts.lower() or pattern in text.lower():
                        matches.append(conv_idx)
                        break
    
    return list(set(matches))


def thread_path(acset: OpenAIACSet, node_idx: int) -> list:
    """Reconstruct thread by walking parent chain."""
    path = [node_idx]
    current = node_idx
    
    while True:
        if current >= len(acset.subparts["parent_of"]):
            break
        parent = acset.subparts["parent_of"][current]
        if parent is None:
            break
        path.insert(0, parent)
        current = parent
    
    return path


def by_role(acset: OpenAIACSet, role: str) -> list:
    """Get all messages by author role."""
    matching_authors = [
        i for i, r in enumerate(acset.subparts["Author_role"]) 
        if r == role
    ]
    
    messages = []
    for msg_idx, author_idx in enumerate(acset.subparts["author_of"]):
        if author_idx in matching_authors:
            messages.append(msg_idx)
    
    return messages


if __name__ == "__main__":
    import sys
    
    conv_file = sys.argv[1] if len(sys.argv) > 1 else "conversations.json"
    filter_pkg = sys.argv[2] if len(sys.argv) > 2 else None
    
    acset = build_openai_acset(conv_file, filter_pkg)
    print(acset.summary())
    
    # Package analysis
    packages = ['geb', 'anoma', 'catlab', 'agda', 'nats', 'emacs', 'racket', 'idris', 'sbcl']
    print("\n📦 Package mentions:")
    for pkg in packages:
        matches = filter_by_package(acset, pkg)
        if matches:
            print(f"  {pkg.upper()}: {len(matches)} conversations")
    
    # Role distribution
    print("\n👤 Messages by role:")
    for role in ['user', 'assistant', 'system', 'tool']:
        msgs = by_role(acset, role)
        if msgs:
            print(f"  {role}: {len(msgs)} messages")
    
    # Export
    output = {
        "parts": {k: list(v) for k, v in acset.parts.items()},
        "subparts": {k: list(v) for k, v in acset.subparts.items()},
    }
    
    out_file = "openai_full_acset.json"
    with open(out_file, "w") as f:
        json.dump(output, f, default=str)
    print(f"\n💾 Exported to {out_file}")
