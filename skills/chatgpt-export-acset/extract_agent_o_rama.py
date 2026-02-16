#!/usr/bin/env python3
"""
Extract agent-o-rama conversations from ChatGPT export into ACSet structure.
Uses py-acset pattern (dict-based schema) for Python compatibility.
"""
import json
from datetime import datetime
from pathlib import Path
from dataclasses import dataclass, field
from typing import Optional

# ACSet Schema Definition (py-acset style)
SCHEMA = {
    "objects": ["Conversation", "Message", "Author", "Attachment"],
    "morphisms": {
        "conversation_of": ("Message", "Conversation"),
        "author_of": ("Message", "Author"),
        "parent_msg": ("Message", "Message"),
        "attachment_of": ("Attachment", "Message"),
    },
    "attributes": {
        "Conversation": ["title", "create_time", "update_time", "conv_id"],
        "Message": ["msg_id", "content", "role", "create_time", "status"],
        "Author": ["name", "role"],
        "Attachment": ["file_id", "file_type", "file_path"],
    }
}

@dataclass
class PyACSet:
    """Simple ACSet implementation in Python."""
    schema: dict
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
        for attr, val in attrs.items():
            self.subparts[f"{ob}_{attr}"].append(val)
        return idx
    
    def set_subpart(self, morph: str, src: int, tgt: int):
        while len(self.subparts[morph]) <= src:
            self.subparts[morph].append(None)
        self.subparts[morph][src] = tgt
    
    def nparts(self, ob: str) -> int:
        return len(self.parts[ob])
    
    def to_dict(self) -> dict:
        return {"parts": self.parts, "subparts": self.subparts}
    
    def summary(self) -> str:
        lines = ["╭─────────────────────────────────────────────────╮",
                 "│     agent-o-rama ChatGPT Export ACSet          │",
                 "├─────────────────────────────────────────────────┤"]
        for ob in self.schema["objects"]:
            n = self.nparts(ob)
            lines.append(f"│  {ob:15} : {n:5} parts                  │")
        lines.append("╰─────────────────────────────────────────────────╯")
        return "\n".join(lines)


def extract_messages(mapping: dict) -> list:
    """Extract messages from ChatGPT mapping structure."""
    messages = []
    for node_id, node in mapping.items():
        if node.get("message"):
            msg = node["message"]
            content = ""
            if msg.get("content"):
                parts = msg["content"].get("parts", [])
                content = "\n".join(str(p) for p in parts if isinstance(p, str))
            
            messages.append({
                "id": msg.get("id"),
                "role": msg.get("author", {}).get("role", "unknown"),
                "content": content[:1000],  # Truncate for ACSet
                "create_time": msg.get("create_time"),
                "status": msg.get("status"),
                "parent": node.get("parent"),
            })
    return messages


def build_acset(conversations_file: str) -> PyACSet:
    """Build ACSet from ChatGPT export."""
    acset = PyACSet(schema=SCHEMA)
    
    with open(conversations_file) as f:
        convos = json.load(f)
    
    # Filter for agent-o-rama
    agent_o_rama_convos = []
    for c in convos:
        text = json.dumps(c).lower()
        if 'agent-o-rama' in text or 'redplanetlabs' in text:
            agent_o_rama_convos.append(c)
    
    print(f"Found {len(agent_o_rama_convos)} agent-o-rama conversations")
    
    # Track authors
    author_cache = {}
    
    for conv in agent_o_rama_convos:
        # Add conversation
        conv_idx = acset.add_part("Conversation",
            title=conv.get("title", ""),
            create_time=conv.get("create_time"),
            update_time=conv.get("update_time"),
            conv_id=conv.get("id", ""))
        
        # Extract messages
        messages = extract_messages(conv.get("mapping", {}))
        msg_id_to_idx = {}
        
        for msg in messages:
            # Get or create author
            role = msg["role"]
            if role not in author_cache:
                author_idx = acset.add_part("Author", name=role, role=role)
                author_cache[role] = author_idx
            
            # Add message
            msg_idx = acset.add_part("Message",
                msg_id=msg["id"] or "",
                content=msg["content"],
                role=role,
                create_time=msg["create_time"],
                status=msg["status"] or "")
            
            msg_id_to_idx[msg["id"]] = msg_idx
            
            # Set morphisms
            acset.set_subpart("conversation_of", msg_idx, conv_idx)
            acset.set_subpart("author_of", msg_idx, author_cache[role])
        
        # Set parent relationships
        for msg in messages:
            if msg["parent"] and msg["parent"] in msg_id_to_idx:
                src = msg_id_to_idx[msg["id"]]
                tgt = msg_id_to_idx[msg["parent"]]
                acset.set_subpart("parent_msg", src, tgt)
    
    return acset


def export_to_julia(acset: PyACSet, output_file: str):
    """Export ACSet to Julia-compatible format."""
    julia_code = '''# Auto-generated from ChatGPT export
using ACSets

@present SchChatGPT(FreeSchema) begin
    Conversation::Ob
    Message::Ob
    Author::Ob
    
    conversation_of::Hom(Message, Conversation)
    author_of::Hom(Message, Author)
    parent_msg::Hom(Message, Message)
    
    Title::AttrType
    Content::AttrType
    Role::AttrType
    Time::AttrType
    
    title::Attr(Conversation, Title)
    content::Attr(Message, Content)
    role::Attr(Author, Role)
end

# Data extracted: {n_conv} conversations, {n_msg} messages
'''.format(
        n_conv=acset.nparts("Conversation"),
        n_msg=acset.nparts("Message")
    )
    
    with open(output_file, 'w') as f:
        f.write(julia_code)
    print(f"Exported Julia schema to {output_file}")


if __name__ == "__main__":
    acset = build_acset("conversations.json")
    print(acset.summary())
    
    # Export
    with open("agent_o_rama_acset.json", "w") as f:
        json.dump(acset.to_dict(), f, indent=2, default=str)
    print("\nExported to agent_o_rama_acset.json")
    
    export_to_julia(acset, "agent_o_rama_schema.jl")
    
    # Print some stats
    print(f"\nConversation titles:")
    for i, title in enumerate(acset.subparts["Conversation_title"]):
        print(f"  {i+1}. {title}")
