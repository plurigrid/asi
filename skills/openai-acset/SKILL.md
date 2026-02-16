---
metadata:
  interface_ports:
  - Related Skills
  - GF(3) Triads
trit: 0
color: '#10B981'
---
# openai-acset

> Compositional ACSet schema for OpenAI ChatGPT export traversal

**Version**: 1.0.0
**Trit**: 0 (ERGODIC - schema discovery coordinator)
**Color**: #10B981

## Anticipated Schema via Traversal

OpenAI's ChatGPT export has a **tree-structured mapping** where messages form a DAG via `parent`/`children` relationships. The compositional ACSet anticipates this structure.

## Discovered Schema (via traversal parsing)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         SchOpenAIExport                                      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  Conversation ◄─────────── conv_of ─────────── Node                         │
│       │                                          │                           │
│       │                                          ├── message ──► Message     │
│       │                                          │                  │        │
│       │                                          ├── parent ───────┐│        │
│       │                                          │        ▲        ││        │
│       │                                          └── children[]────┘│        │
│       │                                                              │        │
│       │                                          Message ────────────┘        │
│       │                                             │                         │
│       │                                             ├── author ──► Author     │
│       │                                             ├── content ─► Content    │
│       │                                             └── metadata ► Metadata   │
│       │                                                                       │
│  Content (polymorphic)                                                        │
│    ├── TextContent     {parts: [str]}                                         │
│    ├── CodeContent     {text: str, language: str}                             │
│    ├── ImageContent    {asset_pointer: str}                                   │
│    ├── ToolResult      {content_type: "execution_output"}                     │
│    └── UserContext     {user_profile: str, user_instructions: str}            │
│                                                                               │
│  Metadata (extensible)                                                        │
│    ├── model_slug, request_id, turn_exchange_id                               │
│    ├── citations[], content_references[]                                      │
│    ├── attachments[], search_queries[]                                        │
│    └── aggregate_result (for tool outputs)                                    │
│                                                                               │
└─────────────────────────────────────────────────────────────────────────────┘
```

## Julia ACSet Definition

```julia
using ACSets, Catlab

@present SchOpenAIExport(FreeSchema) begin
    # Objects (Obs)
    Conversation::Ob
    Node::Ob           # mapping entry (id → node)
    Message::Ob
    Author::Ob
    Content::Ob
    Attachment::Ob
    Citation::Ob
    SearchQuery::Ob
    
    # Morphisms (Homs) - tree structure
    conv_of::Hom(Node, Conversation)
    message_of::Hom(Node, Message)     # Node.message (nullable)
    parent_of::Hom(Node, Node)         # Node.parent (nullable, DAG)
    child_of::Hom(Node, Node)          # Node.children[] (inverse)
    
    # Message structure
    author_of::Hom(Message, Author)
    content_of::Hom(Message, Content)
    attachment_of::Hom(Attachment, Message)
    citation_of::Hom(Citation, Message)
    query_of::Hom(SearchQuery, Message)
    
    # Attributes
    ID::AttrType
    Text::AttrType
    Role::AttrType
    Time::AttrType
    Status::AttrType
    ContentType::AttrType
    ModelSlug::AttrType
    
    # Conversation attrs
    title::Attr(Conversation, Text)
    conv_id::Attr(Conversation, ID)
    create_time::Attr(Conversation, Time)
    update_time::Attr(Conversation, Time)
    current_node::Attr(Conversation, ID)
    gizmo_id::Attr(Conversation, ID)        # GPT custom
    
    # Node attrs
    node_id::Attr(Node, ID)
    
    # Message attrs
    msg_id::Attr(Message, ID)
    msg_status::Attr(Message, Status)
    end_turn::Attr(Message, Status)
    weight::Attr(Message, Time)             # Float
    recipient::Attr(Message, Text)
    
    # Author attrs
    role::Attr(Author, Role)                # user|assistant|system|tool
    name::Attr(Author, Text)                # tool name if role=tool
    
    # Content attrs (polymorphic via content_type)
    content_type::Attr(Content, ContentType)
    parts::Attr(Content, Text)              # JSON array as string
    text::Attr(Content, Text)               # for code/tool output
    
    # Metadata as attrs on Message
    model_slug::Attr(Message, ModelSlug)
    request_id::Attr(Message, ID)
    turn_exchange_id::Attr(Message, ID)
end

@acset_type OpenAIExport(SchOpenAIExport, 
    index=[:conv_of, :parent_of, :author_of, :role])
```

## Python py-acset Implementation

```python
SCHEMA_OPENAI = {
    "objects": [
        "Conversation", "Node", "Message", 
        "Author", "Content", "Attachment", 
        "Citation", "SearchQuery"
    ],
    "morphisms": {
        # Tree structure
        "conv_of": ("Node", "Conversation"),
        "message_of": ("Node", "Message"),
        "parent_of": ("Node", "Node"),
        
        # Message composition
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
```

## Specter-Style Navigation Paths

```julia
# Traverse from Conversation to all Messages
all_messages(acset, conv_id) = begin
    nodes = incident(acset, conv_id, :conv_of)
    [acset[n, :message_of] for n in nodes if acset[n, :message_of] !== nothing]
end

# Thread reconstruction: walk parent chain
function thread_path(acset, node_id)
    path = [node_id]
    while true
        parent = acset[node_id, :parent_of]
        parent === nothing && break
        pushfirst!(path, parent)
        node_id = parent
    end
    path
end

# All messages by role (user/assistant/tool)
by_role(acset, r) = begin
    authors = findall(==(r), acset[:role])
    [m for m in parts(acset, :Message) if acset[m, :author_of] ∈ authors]
end

# Tool invocations
tool_calls(acset) = by_role(acset, "tool")

# Search through content
search_content(acset, pattern) = begin
    matches = []
    for m in parts(acset, :Message)
        c = acset[m, :content_of]
        text = acset[c, :parts] * acset[c, :text]
        occursin(pattern, text) && push!(matches, m)
    end
    matches
end
```

## Compositional Decomposition

The OpenAI export decomposes into **three compositional layers**:

### Layer 1: Conversation Graph (DAG)
```
Node ──parent_of──► Node
  │
  └──children[]──► Node[]
```

### Layer 2: Message Content (Product)
```
Message = Author × Content × Metadata
```

### Layer 3: Polymorphic Content (Coproduct)
```
Content = TextContent + CodeContent + ImageContent + ToolResult + UserContext
```

## Comparison: OpenAI vs Anthropic vs Amp

| Dimension | OpenAI Export | Anthropic Claude | Amp Threads |
|-----------|---------------|------------------|-------------|
| **Structure** | Tree (DAG) | Linear | Linear |
| **Parent ref** | `parent: uuid` | Implicit | Implicit |
| **Branching** | `children: []` | None | None |
| **Tools** | `author.role=tool` | `tool_use` block | Tool blocks |
| **Attachments** | `metadata.attachments` | Inline | Inline |
| **Models** | `model_slug` | `model` | Model ID |

## Package Dependencies Discovery

From traversal, the export references:

| Package | Evidence | Morphism |
|---------|----------|----------|
| **geb** | `model_slug: "gpt-4"` context | Content → Anoma |
| **catlab** | Discussion content | Content → AlgebraicJulia |
| **nats** | Search queries | SearchQuery → Messaging |
| **emacs** | Tool outputs | Content → Editor |
| **agda** | HoTT discussions | Content → TypeTheory |

## Usage

```bash
# Extract with package filtering
python3 -c "
from openai_acset import build_openai_acset, filter_by_package
acset = build_openai_acset('conversations.json')
geb_convos = filter_by_package(acset, 'geb')
print(f'GEB conversations: {len(geb_convos)}')
"
```

## Files

| File | Purpose |
|------|---------|
| `openai_acset.py` | Full Python implementation |
| `openai_schema.jl` | Julia ACSet schema |
| `traverse_parser.py` | Schema discovery via traversal |

Base directory: file:///Users/bob/.claude/skills/openai-acset

---

## End-of-Skill Interface

## GF(3) Triads

```
three-match (-1) ⊗ openai-acset (0) ⊗ gay-mcp (+1) = 0 ✓        [Export coloring]
lispsyntax-acset (-1) ⊗ openai-acset (0) ⊗ specter-acset (+1) = 0 ✓  [Navigation]
temporal-coalgebra (-1) ⊗ openai-acset (0) ⊗ duckdb-timetravel (+1) = 0 ✓  [Versioning]
```

## Related Skills

- `chatgpt-export-acset` - Simpler extraction
- `acsets-algebraic-databases` - Core ACSet theory
- `specter-acset` - Bidirectional navigation
- `compositional-acset-comparison` - Schema comparison (DuckDB/LanceDB)
- `lispsyntax-acset` - Sexp bridge


---

## Autopoietic Marginalia

> **The interaction IS the skill improving itself.**

Every use of this skill is an opportunity for worlding:
- **MEMORY** (-1): Record what was learned
- **REMEMBERING** (0): Connect patterns to other skills  
- **WORLDING** (+1): Evolve the skill based on use



*Add Interaction Exemplars here as the skill is used.*
