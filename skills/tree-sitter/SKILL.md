---
name: tree-sitter
description: AST-based code analysis using tree-sitter. Use for parsing code structure, extracting symbols, finding patterns with tree-sitter queries, analyzing complexity, and understanding code architecture. Supports Python, JavaScript, TypeScript, Go, Rust, C, C++, Swift, Java, Kotlin, Julia, and more.
compatibility: Requires Python 3.10+, mcp-server-tree-sitter package installed.
---

# Tree-sitter Code Analysis

Intelligent code analysis via AST parsing with tree-sitter.

## When to Use

- Understanding code structure across multiple languages
- Extracting function/class definitions
- Finding code patterns with tree-sitter queries
- Analyzing code complexity
- Symbol extraction and dependency analysis

## Setup

MCP server configured in `~/.mcp.json`:
```json
{
  "tree-sitter": {
    "command": "python3",
    "args": ["-m", "mcp_server_tree_sitter.server"],
    "cwd": "/Users/alice/mcp-server-tree-sitter"
  }
}
```

## Usage Pattern

### 1. Register a Project First
```
register_project_tool(path="/path/to/project", name="my-project")
```

### 2. Explore Files
```
list_files(project="my-project", pattern="**/*.py")
get_file(project="my-project", path="src/main.py")
```

### 3. Analyze Structure
```
get_ast(project="my-project", path="src/main.py", max_depth=3)
get_symbols(project="my-project", path="src/main.py")
```

### 4. Search with Queries
```
find_text(project="my-project", pattern="function", file_pattern="**/*.py")
run_query(
  project="my-project",
  query='(function_definition name: (identifier) @function.name)',
  language="python"
)
```

### 5. Complexity Analysis
```
analyze_complexity(project="my-project", path="src/main.py")
```

## Available Tools

- **Project**: `register_project_tool`, `list_projects_tool`, `remove_project_tool`
- **Language**: `list_languages`, `check_language_available`
- **Files**: `list_files`, `get_file`, `get_file_metadata`
- **AST**: `get_ast`, `get_node_at_position`
- **Search**: `find_text`, `run_query`
- **Symbols**: `get_symbols`, `find_usage`
- **Analysis**: `analyze_project`, `get_dependencies`, `analyze_complexity`
- **Queries**: `get_query_template_tool`, `build_query`, `adapt_query`
- **Similar Code**: `find_similar_code`

## Supported Languages

Python, JavaScript, TypeScript, Go, Rust, C, C++, Swift, Java, Kotlin, Julia, APL, and many more via tree-sitter-language-pack.
