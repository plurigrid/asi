# MCP-Tasks CLI Reference

This skill provides comprehensive CLI reference for the mcp-tasks command-line tool.

## Overview

The mcp-tasks CLI provides task management via command-line interface for scripting and automation. For agent workflows, use the MCP server instead.

## Installation

The CLI is distributed as a pre-built Babashka uberscript in this plugin:
```bash
plugins/mcp-tasks-cli/bin/mcp-tasks
```

Add to PATH or invoke directly:
```bash
# Add to PATH (example)
export PATH="$PATH:/path/to/plugins/mcp-tasks-cli/bin"

# Or invoke directly
/path/to/plugins/mcp-tasks-cli/bin/mcp-tasks --help
```

## Configuration Discovery

No `--config-path` required. The CLI automatically searches for `.mcp-tasks.edn`:
- Starts from current directory
- Traverses up directory tree
- Stops at filesystem root or when found

Example:
```bash
# Project structure:
# /project/.mcp-tasks.edn
# /project/src/

# Works from any subdirectory:
cd /project/src
mcp-tasks list  # Finds /project/.mcp-tasks.edn
```

## Commands

| Command | Purpose | Required Args | Key Options |
|---------|---------|---------------|-------------|
| `list` | Query tasks with filters | None | `--status`, `--category`, `--type`, `--parent-id`, `--task-id`, `--title-pattern`, `--limit`, `--unique` |
| `show` | Display single task | `--task-id` | `--format` |
| `add` | Create new task | `--category`, `--title` | `--description`, `--type`, `--parent-id`, `--prepend` |
| `complete` | Mark task complete | `--task-id` or `--title` | `--category`, `--completion-comment` |
| `update` | Update task fields | `--task-id` | `--title`, `--description`, `--design`, `--status`, `--category`, `--type`, `--parent-id`, `--meta`, `--relations` |
| `delete` | Delete task | `--task-id` or `--title-pattern` | None |

## Global Options

| Option | Values | Default | Description |
|--------|--------|---------|-------------|
| `--format` | `edn`, `json`, `human` | `edn` | Output format |
| `--help` | - | - | Show help message |

## Command Details

### list

Query tasks with optional filters.

**Usage:**
```bash
mcp-tasks list [options]
```

**Options:**

| Flag | Alias | Type | Description |
|------|-------|------|-------------|
| `--status` | `-s` | keyword | Filter by status: `open`, `closed`, `in-progress`, `blocked`, `any` |
| `--category` | `-c` | string | Filter by category name |
| `--type` | `-t` | keyword | Filter by type: `task`, `bug`, `feature`, `story`, `chore` |
| `--parent-id` | `-p` | integer | Filter by parent task ID |
| `--task-id` | - | integer | Filter by specific task ID |
| `--title-pattern` | `--title` | string | Filter by title pattern (regex or substring) |
| `--limit` | - | integer | Maximum tasks to return (default: 30) |
| `--unique` | - | boolean | Enforce 0 or 1 match (error if >1) |
| `--format` | - | keyword | Output format: `edn`, `json`, `human` |

**Examples:**
```bash
# List open tasks in human format
mcp-tasks list --status open --format human

# List all tasks for a category
mcp-tasks list --status any --category simple

# List story child tasks
mcp-tasks list --parent-id 31 --status open
```

### show

Display a single task by ID.

**Usage:**
```bash
mcp-tasks show --task-id <id> [options]
```

**Options:**

| Flag | Alias | Type | Required | Description |
|------|-------|------|----------|-------------|
| `--task-id` | `--id` | integer | Yes | Task ID to display |
| `--format` | - | keyword | No | Output format: `edn`, `json`, `human` |

**Examples:**
```bash
# Show task in EDN format
mcp-tasks show --task-id 42

# Show task in human-readable format
mcp-tasks show --id 42 --format human
```

### add

Create a new task.

**Usage:**
```bash
mcp-tasks add --category <name> --title <title> [options]
```

**Options:**

| Flag | Alias | Type | Required | Description |
|------|-------|------|----------|-------------|
| `--category` | `-c` | string | Yes | Task category (e.g., `simple`, `medium`, `large`) |
| `--title` | `-t` | string | Yes | Task title |
| `--description` | `-d` | string | No | Task description |
| `--type` | - | keyword | No | Task type (default: `task`). Options: `task`, `bug`, `feature`, `story`, `chore` |
| `--parent-id` | `-p` | integer | No | Parent task ID (for child tasks) |
| `--prepend` | - | boolean | No | Add task at beginning instead of end |
| `--format` | - | keyword | No | Output format: `edn`, `json`, `human` |

**Examples:**
```bash
# Create simple task
mcp-tasks add --category simple --title "Fix parser bug"

# Create task with description
mcp-tasks add -c medium -t "Add auth" -d "Implement JWT auth"

# Create child task
mcp-tasks add --category simple --title "Subtask" --parent-id 31
```

### complete

Mark a task as complete and move to archive.

**Usage:**
```bash
mcp-tasks complete (--task-id <id> | --title <pattern>) [options]
```

**Options:**

| Flag | Alias | Type | Required | Description |
|------|-------|------|----------|-------------|
| `--task-id` | `--id` | integer | * | Task ID to complete |
| `--title` | `-t` | string | * | Task title pattern (alternative to task-id) |
| `--category` | `-c` | string | No | Task category (for verification) |
| `--completion-comment` | `--comment` | string | No | Optional completion comment |
| `--format` | - | keyword | No | Output format: `edn`, `json`, `human` |

\* At least one of `--task-id` or `--title` required.

**Examples:**
```bash
# Complete by ID
mcp-tasks complete --task-id 42

# Complete by title with comment
mcp-tasks complete --title "Fix bug" --comment "Fixed via PR #123"

# Complete with category verification
mcp-tasks complete --id 42 --category simple
```

### update

Update task fields.

**Usage:**
```bash
mcp-tasks update --task-id <id> [options]
```

**Options:**

| Flag | Alias | Type | Required | Description |
|------|-------|------|----------|-------------|
| `--task-id` | `--id` | integer | Yes | Task ID to update |
| `--title` | `-t` | string | No | New task title |
| `--description` | `-d` | string | No | New task description |
| `--design` | - | string | No | New task design notes |
| `--status` | `-s` | keyword | No | New status: `open`, `closed`, `in-progress`, `blocked` |
| `--category` | `-c` | string | No | New task category |
| `--type` | - | keyword | No | New task type: `task`, `bug`, `feature`, `story`, `chore` |
| `--parent-id` | `-p` | integer/string | No | New parent task ID (pass `"null"` to remove) |
| `--meta` | - | JSON string | No | New metadata as JSON object (replaces entire map) |
| `--relations` | - | JSON string | No | New relations as JSON array (replaces entire vector) |
| `--format` | - | keyword | No | Output format: `edn`, `json`, `human` |

**Examples:**
```bash
# Update status
mcp-tasks update --task-id 42 --status in-progress

# Update title and description
mcp-tasks update --id 42 --title "New title" --description "New desc"

# Update metadata
mcp-tasks update --task-id 42 --meta '{"priority":"high"}'

# Remove parent relationship
mcp-tasks update --task-id 42 --parent-id "null"
```

### delete

Delete a task from tasks.ednl (archives to complete.ednl with `:status :deleted`).

**Usage:**
```bash
mcp-tasks delete (--task-id <id> | --title-pattern <pattern>) [options]
```

**Options:**

| Flag | Alias | Type | Required | Description |
|------|-------|------|----------|-------------|
| `--task-id` | `--id` | integer | * | Task ID to delete |
| `--title-pattern` | `--title` | string | * | Title pattern to match (alternative to task-id) |
| `--format` | - | keyword | No | Output format: `edn`, `json`, `human` |

\* At least one of `--task-id` or `--title-pattern` required.

**Constraints:**
- Cannot delete tasks with non-closed children (must complete or delete children first)

**Examples:**
```bash
# Delete by ID
mcp-tasks delete --task-id 42

# Delete by title pattern
mcp-tasks delete --title-pattern "old-task"

# Delete with human-readable output
mcp-tasks delete --id 42 --format human
```

## Output Formats

### EDN (Default)

Clojure EDN format suitable for programmatic consumption:
```clojure
{:tasks [{:id 42 :title "Fix bug" :status :open ...}]
 :metadata {:open-task-count 5 :returned-count 1}}
```

### JSON

JSON format for integration with non-Clojure tools:
```json
{
  "tasks": [{"id": 42, "title": "Fix bug", "status": "open", ...}],
  "metadata": {"open_task_count": 5, "returned_count": 1}
}
```

### Human

Human-readable tabular format:
```
Tasks (1 found, showing 1):

ID  | Status | Category | Type | Title
----|--------|----------|------|--------
42  | open   | simple   | task | Fix bug

Metadata:
  Open tasks: 5
  Returned: 1
```

## Common Workflows

### Query and Display
```bash
# Find tasks by status and category
mcp-tasks list --status open --category medium --format human

# Show specific task details
mcp-tasks show --task-id 42 --format human
```

### Create and Manage Tasks
```bash
# Create simple task
mcp-tasks add --category simple --title "Fix parser"

# Create story with child tasks
mcp-tasks add --category large --title "User auth" --type story
mcp-tasks add --category medium --title "Login" --parent-id 100

# Update task status
mcp-tasks update --task-id 101 --status in-progress

# Complete task with comment
mcp-tasks complete --task-id 101 --comment "Implemented"
```

### Scripting Examples
```bash
# Get open task count (JSON + jq)
mcp-tasks list --status open --format json | jq '.metadata.open_task_count'

# List all story tasks
mcp-tasks list --type story --status any --format human

# Batch update tasks (shell loop)
for id in 42 43 44; do
  mcp-tasks update --task-id $id --status closed
done
```

## File Locations

The CLI operates on these files within the `.mcp-tasks/` directory:

| File | Purpose |
|------|---------|
| `.mcp-tasks.edn` | Configuration file (searched automatically) |
| `.mcp-tasks/tasks.ednl` | Incomplete tasks |
| `.mcp-tasks/complete.ednl` | Completed/deleted tasks archive |
| `.mcp-tasks/prompts/<category>.md` | Category-specific prompts (not used by CLI) |

## CLI vs MCP Server

**Use CLI for:**
- Shell scripting and automation
- CI/CD pipelines
- Batch operations
- Quick queries from terminal
- Integration with non-agent tools

**Use MCP Server for:**
- Agent-driven task execution
- Interactive task refinement
- Workflow automation with prompts
- Story-based development
- Git integration (branches, worktrees)

The CLI and MCP server operate on the same `.mcp-tasks/` data files and can be used interchangeably.

## Error Handling

**Configuration not found:**
```
Error: Could not find .mcp-tasks.edn in current directory or any parent directory
```
Solution: Initialize project with `.mcp-tasks.edn` or run from correct directory.

**Unknown option:**
```
Unknown option: --invalid. Use --help to see valid options.
```
Solution: Check command-specific help with `mcp-tasks <command> --help`.

**Invalid format:**
```
Invalid format: xml. Must be one of: edn, json, human
```
Solution: Use one of the supported format values.

**Missing required argument:**
```
Required option: --task-id (or --id)
```
Solution: Provide all required arguments for the command.

**Task not found:**
```
Error: No task found with task-id: 999
```
Solution: Verify task ID exists using `mcp-tasks list`.

## Limitations

- No interactive prompts (use flags for all input)
- No task execution workflows (use MCP server)
- No git integration (use MCP server)
- No worktree management (use MCP server)
- No branch automation (use MCP server)

## Version

Check version in `plugins/mcp-tasks-cli/.claude-plugin/plugin.json`.
