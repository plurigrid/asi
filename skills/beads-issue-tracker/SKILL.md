---
name: beads-issue-tracker
description: |
  Guide for using Beads (bd), a dependency-aware issue tracker for AI agents. Issues chained together like beads.
license: MIT
metadata:
  author: Stakpak <team@stakpak.dev>
  version: 1.0.11
---

# Beads Issue Tracker (bd)

Issues chained together like beads. A lightweight issue tracker with first-class dependency support.

## Getting Started

```bash
bd init                      # Initialize bd in your project
bd init --prefix api         # Initialize with custom prefix (api-1, api-2)
```

## Creating Issues

```bash
bd create "Fix login bug"
bd create "Add auth" -p 0 -t feature
bd create "Write tests" -d "Unit tests for auth" --assignee alice
```

## Viewing Issues

```bash
bd list                      # List all issues
bd list --status open        # List by status
bd list --priority 0         # List by priority (0-4, 0=highest)
bd show bd-1                 # Show issue details
```

## Managing Dependencies

```bash
bd dep add bd-1 bd-2         # Add dependency (bd-2 blocks bd-1)
bd dep tree bd-1             # Visualize dependency tree
bd dep cycles                # Detect circular dependencies
```

**Dependency Types:**
- `blocks` - Task B must complete before task A
- `related` - Soft connection, doesn't block progress
- `parent-child` - Epic/subtask hierarchical relationship
- `discovered-from` - Auto-created when AI discovers related work

## Ready Work

```bash
bd ready                     # Show issues ready to work on
```

Ready = status is 'open' AND no blocking dependencies. Perfect for agents to claim next work!

## Updating Issues

```bash
bd update bd-1 --status in_progress
bd update bd-1 --priority 0
bd update bd-1 --assignee bob
```

## Closing Issues

```bash
bd close bd-1
bd close bd-2 bd-3 --reason "Fixed in PR #42"
```

## Database Location

bd automatically discovers your database:
1. `--db /path/to/db.db` flag
2. `$BEADS_DB` environment variable
3. `.beads/*.db` in current directory or ancestors
4. `~/.beads/default.db` as fallback

## Agent Integration

bd is designed for AI-supervised workflows:
- Agents create issues when discovering new work
- `bd ready` shows unblocked work ready to claim
- Use `--json` flags for programmatic parsing
- Dependencies prevent agents from duplicating effort

## Git Workflow (Auto-Sync)

bd automatically keeps git in sync:
- Export to JSONL after CRUD operations (5s debounce)
- Import from JSONL when newer than DB (after git pull)
- Works seamlessly across machines and team members

Disable with: `--no-auto-flush` or `--no-auto-import`

## References

- [GitHub Repository](https://github.com/steveyegge/beads)
- [Agent Instructions](https://github.com/steveyegge/beads/blob/main/AGENT_INSTRUCTIONS.md)