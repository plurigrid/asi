# MCP-Tasks Story and Task Management

This skill provides guidance on using the mcp-tasks MCP server for task and story management.

## Overview

The mcp-tasks MCP server provides:
- **Tools**: For managing tasks (create, update, select, complete, delete)
- **Prompts**: Workflow templates for executing tasks and stories
- **Resources**: Category instructions and execution state

## MCP Tools

### Task Query and Modification

| Tool | Purpose | Key Parameters |
|------|---------|---------------|
| `select-tasks` | Query tasks with filtering | `task-id`, `parent-id`, `category`, `type`, `status`, `title-pattern`, `limit`, `unique` |
| `add-task` | Create new task | Required: `category`, `title`. Optional: `description`, `parent-id`, `type`, `prepend` |
| `update-task` | Update task fields | Required: `task-id`. Optional: `title`, `description`, `design`, `category`, `type`, `status`, `parent-id`, `meta`, `relations` |
| `complete-task` | Mark complete and archive | Identify by `task-id` or `title`. Optional: `completion-comment` |
| `delete-task` | Delete task | Identify by `task-id` or `title-pattern`. Cannot delete with non-closed children |

### Task Environment Setup

**`work-on`** - Prepares task execution environment (called automatically by execute prompts)
- Required: `task-id`
- Actions: Records execution state, manages branches/worktrees (if configured)
- Returns: Task info (`:task-id`, `:category`, `:type`, `:title`, `:status`), environment info (`:worktree-path`, `:worktree-name`, `:branch-name`, `:worktree-clean?`, `:worktree-created?`), state file path

## Available Activities

Each activity can be invoked via slash command or by programmatically accessing the MCP resource using `ReadMcpResourceTool`.

### Task Activities

**Execute task by criteria**
- Slash command: `/mcp-tasks:execute-task [selection-criteria...]`
- Arguments: `category=X`, `parent-id=N`, `type=X` (combinable)
- MCP resource: `prompt://execute-task`
- Implementation: Use slash command OR read resource and follow prompt instructions

**Execute next task for category**
- Slash command: `/mcp-tasks:next-<category>`
- Arguments: None
- MCP resource: `prompt://next-<category>`
- Implementation: Use slash command OR read resource and follow prompt instructions

**Refine task**
- Slash command: `/mcp-tasks:refine-task [task-spec] [context...]`
- Arguments: Task ID ("#59", "59", "task 59") or pattern ("Update prompt")
- MCP resource: `prompt://refine-task`
- Implementation: Use slash command OR read resource and follow prompt instructions

**Review task implementation**
- Slash command: `/mcp-tasks:review-task-implementation [task-spec]`
- Arguments: Task ID ("#59", "59", "task 59") or none (uses current execution state)
- MCP resource: `prompt://review-task-implementation`
- Implementation: Use slash command OR read resource and follow prompt instructions

### Story Activities

**Create story tasks**
- Slash command: `/mcp-tasks:create-story-tasks [story-spec] [context...]`
- Arguments: Story ID ("#59", "59", "story 59") or pattern ("Story title")
- MCP resource: `prompt://create-story-tasks`
- Implementation: Use slash command OR read resource and follow prompt instructions

**Execute story task**
- Slash command: `/mcp-tasks:execute-story-child [story-spec] [context...]`
- Arguments: Same as create-story-tasks
- MCP resource: `prompt://execute-story-child`
- Implementation: Use slash command OR read resource and follow prompt instructions

**Create story PR**
- Slash command: `/mcp-tasks:create-story-pr [story-spec]`
- Arguments: Same as create-story-tasks
- MCP resource: `prompt://create-story-pr`
- Implementation: Use slash command OR read resource and follow prompt instructions

**Review story implementation**
- Slash command: `/mcp-tasks:review-story-implementation [story-spec]`
- Arguments: Same as create-story-tasks
- MCP resource: `prompt://review-story-implementation`
- Implementation: Use slash command OR read resource and follow prompt instructions

**Complete story**
- Slash command: `/mcp-tasks:complete-story [story-spec]`
- Arguments: Same as create-story-tasks
- MCP resource: `prompt://complete-story`
- Implementation: Use slash command OR read resource and follow prompt instructions

### Story Creation Guidelines

**Story creation and task breakdown are separate workflow steps.**

When creating a story via `add-task`:
- Create ONLY the story record itself
- Do NOT automatically invoke `create-story-tasks`
- Wait for explicit user request to break down the story into tasks

This separation ensures the user can:
1. Review and refine the story before breakdown
2. Control when task breakdown occurs
3. Provide additional context or constraints before tasks are created

**Correct workflow:**
```
1. User requests story creation
2. Agent creates story with add-task (type: story)
3. Agent stops and informs user story is created
4. User reviews story, optionally requests refinement
5. User explicitly requests task breakdown
6. Agent invokes create-story-tasks
```

**Incorrect workflow (never do this):**
```
1. User requests story creation
2. Agent creates story with add-task
3. Agent immediately invokes create-story-tasks ← WRONG
```

### Story Shared Context

Stories maintain a **shared context** (`:shared-context` field) that
enables inter-task communication during story execution. This allows
child tasks to coordinate by reading context from previous tasks and
appending discoveries, decisions, and important information for
subsequent tasks.

**How It Works:**

1. **Reading Context**: Child tasks access parent story's shared context via `:parent-shared-context` field returned by `select-tasks`
2. **Writing Context**: Tasks append to parent story's shared context using `update-task` with the story's task ID
3. **Automatic Prefixing**: System reads current task ID from execution state (`.mcp-tasks-current.edn`) and automatically prefixes each entry with "Task NNN: "
4. **Persistence**: Context persists with story throughout execution and is archived when story completes

**Context Precedence Rule:**

Shared context takes precedence over a task's static `:description` and
`:design` fields when conflicts exist or new information emerges. This
ensures tasks work with the most current state.

**When to Update Shared Context:**

Update during execution when you:
- Make architectural or design decisions
- Discover important information (API endpoints, configuration, constraints)
- Find edge cases or issues
- Implement features that subsequent tasks depend on
- Choose between alternatives that affect later work

The system automatically prefixes your update with "Task NNN:" where NNN
is the current task ID. Multiple updates accumulate with newest first.

**Key Points:**

- **Append Only**: New entries are appended to existing context (not replaced)
- **Chronological Order**: Entries maintain order with task ID prefix showing sequence
- **Size Limit**: 50KB total serialized EDN (enforced by `update-task`)
- **Story Scope**: Context shared only among story and its children (not across stories)
- **Security**: Don't store sensitive data - context appears in task files and may appear in PRs

### Other Resources

**Category instructions:**
- `prompt://category-<category>` - Execution instructions for specific category (e.g., `prompt://category-simple`)

**Execution state:**
- `resource://current-execution` - Current execution state (`story-id`, `task-id`, `started-at`)

### Accessing MCP Resources Programmatically

```clojure
;; Example: Access execute-task prompt
(ReadMcpResourceTool
  :server "mcp-tasks"
  :uri "prompt://execute-task")
```

**Common workflow:** All execution activities follow: Find task → Call work-on → Execute category workflow → Mark complete

## Common Workflows

**Execute simple task:**
```
/mcp-tasks:next-simple
```

**Story workflow:**
```
/mcp-tasks:create-story-tasks 59       # Break into tasks
/mcp-tasks:execute-story-child 59       # Execute (repeat for each task)
/mcp-tasks:review-story-implementation 59
/mcp-tasks:complete-story 59
```

**Refine then execute:**
```
/mcp-tasks:refine-task 123
/mcp-tasks:execute-task task-id=123
```

## Complete Task Lifecycle Walkthrough

### Prerequisites
- mcp-tasks MCP server configured and running
- Project initialized with `.mcp-tasks/` directory
- Optional: `:worktree-management?` enabled in `.mcp-tasks.edn`
- Optional: `:base-branch` configured for branch management

This section covers two workflows: **Standalone Tasks** and **Story-Based Workflows**.

### Workflow A: Standalone Task

Example: Executing standalone task #123 "Add user authentication" (category: medium).

#### 1. Refine Task (Optional - Skip for Simple/Clear Tasks)

```bash
/mcp-tasks:refine-task 123
```

**What happens:**
- Agent analyzes task in project context
- Reviews design patterns and codebase
- Suggests improvements interactively
- Updates task with `update-task` tool
- Sets `meta: {"refined": "true"}`

**When to skip:** Simple tasks with clear requirements need no refinement.

#### 2. Execute Task

```bash
/mcp-tasks:execute-task task-id=123
```

**Behind the scenes - work-on tool (automatic):**

The execute prompt calls `work-on` which:
- Writes execution state to `.mcp-tasks-current.edn`
- Creates/switches to worktree (if `:worktree-management?` enabled)
- Creates/switches to branch `123-add-user-authentication` (if branch management configured)

See [work-on Tool Reference](#work-on-tool-reference) for complete return value specification.

**Agent displays working environment:**
```
Worktree: project-123-add-user-authentication
Directory: /Users/user/project-123-add-user-authentication
Branch: 123-add-user-authentication
```

**Category workflow execution (medium):**

1. **Analyze** - Agent reviews task spec, researches patterns
2. **Check understanding** - Agent confirms understanding with user
3. **Plan** - Agent creates implementation plan
4. **Implement** - Agent writes code
5. **Commit** - Agent creates git commit in main repository

#### 3. Complete Task

After successful implementation, the agent calls:

```clojure
(complete-task :task-id 123 :completion-comment "Implemented JWT auth")
```

**What happens:**
- Task status changed to `:closed`
- Task moved from `tasks.ednl` to `complete.ednl`
- Execution state cleared from `.mcp-tasks-current.edn`
- **Automatic worktree cleanup** (if `:worktree-management?` enabled) - see [Worktree Cleanup Mechanism](#worktree-cleanup-mechanism)

### Configuration Impact

| Feature | Enabled | Disabled |
|---------|---------|----------|
| **Worktree Management** | Creates sibling directory worktree, auto-cleanup on completion | Works in current directory |
| **Branch Management** | Creates `<id>-<title-slug>` branch automatically | Uses current branch |

See [Git Integration](#git-integration) for naming conventions and [Error Recovery](#error-recovery) for failure handling.

### Workflow B: Story-Based Workflow

Example: Story #408 "Improve mcp-tasks skill" with multiple child tasks.

#### 1. Refine Story (Optional but Recommended)

```bash
/mcp-tasks:refine-task 408
```

**What happens:**
- Agent analyzes story in project context
- Suggests improvements to requirements
- Updates story with `update-task` tool
- Sets `meta: {"refined": "true"}`

**Note:** The `create-story-tasks` prompt will halt and require explicit user confirmation to proceed if story is unrefined. Agents must never proceed automatically.

#### 2. Create Story Tasks

```bash
/mcp-tasks:create-story-tasks 408
```

**What happens:**
- Retrieves story using `select-tasks` (type: story)
- Checks refinement status, warns if not refined
- Displays story content to user
- Analyzes and breaks down into specific tasks
- Presents task breakdown for user approval
- Adds each task using `add-task` with:
  - `parent-id`: Story ID (408)
  - `category`: Appropriate category per task
  - `type`: Usually `:task`, `:feature`, or `:bug`

**Example tasks created:**
```
Task #410: Add walkthrough section (category: medium, parent-id: 408)
Task #411: Document git integration (category: medium, parent-id: 408)
Task #412: Add error recovery section (category: simple, parent-id: 408)
```

#### 3. Execute Story Tasks (Repeat for Each Task)

```bash
/mcp-tasks:execute-story-child 408
```

**What happens:**
- Finds story and first incomplete child task
- Shows progress: "2 of 5 tasks completed"
- Calls `work-on` tool with task ID
- **For first task only** (if worktree/branch management enabled):
  - Creates worktree: `project-408-improve-mcp-tasks-skill/`
  - Creates branch: `408-improve-mcp-tasks-skill`
  - All story tasks use same worktree/branch
- Executes task using its category workflow
- Creates git commit
- Marks task complete with `complete-task`
- **Preserves worktree** for remaining story tasks

**Repeat** until all story tasks complete.

#### 4. Create Pull Request (Optional)

```bash
/mcp-tasks:create-story-pr 408
```

**What happens:**
- Finds story using `select-tasks`
- Verifies current branch (must not be master/main)
- Collects commits from story branch
- Generates PR content:
  - Title: Story title (with optional semantic prefix)
  - Description: Story details + commit summary
- Creates PR targeting default branch
- Returns PR URL

**Prerequisites:**
- Must be on story branch
- Remote repository configured
- `gh` CLI or similar tool available

#### 5. Complete Story (After PR Merged)

```bash
/mcp-tasks:complete-story 408
```

**What happens:**
- Requires user confirmation before archiving. Never complete a story without explicit user approval.
- Moves story and all child tasks to archive
- Preserves implementation history

**Worktree cleanup:**
After PR is merged, manually remove worktree:
```bash
git worktree remove /path/to/project-408-improve-mcp-tasks-skill
```

Or if automatic cleanup enabled, it happens on last task completion.

## work-on Tool Reference

### Invocation Rules

| Context | Invocation | Who Calls |
|---------|------------|-----------|
| Execute prompts | Automatic | Execute prompt calls `work-on` before category workflow |
| Manual setup | Manual | User calls `work-on` directly via tool |
| Typical use | Automatic | Most users never call `work-on` directly |

**When to call manually:**
- Custom workflows outside standard execute prompts
- Debugging execution state issues
- Setting up environment without executing task

### When Agents Should Call work-on Directly

Agents must call the `work-on` tool explicitly when the user instructs them to work on a specific task or story:

**User instruction patterns requiring explicit work-on call:**
- "Work on task 123"
- "Start working on task 123"
- "Work on story 59"
- "Begin task 123"
- Similar direct instructions to start working on a specific task/story

**Process:**
1. Parse user instruction to identify task/story ID
2. Call `mcp__mcp-tasks__work-on` with the task ID
3. Display working environment context (worktree, branch if present)
4. Proceed with task execution according to the category workflow

**Contrast with execute prompts:**
- Execute prompts (e.g., `/mcp-tasks:execute-story-child`) call `work-on` automatically
- When user gives direct instruction to work on a task, agent must call `work-on` before proceeding

### Return Value Specification

`work-on` returns a map with task and environment information:

| Field | Type | Always Present | Description |
|-------|------|----------------|-------------|
| `:task-id` | int | Yes | Task ID being worked on |
| `:category` | string | Yes | Task category |
| `:type` | keyword | Yes | Task type (`:task`, `:bug`, `:feature`, `:story`, `:chore`) |
| `:title` | string | Yes | Task title |
| `:status` | keyword | Yes | Task status (`:open`, `:in-progress`, `:blocked`, `:closed`) |
| `:message` | string | Yes | Status message about operation |
| `:execution-state-file` | string | Yes | Path to `.mcp-tasks-current.edn` |
| `:worktree-path` | string | Conditional | Full path to worktree (only if in worktree) |
| `:worktree-name` | string | Conditional | Worktree directory name (only if `:worktree-path` present) |
| `:branch-name` | string | Conditional | Current branch name (only if branch management active) |
| `:worktree-clean?` | boolean | Conditional | No uncommitted changes (only if in worktree) |
| `:worktree-created?` | boolean | Conditional | New worktree created vs reused (only if in worktree) |

**Example response (with worktree management enabled):**
```clojure
{:task-id 123
 :category "medium"
 :type :task
 :title "Add user authentication"
 :status :open
 :message "Task validated successfully and execution state written"
 :worktree-path "/Users/user/project-123-add-user-authentication"
 :worktree-name "project-123-add-user-authentication"
 :branch-name "123-add-user-authentication"
 :worktree-clean? true
 :worktree-created? true
 :execution-state-file "/Users/user/project-123-add-user-authentication/.mcp-tasks-current.edn"}
```

**Example response (worktree management disabled):**
```clojure
{:task-id 123
 :category "medium"
 :type :task
 :title "Add user authentication"
 :status :open
 :message "Task validated successfully and execution state written"
 :execution-state-file ".mcp-tasks-current.edn"}
```

## Git Integration

### Branch Naming Convention

**Format:** `<id>-<title-slug>`

**Slugification process:**
1. Extract first N words from title (default: 4, configurable via `:branch-title-words`)
2. Convert to lowercase
3. Replace spaces with dashes
4. Remove all special characters (keep only a-z, 0-9, -)

**Examples:**

| Task ID | Title | `:branch-title-words` | Branch Name |
|---------|-------|----------------------|-------------|
| 123 | "Implement user authentication with OAuth" | 4 (default) | `123-implement-user-authentication-with` |
| 123 | "Implement user authentication with OAuth" | 2 | `123-implement-user` |
| 123 | "Implement user authentication with OAuth" | nil | `123-implement-user-authentication-with-oauth` |
| 59 | "Add JWT support" | 4 | `59-add-jwt-support` |
| 408 | "Improve mcp-tasks skill" | 4 | `408-improve-mcp-tasks-skill` |

### Worktree Naming Convention

**Format:** Depends on `:worktree-prefix` configuration

| `:worktree-prefix` | Format | Example |
|-------------------|--------|---------|
| `:project-name` | `<project>-<id>-<title-slug>` | `mcp-tasks-123-implement-user-authentication-with` |
| `:none` | `<id>-<title-slug>` | `123-implement-user-authentication-with` |

**Title slug:** Same process as branch naming (first N words, slugified)

**Location:** Sibling directory to main repository
```
/Users/user/project/                           # Main repo
/Users/user/project-123-add-auth/              # Worktree (with :project-name prefix)
/Users/user/123-add-auth/                      # Worktree (with :none prefix)
```

### Commit Timing and Location

**When commits occur:**
- During category workflow execution (varies by category)
- Simple: After implementation complete
- Medium: After implementation complete
- Large: After each significant milestone + final implementation

**Where commits occur:**
- Always in the **main repository** (`.git` directory location)
- Even when working in a worktree, commits are recorded in main repo
- Worktrees share the same commit history

**Who creates commits:**
- The agent executing the category workflow
- Follows category-specific commit instructions
- Uses git operations in current working directory

### Task/Branch/Worktree Relationships

```
Story Task #408 "Improve mcp-tasks skill"
  ├─ Branch: 408-improve-mcp-tasks-skill
  ├─ Worktree: /path/to/project-408-improve-mcp-tasks-skill/
  │
  ├─ Child Task #410 (category: medium)
  │   └─ Uses same branch + worktree as parent story
  │
  ├─ Child Task #411 (category: medium)
  │   └─ Uses same branch + worktree as parent story
  │
  └─ Child Task #412 (category: simple)
      └─ Uses same branch + worktree as parent story

Standalone Task #123 "Add authentication"
  ├─ Branch: 123-add-authentication
  └─ Worktree: /path/to/project-123-add-authentication/
```

**Rules:**
- Story tasks share parent story's branch and worktree
- Standalone tasks get unique branch and worktree
- One worktree per task/story (not per child task)
- All commits for story tasks go to story branch

### Worktree Cleanup Mechanism

**Automatic cleanup (when `:worktree-management?` enabled):**

Triggered by `complete-task` tool when:
- Task is completed successfully
- Current working directory is inside a worktree

**Safety checks before removal:**

| Check | Requirement | Failure Result |
|-------|-------------|----------------|
| Clean working directory | No uncommitted changes | Task marked complete, worktree preserved, warning shown |
| Pushed commits | All commits pushed to remote (if remote configured) | Task marked complete, worktree preserved, warning shown |

**Cleanup outcomes:**

| Scenario | Task Status | Worktree | Branch | Message |
|----------|-------------|----------|--------|---------|
| Success | `:closed` | Removed | Preserved | "Worktree removed at /path (switch directories to continue)" |
| Uncommitted changes | `:closed` | Preserved | Preserved | "Warning: Could not remove worktree: Uncommitted changes exist" |
| Unpushed commits | `:closed` | Preserved | Preserved | "Warning: Could not remove worktree: Unpushed commits exist" |
| Git error | `:closed` | Preserved | Preserved | "Warning: Could not remove worktree: <error message>" |

**Manual cleanup commands:**

```bash
# From main repository directory
git worktree remove /path/to/worktree

# Force removal (use with caution)
git worktree remove --force /path/to/worktree

# List all worktrees
git worktree list

# Remove worktree that was already deleted from filesystem
git worktree prune
```

**When to use manual cleanup:**
- Automatic cleanup failed due to safety checks
- Worktree directory deleted manually
- Need to clean up multiple worktrees at once
- Worktree in inconsistent state

## Error Recovery

### Task Execution Failures

**If task execution fails or is interrupted:**

1. **Execution state persists:** `.mcp-tasks-current.edn` remains with `:started-at` timestamp
2. **Task status unchanged:** Stays `:open` (not marked complete)
3. **Worktree/branch preserved:** Environment remains set up
4. **To resume:** Re-run the execute prompt
   - `work-on` overwrites stale execution state automatically
   - Execution continues from current code state

**Common failure scenarios:**

| Failure | Recovery Action |
|---------|----------------|
| Agent context limit exceeded | Break task into smaller subtasks, execute separately |
| Implementation error/bug | Fix manually, re-run execute prompt to continue |
| Network/tool failure | Re-run execute prompt (idempotent) |
| User interruption (Ctrl-C) | Re-run execute prompt |

### Handling Blocked Tasks

**When a task depends on another task:**

```clojure
;; Mark current task as blocked
(update-task
  :task-id 123
  :status :blocked
  :relations [{:relates-to 456, :as-type :blocked-by}])
```

**Relation types:**

| Type | Meaning | Example |
|------|---------|---------|
| `:blocked-by` | Cannot proceed until other task completes | Task #123 blocked by #456 |
| `:related` | Related but not blocking | Task #123 related to #456 |
| `:discovered-during` | Found while working on another task | Task #123 found during #456 |

**Unblocking workflow:**
1. Execute blocking task first (e.g., task #456)
2. Complete blocking task
3. Update blocked task to remove relation and set status to `:open`
4. Execute previously blocked task

### Delete vs Update vs Complete

**Decision matrix:**

| Scenario | Action | Tool | Reason |
|----------|--------|------|--------|
| Task done successfully | Complete | `complete-task` | Preserves audit trail in `complete.ednl` |
| Task no longer needed | Delete | `delete-task` | Removes from `tasks.ednl`, archives in `complete.ednl` with `:status :deleted` |
| Task needs clarification | Update | `update-task` | Modify `:description` or `:design` fields |
| Task scope changed | Update | `update-task` | Modify `:title`, `:description`, `:category` |
| Task blocked temporarily | Update | `update-task` | Set `:status :blocked`, add `:relations` |
| Task duplicates another | Delete | `delete-task` | Add `:relations` to other task first |
| Task split into subtasks | Create subtasks then delete parent | `add-task` + `delete-task` | Use `:parent-id` for subtasks |

**Constraints:**
- Cannot delete task with non-closed children (must complete or delete children first)
- Cannot complete task if blocked (must update to `:open` first)
- Deleted tasks are archived, not permanently removed

### Recovering from Interrupted Execution

**Stale execution state detection:**

External tools detect stale executions via `:started-at` timestamp in `.mcp-tasks-current.edn`:

```clojure
{:story-id 408
 :task-id 411
 :started-at "2025-10-29T10:30:00Z"}  ; If hours/days old = likely stale
```

**Recovery steps:**

1. **Check current execution state:**
   ```bash
   cat .mcp-tasks-current.edn
   ```

2. **Verify if execution actually stale:**
   - Check timestamp age
   - Check if agent still running
   - Check if work in progress

3. **Resume or restart:**
   - If continuing same task: Re-run execute prompt
   - If switching tasks: Run execute prompt for different task (overwrites state)
   - If abandoning task: Manually delete `.mcp-tasks-current.edn`

4. **Manual state cleanup (if needed):**
   ```bash
   rm .mcp-tasks-current.edn
   ```

**Note:** `work-on` automatically overwrites execution state, so manual cleanup rarely needed.

## Best Practices

- Refine complex/unclear tasks before execution
- Match task complexity to category
- Use `parent-id` when creating story tasks
- Monitor execution via `resource://current-execution`
- Never create story child tasks for unrefined stories without explicit user confirmation
- Always call work-on tool when user instructs you to work on a specific task or story
- Never complete stories without explicit user confirmation

## File Locations

- Tasks: `.mcp-tasks/tasks.ednl`
- Completed: `.mcp-tasks/complete.ednl`
- Execution state: `.mcp-tasks-current.edn`
- Category prompts: `.mcp-tasks/prompts/<category>.md` (optional overrides)
- Story prompts: `.mcp-tasks/story/prompts/<name>.md` (optional overrides)
