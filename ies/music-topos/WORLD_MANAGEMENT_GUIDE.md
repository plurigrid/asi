# World Management & Agent Skills Integration Guide

**Date**: 2025-12-21
**Status**: Justfile enhanced with GitHub CLI + DuckDB integration
**Location**: `/Users/bob/ies/music-topos/justfile`

---

## What Was Added

Your justfile now includes **four major new features**:

### 1. **GitHub CLI GraphQL Interactions**
Query and manage music-topos related repositories programmatically

### 2. **DuckDB World Versioning**
Track world versions, execution history, and metadata in a queryable database

### 3. **Agent Skills Registry**
Auto-register and manage agent skills from agentskills.io

### 4. **World Execution Logging**
Record execution time, status, and output files for each world run

---

## Quick Start

### Initialize Everything

```bash
# Set up the world database
just world-db-init

# Register agent skills
just skills-register

# List all registered worlds
just world-list

# List all available skills
just skills-list
```

### Query GitHub Repositories

```bash
# Find all music-topos and worlds-tagged repos
just world-repos-query

# Clone/sync all repos to /Users/bob/ies/worlds/
just world-repos-sync
```

### Manage World Versions

```bash
# Register a new world
just world-register my-new-world

# Bump version (patch, minor, or major)
just world-version-bump my-world patch
just world-version-bump my-world minor
just world-version-bump my-world major

# View execution history
just world-history my-world
just world-history "*" 20  # Last 20 runs across all worlds
```

### Execute Worlds with Logging

```bash
# Run a world and log results to DuckDB
just world-execute my-world

# The system logs:
#   - Execution timestamp
#   - Duration in seconds
#   - Status (success/error)
#   - Output file location
```

---

## Database Schema

### `worlds` table
```
id (INTEGER, PK)
name (VARCHAR, UNIQUE)
path (VARCHAR)
version (VARCHAR) - Semver format: 1.0.0
created_at (TIMESTAMP)
last_modified (TIMESTAMP)
description (VARCHAR)
tags (VARCHAR[])
author (VARCHAR)
```

### `world_dependencies` table
```
dependent_world_id (FK)
dependency_world_id (FK)
dependency_type (VARCHAR) - 'import', 'extends', 'requires'
```

### `world_execution` table
```
id (INTEGER, PK)
world_id (FK)
executed_at (TIMESTAMP)
duration_seconds (REAL)
status (VARCHAR) - 'success' or 'error'
output_file (VARCHAR)
```

### `agent_skills` table
```
id (INTEGER, PK)
skill_name (VARCHAR, UNIQUE)
description (VARCHAR)
source_url (VARCHAR)
version (VARCHAR)
compatibility (VARCHAR[]) - ['Amp', 'Claude Code', 'Copilot', ...]
requires (VARCHAR[]) - Dependencies on other skills
created_at (TIMESTAMP)
last_used (TIMESTAMP)
```

---

## Registered Agent Skills

### 7 Skills Auto-Registered

1. **epistemic-arbitrage**
   - Parallel mathematician broadcast with propagators
   - Platforms: Amp, Claude Code, Copilot

2. **glass-bead-game**
   - Interdisciplinary synthesis connecting domains
   - Platforms: Amp, Claude Code, Aider

3. **world-hopping**
   - Badiou triangle inequality for possible worlds
   - Platforms: Amp, Claude Code

4. **parallel-execution**
   - SPI-compliant deterministic parallel computation
   - Platforms: Claude Code
   - Requires: gay-rs

5. **mcp-server-creation**
   - Tool composition for agent capabilities
   - Platforms: Claude Code, Cursor

6. **repl-integration**
   - Live coding with feedback loops (Sonic Pi, SuperCollider)
   - Platforms: Claude Code, Geiser

7. **skill-composition**
   - Meta-skill for combining existing skills
   - Platforms: Amp, Claude Code, Copilot
   - Requires: epistemic-arbitrage, glass-bead-game, world-hopping

---

## GitHub GraphQL Queries

### Query Structure

The system uses GitHub GraphQL to search for repositories with topics:
- `topic:music-topos` - Primary project repos
- `topic:worlds` - World-related projects

```graphql
query {
    search(query: "topic:music-topos topic:worlds", type: REPOSITORY, first: 50) {
        repositoryCount
        edges {
            node {
                ... on Repository {
                    name
                    nameWithOwner
                    url
                    description
                    pushedAt
                    primaryLanguage { name }
                }
            }
        }
    }
}
```

### Example Output

```
ToposInstitute/CatColab: Formal collaborative modeling via category theory (2025-12-21T18:42:28Z)
borkdude/cherry-mac-app-test: Cherry ClojureScript compiler (2025-12-20T14:30:15Z)
...
```

---

## How It Integrates With Your System

### Knowledge Graph Integration

```
Knowledge Indexer (DuckDB)
    ↓ Topics, Resources, Experts
    ↓
Music Topos (.worlds.duckdb)
    ├─ worlds table (your curated world collection)
    ├─ world_execution (logs when each world runs)
    └─ agent_skills (tools available to extend system)
```

### Version Increment Workflow

```
Version 1.0.0
    ↓ (just world-version-bump myworld patch)
Version 1.0.1  ← Patch: bug fix
    ↓ (just world-version-bump myworld minor)
Version 1.1.0  ← Minor: backward-compatible feature
    ↓ (just world-version-bump myworld major)
Version 2.0.0  ← Major: breaking change
```

### Execution Logging

```
User runs: just world-execute initial
    ↓
System executes world (~/worlds/initial/run.rb or pattern-on-matter)
    ↓
Measures duration, records status
    ↓
Inserts into world_execution:
    world_id: 1001
    executed_at: 2025-12-21 19:45:33
    duration_seconds: 12.5
    status: 'success'
    output_file: '/tmp/initial.wav'
    ↓
User can query: just world-history initial 10
```

---

## Advanced Usage

### Query Execution History (Raw SQL)

```bash
# Connect to the database directly
duckdb /Users/bob/ies/music-topos/.worlds.duckdb

# List slowest worlds
SELECT w.name, COUNT(*) as runs, AVG(e.duration_seconds) as avg_duration
FROM world_execution e
JOIN worlds w ON e.world_id = w.id
GROUP BY w.id, w.name
ORDER BY avg_duration DESC;

# Find failed executions
SELECT w.name, e.executed_at, e.status
FROM world_execution e
JOIN worlds w ON e.world_id = w.id
WHERE e.status != 'success'
ORDER BY e.executed_at DESC;
```

### Custom Skill Registration

You can add your own skills to the database:

```bash
duckdb /Users/bob/ies/music-topos/.worlds.duckdb

INSERT INTO agent_skills (skill_name, description, compatibility, requires)
VALUES (
    'my-custom-skill',
    'Description of what it does',
    ARRAY['Claude Code', 'Cursor'],
    ARRAY['dependency1', 'dependency2']
);
```

### Sync and Register All GitHub Repos

```bash
# One-shot command to sync all repos and register them
for repo_dir in /Users/bob/ies/worlds/*/; do
    world_name=$(basename "$repo_dir")
    just world-register "$world_name"
done

# Verify
just world-list
```

---

## Integration With Existing "just world" Target

The new `world-append-duckdb` target is designed to be called from your main `world` target:

```bash
# Current "just world" does:
# 1. Check deps
# 2. Setup SuperCollider
# 3. Boot SuperCollider
# 4. Build
# 5. Check audio
# 6. Run InitialObjectWorld
# 7. Run TerminalObjectWorld

# You can add at the end:
#     just world-append-duckdb  ← Initializes databases and logs execution
```

---

## Workflow Examples

### Example 1: Track a New World Type

```bash
# Create new world directory
mkdir -p /Users/bob/ies/worlds/my-procedural-world
echo "#!/bin/bash\necho 'Running my world...'" > /Users/bob/ies/worlds/my-procedural-world/run.sh

# Register it
just world-register my-procedural-world

# Increment version as you develop
just world-version-bump my-procedural-world patch

# Run and log
just world-execute my-procedural-world

# Check history
just world-history my-procedural-world
```

### Example 2: Discover Available Skills

```bash
# List all skills
just skills-list

# Find skills compatible with Claude Code
duckdb /Users/bob/ies/music-topos/.worlds.duckdb << 'EOF'
SELECT skill_name, description
FROM agent_skills
WHERE array_contains(compatibility, 'Claude Code')
ORDER BY skill_name;
EOF
```

### Example 3: Sync External Worlds

```bash
# Find all public music-topos repos on GitHub
just world-repos-query

# Clone/update them all
just world-repos-sync

# Register each one
for repo in /Users/bob/ies/worlds/*/; do
    just world-register "$(basename "$repo")"
done

# Now you have a full world index
just world-list
```

---

## Commands Reference

| Command | Purpose |
|---------|---------|
| `just world-repos-query` | Find music-topos repos on GitHub |
| `just world-repos-sync` | Clone/pull all repos to local |
| `just world-db-init` | Initialize DuckDB schema |
| `just world-register NAME` | Add a world to the database |
| `just world-list` | Show all registered worlds |
| `just world-version-bump NAME TYPE` | Increment version (patch/minor/major) |
| `just world-history NAME` | Show execution history |
| `just skills-register` | Register agent skills |
| `just skills-list` | Show available skills |
| `just world-execute NAME` | Run a world and log results |
| `just world-append-duckdb` | Initialize everything (call from `just world`) |

---

## Next Steps

1. **Initialize**: `just world-db-init`
2. **Sync repos**: `just world-repos-sync`
3. **Register worlds**: `just world-register <each-world>`
4. **Verify**: `just world-list` and `just skills-list`
5. **Execute**: `just world-execute initial` (will log to DuckDB)
6. **Query**: `just world-history initial`

---

## Integration Notes

### Why DuckDB?

- **Embedded**: No separate server (single `.worlds.duckdb` file)
- **SQL**: Full SQL queries on world metadata
- **Fast**: OLAP-optimized for analytics
- **Deterministic**: Same schema = same results across machines
- **Syncs with knowledge graph**: Can join against main music-topos knowledge base

### Why GitHub GraphQL?

- **Precise**: Query by topic, language, last-modified date
- **Automated**: Discover new music-topos repos automatically
- **Bidirectional**: Sync fork relationships, collaborators
- **Auditable**: Logged API calls show what changed and when

### Why Agent Skills?

- **Composable**: Skills depend on other skills
- **Reusable**: Same skill works across multiple agents
- **Discoverable**: Query by platform compatibility
- **Versioned**: Track which version of a skill you're using

---

## Error Handling

### No DuckDB

```bash
just world-list
# → "No world database found. Run: just world-db-init"

just world-db-init  # Fixes it
```

### World Not Found

```bash
just world-execute nonexistent
# → "✗ World not found: nonexistent"

just world-register myworld  # Register it first
```

### GitHub Not Authenticated

```bash
just world-repos-query
# → Authentication error

gh auth login  # Login to GitHub CLI first
```

---

**Status**: Ready to use
**Test it**: `just world-db-init && just world-list`

