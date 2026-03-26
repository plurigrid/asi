---
name: skill-repo-sync
description: Push local skills to plurigrid/asi repo, remove skills by agreement (with full history purge), and manage .gitignore for local-only skills. Triggers: push skills, sync asi, remove skill from repo, skill repo sync, purge skill.
---

# Skill Repo Sync

Manages the flow between local skill directories and the upstream `plurigrid/asi` repo.

## Directories

- **Upstream**: `/Users/alice/v/asi/skills/`
- **Local sources**: `~/.claude/skills/`, `~/v/.agents/skills/`, `~/.codex/skills/`, `~/.config/goose/skills/`, `~/.copilot/skills/`, `~/.openhands/skills/`
- **Standalone**: `~/repos/skills/skill-codex/`, `~/ies/mcp/topos/`, `~/v/gay-terminal-colors/`

## Operations

### Find what needs pushing

Use `skill-finder-verifier` first:
```bash
python3 ~/.claude/skills/skill-finder-verifier/scripts/finder.py scan
```
Skills classified as `local-only` are candidates for pushing.

### Push local skills to asi

```bash
cd /Users/alice/v/asi
# Copy from source
cp -r <source>/skill-name skills/skill-name
# Stage, commit, push
git add skills/skill-name
git -c commit.gpgsign=false commit -m "feat: add skill-name"
git push origin main
```

### Remove a skill by agreement (full purge)

When a skill must be removed with no trace:

```bash
cd /Users/alice/v/asi
# 1. Purge from all history
/Users/alice/Library/Python/3.9/bin/git-filter-repo --path skills/SKILL-NAME/ --invert-paths --force

# 2. Re-add remote (filter-repo removes it)
git remote add origin https://github.com/plurigrid/asi.git

# 3. Pop any stashed changes
git stash pop  # resolve conflicts if needed

# 4. Add to .gitignore to prevent re-addition
echo "skills/SKILL-NAME/" >> .gitignore
# Add comment: "# Local-only skills (kept on disk, excluded from repo by agreement)"

# 5. Commit and force push
git -c commit.gpgsign=false commit -am "chore: remove SKILL-NAME by agreement"
git push --force origin main
```

### Keep a skill local-only (no purge needed)

Just add to `.gitignore`:
```bash
echo "skills/skill-name/" >> /Users/alice/v/asi/.gitignore
```

## Quality Gate (skill-creator rules)

When pushing skills, review and fix them inline — never report issues without fixing them. skill-creator criteria take priority:

- SKILL.md with YAML frontmatter (`name`, `description` with trigger words). No extra fields.
- Under 500 lines. Only context Claude doesn't already have.
- No human-oriented content: no README, prerequisites, pip install, "Learn More", difficulty ratings, estimated times.
- No textbook definitions or standard algorithms Claude already knows.
- No GF(3) trit assignment sections, SDF interleaving, or philosophical decoration.
- Ground all APIs to actual file paths and commands. No aspirational/unimplemented interfaces.
- File must be named `SKILL.md`, not `instructions.md` or anything else.

## GPG Note

GPG signing is not available on this machine. Use `git -c commit.gpgsign=false commit` for commits.

## Companion Skills

- **skill-finder-verifier**: Identifies local-only and modified skills
- **claude-questions-leaderboard**: Track question quality (uses same DuckDB pattern)
