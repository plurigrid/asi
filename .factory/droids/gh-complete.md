---
name: gh-complete
description: 'gh-complete'
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# gh-complete

Comprehensive GitHub CLI skill with GraphQL, REST API, and workflow automation.

## Quick Reference

### Authentication
```bash
gh auth login                    # Interactive login
gh auth login --with-token < token.txt
gh auth status                   # Check auth state
gh auth token                    # Print current token
gh auth refresh -s repo,read:org # Refresh with scopes
```

### Repository Operations
```bash
gh repo clone owner/repo
gh repo create name --public --source=. --push
gh repo fork owner/repo --clone
gh repo view [repo] --web
gh repo list owner --limit 100
gh repo archive owner/repo
gh repo delete owner/repo --yes
gh repo rename new-name
gh repo sync                     # Sync fork with upstream
```

### Pull Requests
```bash
gh pr create --title "T" --body "B" --base main
gh pr create --fill              # From commit messages
gh pr create --draft
gh pr list --state open --author @me
gh pr view 123 --comments
gh pr checkout 123
gh pr diff 123
gh pr merge 123 --squash --delete-branch
gh pr ready 123                  # Mark ready for review
gh pr review 123 --approve
gh pr review 123 --request-changes --body "Fix X"
gh pr close 123
gh pr reopen 123
gh pr edit 123 --add-label bug --add-reviewer user
```

### Issues
```bash
gh issue create --title "T" --body "B"
gh issue create --label bug,urgent --assignee @me
gh issue list --state open --label bug
gh issue view 42 --comments
gh issue close 42 --reason completed
gh issue reopen 42
gh issue edit 42 --add-label priority
gh issue transfer 42 owner/other-repo
gh issue pin 42
gh issue develop 42 --checkout   # Create branch for issue
```

### Actions & Workflows
```bash
gh run list                      # List workflow runs
gh run view 12345                # View run details
gh run view 12345 --log          # View logs
gh run watch 12345               # Watch live
gh run rerun 12345               # Rerun failed
gh run cancel 12345
gh workflow list
gh workflow view deploy.yml
gh workflow run