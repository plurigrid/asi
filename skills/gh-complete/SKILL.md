---
name: gh-complete
description: 'gh-complete'
version: 1.0.0
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
gh workflow run deploy.yml -f env=prod
gh workflow enable deploy.yml
gh workflow disable deploy.yml
```

### REST API
```bash
gh api repos/{owner}/{repo}
gh api repos/{owner}/{repo}/issues --method POST \
  -f title="Bug" -f body="Description"
gh api /user --jq '.login'
gh api orgs/{org}/repos --paginate
gh api graphql -f query='{ viewer { login } }'
```

### GraphQL API
```bash
# Get viewer info
gh api graphql -f query='
  query {
    viewer {
      login
      repositories(first: 10) {
        nodes { name stargazerCount }
      }
    }
  }'

# Mutation example
gh api graphql -f query='
  mutation($id: ID!) {
    addStar(input: {starrableId: $id}) {
      starrable { stargazerCount }
    }
  }' -f id="MDEwOlJlcG9zaXRvcnkx"

# With variables file
gh api graphql -F query=@query.graphql -F variables=@vars.json
```

### Gists
```bash
gh gist create file.txt --public
gh gist create file1.txt file2.txt --desc "My gist"
gh gist list --public
gh gist view abc123
gh gist edit abc123
gh gist delete abc123
gh gist clone abc123
```

### Releases
```bash
gh release create v1.0.0 --generate-notes
gh release create v1.0.0 ./dist/* --title "Release v1.0.0"
gh release list
gh release view v1.0.0
gh release download v1.0.0
gh release delete v1.0.0 --yes
gh release edit v1.0.0 --draft=false
```

### SSH Keys & GPG
```bash
gh ssh-key list
gh ssh-key add ~/.ssh/id_ed25519.pub --title "My Key"
gh ssh-key delete 12345
gh gpg-key list
gh gpg-key add key.gpg
```

### Extensions
```bash
gh extension list
gh extension install owner/gh-ext
gh extension upgrade --all
gh extension remove gh-ext
gh extension create my-ext       # Scaffold new extension
gh extension browse              # Discover extensions
```

### Search
```bash
gh search repos "query" --language=rust --stars=">1000"
gh search issues "bug" --state=open --repo=owner/repo
gh search prs "fix" --merged --author=user
gh search code "function" --repo=owner/repo
gh search commits "fix bug" --author=user
```

### Codespaces
```bash
gh codespace list
gh codespace create -r owner/repo
gh codespace ssh -c codespace-name
gh codespace code -c codespace-name  # Open in VS Code
gh codespace stop -c codespace-name
gh codespace delete -c codespace-name
```

### Projects (v2)
```bash
gh project list --owner @me
gh project view 1 --owner @me
gh project create --title "My Project"
gh project item-list 1 --owner @me
gh project item-add 1 --owner @me --url https://github.com/owner/repo/issues/1
```

### Labels & Milestones
```bash
gh label list
gh label create "priority:high" --color FF0000
gh label delete "old-label"
# Milestones via API
gh api repos/{owner}/{repo}/milestones --method POST -f title="v2.0"
```

### Aliases
```bash
gh alias set pv 'pr view'
gh alias set co 'pr checkout'
gh alias list
gh alias delete pv
```

### Config
```bash
gh config set editor vim
gh config set git_protocol ssh
gh config get editor
gh config list
```

### Environment Variables
```bash
GH_TOKEN=xxx gh api /user        # Override auth
GH_HOST=github.example.com       # GitHub Enterprise
GH_REPO=owner/repo               # Default repo
GH_DEBUG=1                       # Debug output
NO_COLOR=1                       # Disable colors
```

## Patterns

### Bulk Operations
```bash
# Close all issues with label
gh issue list --label stale --json number -q '.[].number' | \
  xargs -I {} gh issue close {}

# Add label to all open PRs
gh pr list --json number -q '.[].number' | \
  xargs -I {} gh pr edit {} --add-label needs-review
```

### JSON Processing
```bash
# Get PR authors
gh pr list --json author --jq '.[].author.login' | sort -u

# Format output
gh repo list --json name,stargazerCount \
  --template '{{range .}}{{.name}}: {{.stargazerCount}}{{"\n"}}{{end}}'
```

### CI Integration
```bash
# Wait for checks
gh pr checks 123 --watch

# Get check status
gh pr view 123 --json statusCheckRollup -q '.statusCheckRollup[].state'
```

## GF(3) Assignment

```
Trit: 0 (ERGODIC) - Coordinator
Hue: 210° (GitHub blue)
```

Triads:
- `gh-complete (0)` × `git (-1)` × `github-actions (+1)` = 0 ✓
- `gh-complete (0)` × `code-review (-1)` × `pr-automation (+1)` = 0 ✓
