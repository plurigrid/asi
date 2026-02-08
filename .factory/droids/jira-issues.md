---
name: jira-issues
description: Create, update, and manage Jira issues from natural language. Use when the user wants to log bugs, create tickets, update issue status, or manage their Jira backlog.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Jira Issue Management

Create and manage Jira issues using the Jira REST API or MCP.

## Setup

### Option 1: Jira MCP Server
Install the Jira MCP server for seamless integration:
```bash
npx @anthropic/create-mcp-server jira
```

### Option 2: Direct API
Set environment variables:
```bash
export JIRA_BASE_URL="https://yourcompany.atlassian.net"
export JIRA_EMAIL="your-email@company.com"
export JIRA_API_TOKEN="your-api-token"
```

Get your API token: https://id.atlassian.com/manage-profile/security/api-tokens

## Creating Issues

### Basic Issue
```python
import requests
from requests.auth import HTTPBasicAuth
import os

def create_issue(project_key, summary, description, issue_type="Task"):
    url = f"{os.environ['JIRA_BASE_URL']}/rest/api/3/issue"

    auth = HTTPBasicAuth(
        os.environ['JIRA_EMAIL'],
        os.environ['JIRA_API_TOKEN']
    )

    payload = {
        "fields": {
            "project": {"key": project_key},
            "summary": summary,
            "description": {
                "type": "doc",
                "version": 1,
                "content": [{
                    "type": "paragraph",
                    "content": [{"type": "text", "text": description}]
                }]
            },
            "issuetype": {"name": issue_type}
        }
    }

    response = requests.post(url, json=payload, auth=auth)
    return response.json()

# Example
issue = create_issue("PROJ", "Fix login bug", "Users can't login with SSO", "Bug")
print(f"Created: {issue['key']}")
```

### With Labels and Priority
```python
def create_detailed_issue(project_key, summary, description,
                          issue_type="Task", priority="Medium",
                          labels=None, assignee=None):
    payload = {
        "fields": {
            "project": {"key": project_key},
            "summary": summary,
            "description": {
                "type": "doc",
                "version": 1,
                "content": [{
                   