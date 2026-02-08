---
name: google-workspace
description: Google Workspace MCP integration for Gmail, Drive, Calendar, Docs, Sheets, Slides, Forms, Tasks, and Chat. Use when the user wants to read/send emails, manage files, create/edit documents, schedule events, or interact with any Google Workspace service.
model: inherit
tools: ["Read", "Grep", "Glob", "Execute"]
---

# Google Workspace Skill

Comprehensive MCP integration for all Google Workspace services.

## Denotation

> **Google Workspace tasks map to functional invariants, resulting in consistent email, file, calendar, and task states under Narya condensation and GF(3) conservation.**

The skill reaches a **fixed point** when all pending operations complete with no H¹ obstructions (gluing failures), and thread/folder trit sums are conserved modulo 3.

## Formal Contract

```
Effect: Google Workspace → State × Trit
Invariant: ∀ closed workflow: Σ(trit) ≡ 0 (mod 3)
Denotation: ⟦GW⟧ = lim_{n→∞} Condense(Op_n(...Op_1(S_0)))
```

## Required Parameter

**All tools require `user_google_email`** - the user's Google email address.

## Services Overview

### 📧 Gmail (MINUS -1: Validator)

| Tool | Description |
|------|-------------|
| `search_gmail_messages` | Search with Gmail query syntax |
| `get_gmail_message_content` | Get full message content |
| `get_gmail_messages_content_batch` | Batch get (max 25) |
| `get_gmail_thread_content` | Get full conversation thread |
| `send_gmail_message` | Send email (supports replies) |
| `draft_gmail_message` | Create draft (supports replies) |
| `modify_gmail_message_labels` | Add/remove labels (archive, delete) |
| `batch_modify_gmail_message_labels` | Bulk label operations |
| `list_gmail_labels` | List all labels with IDs |
| `manage_gmail_label` | Create/update/delete labels |

**Query syntax examples:**
- `from:user@example.com` - From specific sender
- `is:unread` - Unread messages
- `has:attachment` - Has attachments
- `after:2024/01/01` - Date filters

### 📁 Drive (ERGODIC 0: Coordinator)

| Tool | Description |
|------|-------------|
| `search_drive_files` | Search files by query |
| `list_drive_items` | List folder contents |
| `get_drive_file_content` | Get file content (text extraction) |
| `get_drive_file_download_url` | Get download URL |
| `create_drive_file` | Create new file |
| `update_drive_file` | Update metadata |
| `