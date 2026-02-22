---
name: opencollective
description: Query and interact with Open Collective's GraphQL API v2. Browse collectives, view budgets/transactions/expenses, manage memberships, submit expenses, and explore the open-source funding ecosystem.
version: 1.0.0
license: MIT
trit: 0
role: ERGODIC
color: "#7FADF2"
hue: 216
tags: [opencollective, graphql, fundraising, open-source, fiscal-host]
metadata:
  triggers: [opencollective, collective, fiscal host, open source funding, expense, backer, sponsor]
  related-skills: [graphql-architect, github-api]
---

# Open Collective

Query and manage Open Collective accounts, finances, and community data via their public GraphQL API v2.

## Endpoint & Auth

- **Endpoint**: `https://api.opencollective.com/graphql/v2`
- **Unauthenticated**: 10 req/min, public read-only
- **Authenticated**: 100 req/min — pass `Personal-Token: <token>` header
- **Token creation**: `https://opencollective.com/<your-slug>/admin/for-developers`
- **Not available via API**: Stripe/PayPal payment creation, captcha-protected operations

## MCP Server Setup

Use `mcp-graphql` to expose the OC API as MCP tools. With fnox-backed auth:

```bash
claude mcp add opencollective-graphql -- /bin/sh -c \
  'unset PYTHONPATH && \
   ENDPOINT=https://api.opencollective.com/graphql/v2 \
   HEADERS="{\"Personal-Token\":\"$(fnox get OPENCOLLECTIVE_TOKEN --age-key-file ~/.age/key.txt -c ~/v/instance-onboarding/fnox.toml)\"}" \
   exec npx mcp-graphql'
```

Store your token: `fnox set OPENCOLLECTIVE_TOKEN <token> --age-key-file ~/.age/key.txt -c ~/v/instance-onboarding/fnox.toml`

## Quick Start

If `opencollective-graphql` MCP server is available, use its `query-graphql` tool. Otherwise use `curl`.

```graphql
query { account(slug: "webpack") { name stats { balance { valueInCents currency } } } }
```

## Core Queries

| Query | Use When |
|-------|----------|
| `account(slug)` | Look up any account by slug |
| `accounts(searchTerm, type, limit)` | Search/browse collectives |
| `host(slug)` | Look up a fiscal host |
| `hosts(limit)` | Browse fiscal hosts |
| `expenses(account, status, limit)` | View submitted expenses |
| `expense(id)` | Single expense detail |
| `transactions(account, type, limit)` | View financial activity |
| `orders(account, status, limit)` | View contributions/donations |
| `search(searchTerm)` | General search (beta) |
| `me` | Current authenticated user |
| `tier(id)` | Sponsorship tier details |
| `tagStats(searchTerm)` | Explore ecosystem categories |

## Core Mutations (all require auth)

| Mutation | Use When |
|----------|----------|
| `createExpense` | Submit expense for reimbursement |
| `editExpense` | Update existing expense |
| `processExpense(action)` | Approve/reject/pay expense |
| `createOrder` | Create contribution/donation |
| `cancelOrder` | Cancel recurring contribution |
| `createComment` | Comment on expense/update |
| `createUpdate` / `publishUpdate` | Post update to collective |
| `inviteMember` | Invite someone to join |
| `followAccount` / `unfollowAccount` | Follow/unfollow collective |
| `createWebhook` | Set up notifications |
| `applyToHost` | Apply collective to fiscal host |
| `createCollective` | Create new collective |
| `createTier` / `editTier` | Manage sponsorship tiers |

## Reference Guide

| Topic | File | Load When |
|-------|------|-----------|
| Query Templates | `references/queries.md` | Need ready-to-use GraphQL queries |
| Mutation Templates | `references/mutations.md` | Need to write/modify data |
| Schema Types | `references/types.md` | Need type details for building queries |
| Weird Mutualism | `references/weird-mutualism.md` | Exploring OC's mutualist ecosystem patterns |

## Key Patterns

- **Pagination**: All collections use `limit`/`offset`, return `totalCount` + `nodes`
- **Account refs**: `{slug: "x"}`, `{id: "uuid"}`, or `{legacyId: 123}`
- **Amounts**: Always `{ valueInCents: Int, currency: String }` — divide by 100 for display
- See `references/queries.md` for full filtering examples

## Account Types

`COLLECTIVE`, `ORGANIZATION`, `INDIVIDUAL`, `FUND`, `EVENT`, `PROJECT`, `HOST`, `VENDOR`

## Status Enums

- **Expense**: `DRAFT` → `UNVERIFIED` → `PENDING` → `APPROVED` → `PROCESSING` → `PAID` (also `REJECTED`, `ERROR`, `CANCELED`)
- **Order**: `NEW`, `PENDING`, `ACTIVE`, `CANCELLED`, `REJECTED`, `PAID`, `ERROR`, `EXPIRED`
- **Transaction type**: `CREDIT` (in) / `DEBIT` (out)
- **Transaction kind**: `CONTRIBUTION`, `EXPENSE`, `ADDED_FUNDS`, `HOST_FEE`, `PAYMENT_PROCESSOR_FEE`, `PLATFORM_FEE`

## Tips

- `stats` subfields on accounts give quick financial summaries
- `members(role: [BACKER])` lists financial contributors
- `tiers` shows sponsorship levels; `updates` shows blog posts
- `socialLinks` has website, twitter, github URLs
