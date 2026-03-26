# Mutations

All mutations require authentication via `Personal-Token` header.

## Submit an Expense
```graphql
mutation CreateExpense($expense: ExpenseCreateInput!, $account: AccountReferenceInput!) {
  createExpense(expense: $expense, account: $account) {
    id status description amount { valueInCents currency }
  }
}
```
Variables:
```json
{
  "account": { "slug": "my-collective" },
  "expense": {
    "description": "Design work - January 2026",
    "type": "INVOICE",
    "payee": { "slug": "my-username" },
    "items": [
      { "description": "Logo design", "amount": 50000 }
    ],
    "currency": "USD",
    "payoutMethod": { "id": "payout-method-id" }
  }
}
```
Expense types: `INVOICE`, `RECEIPT`, `GRANT`, `SETTLEMENT`, `CHARGE`

## Edit an Expense
```graphql
mutation EditExpense($expense: ExpenseUpdateInput!) {
  editExpense(expense: $expense) {
    id status description amount { valueInCents currency }
  }
}
```
Variables:
```json
{
  "expense": {
    "id": "expense-id",
    "description": "Updated description",
    "items": [
      { "id": "item-id", "description": "Updated item", "amount": 60000 }
    ]
  }
}
```

## Process an Expense (Approve/Reject/Pay)
```graphql
mutation ProcessExpense($id: String!, $action: ExpenseProcessAction!) {
  processExpense(expense: {id: $id}, action: $action) {
    id status
  }
}
```
Actions: `APPROVE`, `UNAPPROVE`, `REJECT`, `MARK_AS_UNPAID`, `PAY`, `SCHEDULE_FOR_PAYMENT`

## Comment on an Expense
```graphql
mutation CommentOnExpense($comment: CommentCreateInput!) {
  createComment(comment: $comment) {
    id html createdAt
  }
}
```
Variables:
```json
{
  "comment": {
    "expense": { "id": "expense-id" },
    "html": "<p>Looks good, approved!</p>"
  }
}
```

## Create a Collective
```graphql
mutation CreateCollective($collective: CollectiveCreateInput!, $host: AccountReferenceInput) {
  createCollective(collective: $collective, host: $host) {
    id name slug
  }
}
```
Variables:
```json
{
  "collective": {
    "name": "My Project",
    "slug": "my-project",
    "description": "An open-source project",
    "tags": ["open-source", "javascript"]
  },
  "host": { "slug": "opensource" }
}
```

## Create an Organization
```graphql
mutation CreateOrg($org: OrganizationCreateInput!) {
  createOrganization(organization: $org) {
    id name slug
  }
}
```

## Invite a Member
```graphql
mutation InviteMember($account: AccountReferenceInput!, $memberAccount: AccountReferenceInput!, $role: MemberRole!) {
  inviteMember(account: $account, memberAccount: $memberAccount, role: $role) {
    id role
  }
}
```
Roles: `ADMIN`, `MEMBER`, `ACCOUNTANT`

## Follow / Unfollow
```graphql
mutation { followAccount(account: {slug: "webpack"}) { member { id } } }
mutation { unfollowAccount(account: {slug: "webpack"}) { member { id } } }
```

## Create an Update (Blog Post)
```graphql
mutation CreateUpdate($update: UpdateCreateInput!) {
  createUpdate(update: $update) {
    id title slug
  }
}
```
Variables:
```json
{
  "update": {
    "account": { "slug": "my-collective" },
    "title": "Monthly Report - January 2026",
    "html": "<p>Here's what we accomplished...</p>"
  }
}
```

Then publish: `publishUpdate(id: "update-id") { id publishedAt }`

## Create a Webhook
```graphql
mutation CreateWebhook($webhook: WebhookCreateInput!) {
  createWebhook(webhook: $webhook) {
    id webhookUrl activityType
  }
}
```
Variables:
```json
{
  "webhook": {
    "account": { "slug": "my-collective" },
    "webhookUrl": "https://example.com/webhook",
    "activityType": "ACTIVITY_ALL"
  }
}
```

## Apply to a Fiscal Host
```graphql
mutation ApplyToHost($collective: AccountReferenceInput!, $host: AccountReferenceInput!, $message: String) {
  applyToHost(collective: $collective, host: $host, message: $message) {
    id name
  }
}
```

## Create an Order (Contribution/Donation)
```graphql
mutation CreateOrder($order: OrderCreateInput!) {
  createOrder(order: $order) {
    order { id status totalAmount { valueInCents currency } }
  }
}
```
Variables:
```json
{
  "order": {
    "fromAccount": { "slug": "my-username" },
    "toAccount": { "slug": "webpack" },
    "amount": { "valueInCents": 1000, "currency": "USD" },
    "frequency": "MONTHLY",
    "tier": { "slug": "backer" }
  }
}
```
Note: Payment provider integration (Stripe/PayPal) is not available via external API. Use for pending orders or platform-internal flows.

## Cancel a Recurring Contribution
```graphql
mutation CancelOrder($order: OrderReferenceInput!, $reason: String) {
  cancelOrder(order: $order, reason: $reason) {
    id status
  }
}
```

## Manage Tiers
```graphql
# Create
mutation CreateTier($tier: TierCreateInput!, $account: AccountReferenceInput!) {
  createTier(tier: $tier, account: $account) {
    id name slug
  }
}

# Edit
mutation EditTier($tier: TierUpdateInput!) {
  editTier(tier: $tier) {
    id name amount { valueInCents currency }
  }
}
```
